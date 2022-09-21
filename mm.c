/*
 * Franciszek Pindel 323506 the only author of following source code (excluding
 * fragments from mm-implicit.c).
 * Technique: segregated sort, searching in list with first-fit segregated list
 * setup: blocks for allocating 8, 16, 24, ..., 64, 80 - 96, 112- 160, 176 - inf
 * bytes. There are no optimized boundary tags,  as they decreased nops without
 * increasing util.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* definitions taken from mm-implicit.c */

typedef int32_t word_t;

typedef enum {
  FREE = 0, /* Block is free */
  USED = 1, /* Block is used */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */

/*
 * each free block list has two guards: for start and for end
 * in this particular setup there are 2 * (8 + 3) guards
 */

static word_t *guard_blocks_start;
static word_t *guard_blocks_end;

/* Free lists are divided into two categories:
 * const lists - they contain blocks of one specific size
 * segment lists - they contain block of size in some range
 * (range is increasing by the power of 2)
 */

static word_t *segment_lists_start;

#define MIN_FREE_NODE_SIZE 16

#define CONST_LISTS_NUM 8
#define SEGMENT_LISTS_NUM 3
#define FREE_LISTS_NUM (CONST_LISTS_NUM + SEGMENT_LISTS_NUM)

/* --=[ boundary tag handling ]=-------------------------------------------- */
/* procedures taken from mm-implicit.c */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~USED;
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  word_t bt_val = size | flags;
  bt[0] = bt_val;
  *bt_footer(bt) = bt_val;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  return (bt == last) ? NULL : bt_size(bt) + (void *)bt;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  return (bt == heap_start) ? NULL : (void *)bt - bt_size(bt - 1);
}

/* --=[ free block list handling ]=----------------------------------------- */

/*
 * creates guards as first and last blocks in free block list.
 * First guard must be of size 0 to not be used doring choosing
 * free block. Second is marked used to not be coalesed
 */
static inline void create_guard_pair(word_t *ptr) {
  bt_make(ptr, MIN_FREE_NODE_SIZE, USED);
  ptr[1] = -1;
  ptr[2] = (void *)ptr - (void *)heap_start + MIN_FREE_NODE_SIZE;

  ptr[0] = ptr[3] = 0;

  bt_make((void *)ptr + MIN_FREE_NODE_SIZE, MIN_FREE_NODE_SIZE, USED);
  ptr[5] = (void *)ptr - (void *)heap_start;
  ptr[6] = -1;
}

/* return wheather specified block is first guard block */
static inline int is_head(word_t *ptr) {
  return ptr[0] == 0;
}

/* return wheather specified block is second guard block (last in the free block
 * list) */
static inline int is_tail(word_t *ptr) {
  return ptr[0] == 17 && ptr <= guard_blocks_end;
}

/*
 * every block in free list contain links to prev and next
 * free block in a list. It is implemented by storing offset
 * from start of the heap. As the heap is smaller than 4 Gib,
 * it can be stored as 32-bit val
 * below are standard getters/setters for such offset.
 */
static inline size_t get_prev_offset(word_t *ptr) {
  return ptr[1];
}

static inline size_t get_next_offset(word_t *ptr) {
  return ptr[2];
}

static inline void set_prev_offset(word_t *ptr, word_t offset) {
  ptr[1] = offset;
}

static inline void set_next_offset(word_t *ptr, word_t offset) {
  ptr[2] = offset;
}

/*
 * when block is freed, it may be possible,
 * that there are free blocks before, or after freed block
 * in such case coalescing must be performed.
 * Following procefures merge block after or before
 */
static inline void coalese_front(word_t *bt) {
  word_t *next_block = bt_next(bt);
  last = (next_block == last) ? bt : last;
  bt_make(bt, bt_size(bt) + bt_size(next_block), FREE);
}

static inline void coalese_back(word_t *bt) {
  word_t *prev_block = bt_prev(bt);
  last = (bt == last) ? prev_block : last;
  bt_make(prev_block, bt_size(bt) + bt_size(prev_block), FREE);
}

/* --=[ free block queues management ]=------------------------------------- */

/*
 * returns pointer to free block list that may contain
 * the smallest free blocks, but large enough to contain block
 * of size blk_size
 */
static word_t *get_list(size_t blk_size) {
  /* blk_size is in const list */
  if (blk_size <= CONST_LISTS_NUM * ALIGNMENT) {
    return (void *)guard_blocks_start +
           ((blk_size / MIN_FREE_NODE_SIZE) - 1) * 2 * MIN_FREE_NODE_SIZE;
    /* blk_size is in free list */
  } else {
    int two_to_pow_i = 2;
    word_t low = CONST_LISTS_NUM * ALIGNMENT + ALIGNMENT;

    for (int i = 0; i < SEGMENT_LISTS_NUM - 1; i++) {

      if (blk_size >= low && blk_size <= low + (two_to_pow_i - 1) * ALIGNMENT) {
        return (void *)segment_lists_start + (2 * i * MIN_FREE_NODE_SIZE);
      }

      low = low + two_to_pow_i * ALIGNMENT;
      two_to_pow_i *= 2;
    }

    return (void *)segment_lists_start +
           (2 * (SEGMENT_LISTS_NUM - 1) * MIN_FREE_NODE_SIZE);
  }

  return NULL;
}

/* go to previous free block in a list (or return NULL if it is first) */
static inline word_t *prev_free(word_t *ptr) {
  return (is_head(ptr)) ? NULL : (void *)heap_start + get_prev_offset(ptr);
}

/* go to next free block in a list (or return NULL if it is last) */
static inline word_t *next_free(word_t *ptr) {
  return (is_tail(ptr)) ? NULL : (void *)heap_start + get_next_offset(ptr);
}

/* insert blok to suitable list */
static void insert_block(word_t *blk_ptr) {
  word_t *element_before_inserted = get_list(bt_size(blk_ptr));

  word_t prev_offset = (void *)element_before_inserted - (void *)heap_start;
  word_t next_offset = get_next_offset(element_before_inserted);

  word_t new_block_offset = (void *)blk_ptr - (void *)heap_start;

  set_prev_offset(next_free(element_before_inserted), new_block_offset);
  set_next_offset(element_before_inserted, new_block_offset);

  set_prev_offset(blk_ptr, prev_offset);
  set_next_offset(blk_ptr, next_offset);
}

static void remove_block(word_t *ptr) {
  word_t *blk_prev = prev_free(ptr);
  word_t *blk_next = next_free(ptr);

  set_next_offset(blk_prev, get_next_offset(ptr));
  set_prev_offset(blk_next, get_prev_offset(ptr));
}

/* return first block in list 'list' that is large enough to store block of size
 * 'size' */
static word_t *find_block_in_list(word_t *list, size_t size) {
  word_t *act = list;
  while (!is_tail(act)) {
    if (bt_size(act) >= size)
      return act;
    act = next_free(act);
  }

  return NULL;
}

/* start searching in first list with block large enough, then search in
 * following lists until finding free block. Return NULL if there is no free
 * block. */
static word_t *find_free_block(size_t size) {
  word_t *list_to_check = get_list(size);
  word_t *res = NULL;
  while (list_to_check <= guard_blocks_end &&
         !(res = find_block_in_list(list_to_check, size))) {
    list_to_check = (void *)list_to_check + 2 * MIN_FREE_NODE_SIZE;
  }

  return res;
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* from mm-implicit.c */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (2 * sizeof(word_t) + size + ALIGNMENT - 1) & -ALIGNMENT;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  if (!morecore(ALIGNMENT - sizeof(word_t)))
    return -1;

  /* allocate space for all guards */
  guard_blocks_start = mem_sbrk(2 * MIN_FREE_NODE_SIZE * FREE_LISTS_NUM);
  if (!guard_blocks_start)
    return -1;

  guard_blocks_end = (void *)guard_blocks_start +
                     2 * MIN_FREE_NODE_SIZE * FREE_LISTS_NUM -
                     MIN_FREE_NODE_SIZE;

  /* heap starts where guards starts */
  heap_start = guard_blocks_start;

  for (int i = 0; i < FREE_LISTS_NUM; i++)
    create_guard_pair((void *)guard_blocks_start + 2 * MIN_FREE_NODE_SIZE * i);

  last = guard_blocks_end;
  heap_end = (void *)last + MIN_FREE_NODE_SIZE;

  /* after CONST_LISTS_NUM * 2 guard block lies segment listst guards */
  segment_lists_start =
    (void *)guard_blocks_start + (2 * MIN_FREE_NODE_SIZE * CONST_LISTS_NUM);

  return 0;
}

/*
 * malloc - Try to find free block: if succeed, use it with possible split
 * if not, get more mmry from brk.
 */
void *malloc(size_t size) {
  /* round up to mul of 16 */
  size = blksz(size);

  /* try to find free block */
  word_t *blk_ptr = find_free_block(size);

  /* no free block - get more space by brk */
  if (!blk_ptr) {
    blk_ptr = morecore(size);
    if (!blk_ptr)
      return NULL;
    last = blk_ptr;
    heap_end = (void *)last + size;

    /* there is free block */
  } else {
    remove_block(blk_ptr);

    /* block is large enough to do split */
    if (size < bt_size(blk_ptr)) {
      word_t *splited_free_block = (void *)blk_ptr + size;
      size_t splited_block_size = bt_size(blk_ptr) - size;
      bt_make(splited_free_block, splited_block_size, FREE);
      if (blk_ptr == last)
        last = splited_free_block;
      insert_block(splited_free_block);
    }
  }

  bt_make(blk_ptr, size, USED);
  return bt_payload(blk_ptr);
}

/*
 * free - mark block as free, if possible - do coalessing
 *        insert back to the list.
 */
void free(void *ptr) {
  if (!ptr)
    return;

  word_t *blk_ptr = bt_fromptr(ptr);
  word_t size = bt_size(blk_ptr);
  bt_make(blk_ptr, size, FREE);
  word_t *blk_prev = bt_prev(blk_ptr);
  word_t *blk_next = bt_next(blk_ptr);
  int prev_used = (blk_prev) ? bt_used(blk_prev) : 1;
  int next_used = (blk_next) ? bt_used(blk_next) : 1;
  if (prev_used && next_used)
    insert_block(blk_ptr);
  else if (!prev_used && next_used) {
    remove_block(blk_prev);
    coalese_back(blk_ptr);
    insert_block(blk_prev);
  } else if (prev_used && !next_used) {
    remove_block(blk_next);
    coalese_front(blk_ptr);
    insert_block(blk_ptr);
  } else {
    remove_block(blk_next);
    coalese_back(blk_ptr);
    coalese_front(blk_prev);
  }
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 * main structure of the following code is taken from original mm.c
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  word_t *blk_ptr = bt_fromptr(old_ptr);
  size_t old_size = bt_size(blk_ptr);
  size_t new_block_size = blksz(size);

  /* if size is smaller - just ignore request */
  if (old_size >= new_block_size)
    return old_ptr;

  /* block is last - just increase brk */
  if (!bt_next(blk_ptr)) {
    size_t extend_size = new_block_size - old_size;
    if (!morecore(extend_size))
      return NULL;
    bt_make(blk_ptr, new_block_size, USED);
    heap_end = (void *)heap_end + extend_size;
    return old_ptr;
  } else {
    void *new_ptr = malloc(size);

    /* If malloc() fails, the original block is left untouched. */
    if (!new_ptr)
      return NULL;

    /* Copy the old data. */
    memcpy(new_ptr, old_ptr, old_size - 2 * sizeof(word_t));

    /* Free the old block. */
    free(old_ptr);

    return new_ptr;
  }
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * mm_checkheap - very looong and ugly, but it helped many times
 */

/* check if free block is on proper list */
static int is_on_free_list(word_t *blk_ptr) {
  word_t *act = get_list(bt_size(blk_ptr));
  while (!is_tail(act)) {
    if (act == blk_ptr)
      return 1;
    act = next_free(act);
  }

  return 0;
}

/* prints data about specified block */
static inline void print_heap_state(word_t *blk_ptr) {
  msg("[ %lx: %d, %c ]\n", (long)blk_ptr, bt_size(blk_ptr),
      (bt_used(blk_ptr)) ? 'u' : 'f');
}

/* checkheap checks following invariants:
 * (1) all blocks must be inside heap
 * (2) no adjent free blocks
 * (3) every free block must be on proper free block list
 * (4) next block must be after actual block
 * (5) last block must point to heap end
 * (6) every block in free block list must be marked free
 * (7) and must be of proper size
 */
void mm_checkheap(int verbose) {

  /* guard checkup */
  for (int i = 0; i < FREE_LISTS_NUM; i++) {
    word_t *act_guard_blk =
      (void *)guard_blocks_start + 2 * MIN_FREE_NODE_SIZE * i;
    assert(act_guard_blk[0] == 0);
    assert(act_guard_blk[0] == act_guard_blk[3]);
    assert(act_guard_blk[4] == 17);
    assert(act_guard_blk[4] == act_guard_blk[7]);
  }

  msg("\nHEAP STATE:\n");
  print_heap_state(heap_start);
  word_t *act = guard_blocks_end;
  int last_used = 1;
  int free_blocks_number = 0;
  while (act != heap_end) {
    print_heap_state(act);
    assert(act < heap_end); /* (1) */
    if (!last_used)         /* (2) */
      assert(bt_used(act));
    if (!bt_used(act)) {
      free_blocks_number++;
      assert(is_on_free_list(act)); /* (3) */
    }
    last_used = bt_used(act);
    word_t *next_blk = (void *)act + bt_size(act);
    assert(next_blk > act); /* (4) */
    act = next_blk;
  }

  msg("last: %lx   heap_end: %lx\n", (long)last, (long)heap_end);

  assert(act == heap_end); /* (5) */

  for (int i = 16; i <= CONST_LISTS_NUM * 16; i += 16) {
    act = get_list(i);
    act = next_free(act);
    while (act[0] != 17 || act > guard_blocks_end) {
      free_blocks_number--;
      assert(bt_free(act));      /* (6) */
      assert(bt_size(act) == i); /* (7) */
      act = next_free(act);
    }
  }

  int two_to_pow_i = 2;
  word_t low = CONST_LISTS_NUM * ALIGNMENT + ALIGNMENT;

  for (int i = 0; i < SEGMENT_LISTS_NUM - 1; i++) {
    act = get_list(low);
    act = next_free(act);
    while (act[0] != 17 || act > guard_blocks_end) {
      free_blocks_number--;
      assert(bt_free(act)); /* (6) */
      assert(bt_size(act) >= low &&
             bt_size(act) <= low + (two_to_pow_i - 1) * ALIGNMENT); /* (7) */
      act = next_free(act);
    }

    low = low + two_to_pow_i * ALIGNMENT;
    two_to_pow_i *= 2;
  }

  act = get_list(low);
  act = next_free(act);
  while (act[0] != 17 || act > guard_blocks_end) {
    free_blocks_number--;
    assert(bt_free(act));        /* (6) */
    assert(bt_size(act) >= low); /* (7) */
    act = next_free(act);
  }

  assert(free_blocks_number == 0);
}
