/* mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
*/

/*
 * 32-bit and 64-bit allocator incorporating implicit free lists,
 * first-fit placement (we removed the option to switch between fit methods for a performance boost),
 * and boundary tag coalescing. Blocks are aligned
 * to 8 byte boundaries. Minimum block size is 16 bytes.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"


team_t team = {
    /* Team name */
    "KeithnGrace",
    /* First member's full name */
    "Keith Emert",
    /* First member's email address */
    "keithemert2019@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Grace Richardson",
    /* Second member's email address (leave blank if none) */
    "Gracerichardson2021@u.northwestern.edu"
};



/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size_t)(size) +7) & ~(0x7))

#define BUFFER (1<<7) /* Reallocation buffer */
#define MINSIZE   16      /* Minimum block size */

#define LISTS     20      /* Number of segregated lists */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) > (y)? (y) : (x))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
//line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
//line:vm:mm:get

// Put and keep reallocation bit
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
//line:vm:mm:put

// Put and clear reallocation bit
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

/* Store predecessor or successor pointer for free blocks */
#define SET_PTR(p, bp) (*(unsigned int *)(p) = (unsigned int)(bp))




/* Adjust the reallocation tag */
#define SET_TAG(p)   (*(unsigned int *)(p) = GET(p) | 0x2)
#define CLEAR_TAG(p) (*(unsigned int *)(p) = GET(p) & ~0x2)

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
//line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)
//line:vm:mm:get:alloc
#define GET_TAG(p)   (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

/* Address of free block's predecessor and successor on the segregated list */
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_PTR(bp)))




/* $end mallocmacros */

/* Global variables */
  /* Pointer to first block */
void *free_lists[LISTS];
char *prologue_block;
static char *rover;           /* Next fit rover */
static char *heap_listp = 0;
/* Function prototypes for internal helper routines */
static void *extend_heap(size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkheap(int verbose);
static void checkblock(void *bp);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);


/*
 * mm_init - Initialize the memory manager
 */

int mm_init(void)
{
   int i = 0;
   char *heap_listp;
   for (i = 0; i < LISTS; i++) {
     free_lists[i] = NULL;
    }
    /* Create the initial empty heap */
   if ((long)(heap_listp = mem_sbrk(4*WSIZE)) == -1) //line:vm:mm:begininit
        return -1;
    PUT_NOTAG(heap_listp, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */

     prologue_block = heap_listp + DSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp = NULL;
    int list = 0;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    size = asize;
    /* Select a free block of sufficient size from segregated list */
    while (list < LISTS) {
      if ((list == LISTS - 1) || ((size <= 1) && (free_lists[list] != NULL))) {
	bp = free_lists[list];
	// Ignore blocks that are too small or marked with the reallocation bit
	while ((bp != NULL)
	       && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
	  {
	    bp = PRED(bp);
	  }
	if (bp != NULL)
	  break;
      }

      size >>= 1;
      list++;
    }

    /* No fit found. Get more memory and place the block */
    if (bp == NULL){
      extendsize = MAX(asize,CHUNKSIZE);
      if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block
 */

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    CLEAR_TAG(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_node(bp, size);
    coalesce(bp);
    return;
}


/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));



    if (prev_alloc && next_alloc) {
        return bp;
        /* Case 1 */
    }


    if (GET_TAG(HDRP(PREV_BLKP(bp)))){
      prev_alloc = 1;
    }
    delete_node(bp);
    if (prev_alloc && !next_alloc) {
        /* Case 2 */
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        /* Case 3 */
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
    /* Case 4 */
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp,size);
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    return bp;

}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
  void *new_ptr = ptr;
  size_t nsize = size;
  int unallocated;
  int extendsize;
  int block_buffer;

  if (ptr == NULL){
    extendsize = MAX(nsize,CHUNKSIZE);
    if ((ptr = extend_heap(extendsize)) == NULL)
      return NULL;
  }

  if (size == 0)
    return NULL;

  if (nsize <= DSIZE) {
    nsize = 2 * DSIZE;
  } else {
    nsize = DSIZE * ((nsize + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  nsize += BUFFER;

  block_buffer = GET_SIZE(HDRP(ptr)) - nsize;

  if (block_buffer < 0) {
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
      unallocated = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - nsize;
      if (unallocated < 0) {
        extendsize = MAX(-unallocated, CHUNKSIZE);
        if (extend_heap(extendsize) == NULL)
          return NULL;
        unallocated += extendsize;
      }

      delete_node(NEXT_BLKP(ptr));

      PUT_NOTAG(HDRP(ptr), PACK(nsize + unallocated, 1));
      PUT_NOTAG(FTRP(ptr), PACK(nsize + unallocated, 1));
    } else {
      new_ptr = mm_malloc(nsize - DSIZE);
      memmove(new_ptr, ptr, MIN(size, nsize));
      mm_free(ptr);
    }
    block_buffer = GET_SIZE(HDRP(new_ptr)) - nsize;
  }

  if (block_buffer < 2 * BUFFER)
    SET_TAG(HDRP(NEXT_BLKP(new_ptr)));

return new_ptr;
}

/*
 * mm_checkheap - Check the heap for correctness
 */
void mm_checkheap(int verbose)
{
    checkheap(verbose);
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t size)
{
    void  *bp;
    size_t words = size / WSIZE;
    size_t asize;
    /* Allocate an even number of words to maintain alignment */

    asize = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(asize)) == -1)
        return NULL;                                        //line:vm:mm:endextend


    PUT_NOTAG(HDRP(bp), PACK(asize, 0));
    PUT_NOTAG(FTRP(bp), PACK(asize, 0));
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    insert_node(bp,asize);
    return coalesce(bp);
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
      size_t csize = GET_SIZE(HDRP(bp));
      size_t unallocated = csize - asize;
      delete_node(bp);

      if (unallocated >= MINSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(unallocated, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(unallocated, 0));
	insert_node(NEXT_BLKP(bp),unallocated);
      }
      else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
      }
    return;
}

static void insert_node(void *ptr, size_t size) {
  int list = 0;
  void *search_ptr = ptr;
  void *insert_ptr = NULL;

  /* Select segregated list */
  while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }
  search_ptr = free_lists[list];
  while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
    insert_ptr = search_ptr;
    search_ptr = PRED(search_ptr);
  }

  /* Set predecessor and successor */
  if (search_ptr != NULL) {
    if (insert_ptr != NULL) {
      SET_PTR(PRED_PTR(ptr), search_ptr);
      SET_PTR(SUCC_PTR(search_ptr), ptr);
      SET_PTR(SUCC_PTR(ptr), insert_ptr);
      SET_PTR(PRED_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRED_PTR(ptr), search_ptr);
      SET_PTR(SUCC_PTR(search_ptr), ptr);
      SET_PTR(SUCC_PTR(ptr), NULL);

      /* Add block to appropriate list */
      free_lists[list] = ptr;
    }
  } else {
    if (insert_ptr != NULL) {
      SET_PTR(PRED_PTR(ptr), NULL);
      SET_PTR(SUCC_PTR(ptr), insert_ptr);
      SET_PTR(PRED_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRED_PTR(ptr), NULL);
      SET_PTR(SUCC_PTR(ptr), NULL);

      /* Add block to appropriate list */
      free_lists[list] = ptr;
    }
  }

  return;
}

/*
 * delete_node: Remove a free block pointer from a segregated list. If
 *              necessary, adjust pointers in predecessor and successor blocks
 *              or reset the list head.
 */
static void delete_node(void *ptr) {
  int list = 0;
  size_t size = GET_SIZE(HDRP(ptr));

  /* Select segregated list */
  while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }

  if (PRED(ptr) != NULL) {
    if (SUCC(ptr) != NULL) {
      SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
      SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
    } else {
      SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
      free_lists[list] = PRED(ptr);
    }
  } else {
    if (SUCC(ptr) != NULL) {
      SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
    } else {
      free_lists[list] = NULL;
    }
  }

  return;
}


/*
 * find_fit - Find a fit for a block with asize bytes
 */

static void *find_fit(size_t asize)
{
    char *oldrover = rover;
    void *ptr = NULL;
    int i;
    size_t size = asize;
    for (i = 0; i<LISTS; i++){
      if ((i == LISTS - 1) || ((size<=1) && (free_lists[i] != NULL))){
	ptr = free_lists[i];
	while ((ptr!= NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr))))){
	  ptr = PRED(ptr);

	}
	if (ptr!= NULL){
	  break;
	}
      size >>= 1;
    }
    }
    return ptr;
}
/* $end mmfirstfit */

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    int l = 0 ;
    int count_size;
    char *scan_ptr;
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    if (GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))){
      printf("Error: header size does not match footer size");
    }
    if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))){
      printf("Error: header alloc  does not match footer size");
    }
    if (!GET_ALLOC(HDRP(bp))){
      count_size= GET_SIZE(HDRP(bp));
      while ((l<19) && (count_size >1)){
	count_size >>= 1;
	l++;
      }
      scan_ptr = free_lists[l];
      while ((scan_ptr != NULL) && (scan_ptr != bp)) {
        scan_ptr = PRED(scan_ptr);
      }
      if (scan_ptr == NULL) {
        printf("%d: There is a free block not in the list index\n");
      }

    }

}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose)
{
  char *bp;
    // print value of
    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
        printf("Bad prologue header\n");
        checkblock(heap_listp);
    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
	     printblock(bp);
	     checkblock(bp);
    }

    if (verbose)
      printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    while (verbose) {




    }










}
