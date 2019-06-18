/ * mm-naive.c - The fastest, least memory-efficient malloc package.
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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

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
/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */

static char *rover;           /* Next fit rover */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkheap(int verbose);
static void checkblock(void *bp);


/*
 * mm_init - Initialize the memory manager
 */

int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT_NOTAG(heap_listp, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
     heap_listp += (2*WSIZE);


    rover = heap_listp;


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
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
    char *bp;

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {


        place(bp, asize);

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

/*
 * mm_free - Free a block
 */

void mm_free(void *bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    if (heap_listp == 0){
        mm_init();
    }


    CLEAR_TAG(HDRP(NEXT_BLKP(bp)));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}


/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;

    if (prev_alloc && next_alloc) {
        return bp;
        /* Case 1 */
    }
    else if (prev_alloc && !next_alloc) {
        /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
    /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;
    return bp;

}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
  void *new_ptr = ptr;
  size_t asize = size;
  int unallocated;
  int extendsize;
  int block_buffer;

  if (size == 0)
    return NULL;

  if (asize <= DSIZE) {
    asize = 2 * DSIZE;
  } else {
    asize = DSIZE * ((asize + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  asize += BUFFER;

  block_buffer = GET_SIZE(HDRP(ptr)) - asize;

  if (block_buffer < 0) {
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
      unallocated = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - asize;
      if (unallocated < 0) {
        extendsize = MAX(-unallocated, CHUNKSIZE);
        if (extend_heap(extendsize) == NULL)
          return NULL;
        unallocated += extendsize;
      }


      PUT_NOTAG(HDRP(ptr), PACK(asize + unallocated, 1));
      PUT_NOTAG(FTRP(ptr), PACK(asize + unallocated, 1));
    } else {
      new_ptr = mm_malloc(asize - DSIZE);
      memmove(new_ptr, ptr, MIN(size, asize));
      mm_free(ptr);
    }
    block_buffer = GET_SIZE(HDRP(new_ptr)) - asize;
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
    char  *bp;
    size_t asize;
    /* Allocate an even number of words to maintain alignment */
    asize = ALIGN(size);

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;                                        //line:vm:mm:endextend


    PUT_NOTAG(HDRP(bp), PACK(asize, 0));
    PUT_NOTAG(FTRP(bp), PACK(asize, 0));
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

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

      if (unallocated >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(unallocated, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(unallocated, 0));
      }
      else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
      }
    return;
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */

static void *find_fit(size_t asize)
{
    char *oldrover = rover;


    /* Search from the rover to the end of list */
    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if ((!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) && !(GET_TAG(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if ((!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) && !(GET_TAG(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */

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
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
void checkheap(int verbose)
{
    char *bp = heap_listp;
    // print value of
    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

