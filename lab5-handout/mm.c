/*
 * CS 208 Lab 5: Malloc Lab
 *
 * Viktor Chekhovoi, 2003419
 Lita Theng,
 *
 * An allocator based on explicit free lists, first fit search,
 * and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63                  4  3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  0  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is 1
 * if and only if the block is allocated.
 * if the block is free, it has the following form:
 * ------------------------------------------
 * hdr(s:f)| next_free pointer| prev_free pointer| ftr(s:f)
 *
 * next_free points to the next block in explicit free list, prev_free points to previous block in explicit free list;
 * the next block in EFL is not necessarily next in memory.

 * The list has the following form:
 *
 * begin                                                             end
 * heap                                                             heap
 *  -----------------------------------------------------------------
 * |  pad   | hdr(16:a) | ftr(16:a) | zero or more usr blks | hdr(0:a) |
 *  -----------------------------------------------------------------
 *          |       prologue        |                       | epilogue |
 *          |         block         |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/* Basic constants and macros */
#define WSIZE       8       /* word size (bytes) */
#define DSIZE       16      /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16      /* overhead of header and footer (bytes) */
#define PREV_PTR
#define NEXT_PTR

/* NOTE: feel free to replace these macros with helper functions and/or
 * add new ones that will be useful for you. Just make sure you think
 * carefully about why these work the way they do
 */

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Perform unscaled pointer arithmetic */
#define PADD(p, val) ((char *)(p) + (val))
#define PSUB(p, val) ((char *)(p) - (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0xf)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       (PSUB(bp, WSIZE))
#define FTRP(bp)       (PADD(bp, GET_SIZE(HDRP(bp)) - DSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  (PADD(bp, GET_SIZE(HDRP(bp))))
#define PREV_BLKP(bp)  (PSUB(bp, GET_SIZE((PSUB(bp, DSIZE)))))

/* Next free block ptr and prev free block ptr*/
#define GET_NEXT_FREE(bp) ((void *)GET((bp)))
#define GET_PREV_FREE(bp) ((void *)(GET(PADD(bp, WSIZE))))

/* Setting next free block and previous free block of bp*/
#define SET_NEXT_FREE(bp, val) (PUT(bp, (size_t)val))
#define SET_PREV_FREE(bp, val) (PUT(PADD(bp, WSIZE), (size_t)val))

/* Global variables */

// Pointer to first block
static void *heap_start = NULL;

//Pointer to the first "free" block in EFL
static void *head_free = NULL;

/* Function prototypes for internal helper routines */

static bool check_heap(int lineno);
static void print_heap();
static void print_block(void *bp);
static bool check_block(int lineno, void *bp);
static void *extend_heap(size_t size);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void print_efl();
static void place(void *bp, size_t asize);
static size_t max(size_t x, size_t y);


 /* mm_init - initalizes the heap;
  * takes no arguments, return 0 if heap was initialized successfully, returns -1 otherwise;
  */
int mm_init(void) {
    /* create the initial empty heap */
    if ((heap_start = mem_sbrk(4 * WSIZE)) == NULL)
        return -1;

    head_free = NULL;

    PUT(heap_start, 0);                        /* alignment padding */
    PUT(PADD(heap_start, WSIZE), PACK(OVERHEAD, 1));  /* prologue header */
    PUT(PADD(heap_start, DSIZE), PACK(OVERHEAD, 1));  /* prologue footer */
    PUT(PADD(heap_start, WSIZE + DSIZE), PACK(0, 1));   /* epilogue header */

    heap_start = PADD(heap_start, DSIZE); /* start the heap at the (size 0) payload of the prologue block */
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc -- allocates memory in heap
 * takes the number of bytes the user wants to alocate as an argument
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    } else {
        /* Add overhead and then round up to nearest multiple of double-word alignment */
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = max(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}


/*
 * add_efl - adds a block the the explicit free list;
 * takes a block pointer bp as an argument;
 * bp must be unallocated;
*/
static void add_efl(void *bp){

    if (head_free == NULL){
        head_free = bp;
        SET_NEXT_FREE(head_free, NULL);
        SET_PREV_FREE(head_free, NULL);
    }
    else{
        SET_NEXT_FREE(bp, head_free); //insert from the head
        SET_PREV_FREE(head_free, bp);
        SET_PREV_FREE(bp, NULL);
        head_free = bp;  // update head_free to show new head as the bp
    }
}

/*
 * remove_efl - removes a block from EFL;
 * takes a block pointer bp as an argument
 * bp must be in EFL
*/
static void remove_efl(void*bp){
    if (bp == head_free){
        head_free = GET_NEXT_FREE(bp);
        if (head_free != NULL){ //if there were other elements in EFL
            SET_PREV_FREE(head_free, NULL);
        }
    }

    else if (GET_NEXT_FREE(bp) == NULL){ //if bp is at the tail of EFL
        SET_NEXT_FREE(GET_PREV_FREE(bp), NULL);
    }

    else{ //if bp is in the middle of EFL
        SET_PREV_FREE(GET_NEXT_FREE(bp), GET_PREV_FREE(bp));
        SET_NEXT_FREE(GET_PREV_FREE(bp), GET_NEXT_FREE(bp));
    }
}

/*
 * mm_free -- unallocates the pointer;
 * takes a block pointer bp as an argument;
 * bp must be allocated and in EFL;
 */
void mm_free(void *bp) {

	PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
	PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), 0));
	coalesce(bp);

}

/* The remaining routines are internal helper routines */


/*
 * place -- Place block of asize bytes at start of free block bp
 *          and split the block if it is bigger than asize.
 *          If a block was split, add the unallocated part to EFL.
 * bp must be free and in EFL;
 */
static void place(void *bp, size_t asize) {

	remove_efl(bp);
    size_t block_size = GET_SIZE(HDRP(bp));

	if (block_size >= asize+OVERHEAD+DSIZE){
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		PUT(HDRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(block_size - asize, 0));
    add_efl(NEXT_BLKP(bp));
		return;
	}

	PUT(HDRP(bp), PACK(block_size, 1));
	PUT(FTRP(bp), PACK(block_size, 1));

	return;

}

/*
 * coalesce -- Boundary tag coalescing.
 * Takes a pointer to a free block
 * Return ptr to coalesced block
 * bp has to be free
 */
static void *coalesce(void *bp) {

    void *next = NEXT_BLKP(bp);
    void *prev = PREV_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(HDRP(prev));
    size_t next_alloc = GET_ALLOC(HDRP(next));

    if (prev_alloc && next_alloc) {
        add_efl(bp);
        return bp;
    }

    if (prev_alloc && !next_alloc){
        remove_efl(next);
        size_t size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(next));
        PUT(FTRP(next), PACK(size, 0));
        PUT(HDRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc){
        remove_efl(prev);
        size_t size = GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(prev), PACK(size, 0));
        bp = prev;
    }
    else{
        remove_efl(prev);
        remove_efl(next);
        size_t size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(prev)) + GET_SIZE(FTRP(next));
        PUT(HDRP(prev), PACK(size, 0));
        PUT(FTRP(next), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    add_efl(bp);
	return bp;

}


/*
 * find_fit - Find a fit for a block with asize bytes
 * return a pointer to a block of a correct size.
 * if can't find such block, return NULL
 */
static void *find_fit(size_t asize) {
    /* search from the start of the free list to the end */

    if (head_free == NULL){
        return NULL;
    }
    for (char *cur_block = head_free; cur_block != NULL; cur_block = GET_NEXT_FREE(cur_block)) {
        assert(GET_ALLOC(HDRP(cur_block)) == 0 );
        if (asize <= GET_SIZE(HDRP(cur_block))){
            return cur_block;
        }
    }
    return NULL;  /* no fit found */
}


/*
 * extend_heap - Extend heap with free block and return its block pointer
 *               coalesce the added block with previous block if possible
 */
static void *extend_heap(size_t words) {
    // create the block and then add to explicit free list
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = words * WSIZE;
    if (words % 2 == 1)
        size += WSIZE;

    if ((long)(bp = mem_sbrk(size)) < 0)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * check_heap -- Performs basic heap consistency checks for an explicit free list allocator
 * and prints out all blocks in the heap in memory order.
 * Checks include proper prologue and epilogue, alignment, free list consistency, and matching header and footer
 * Takes a line number (to give the output an identifying tag).
 */
static bool check_heap(int line) {
    char *bp;

    if ((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))) {
        printf("(check_heap at line %d) Error: bad prologue header\n\n", line);
        return false;
    }

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!check_block(line, bp)) {
            return false;
        }
    }

    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("(check_heap at line %d) Error: bad epilogue header\n\n", line);
        return false;
    }
    if (head_free != NULL){
    	for (bp = head_free; bp != NULL; bp = GET_NEXT_FREE(bp)){
	    	if (GET_ALLOC(HDRP(bp))){
		    	printf("(check heap at line %d) Error: allocated block in explicit free list\n\n", line);
		    	return false;
	    	}
	}
    }

    return true;
}

/*
 * check_block -- Checks a block for alignment, correct pointers in EFL, proper coalescing, and matching header and footer
 */
static bool check_block(int line, void *bp) {

    if (bp == GET_NEXT_FREE(bp)){
        printf("(check_heap at line %d) Error: there is a closed cycle\n", line);
        return false;
    }
    if ((size_t)bp % DSIZE) {
        printf("(check_heap at line %d) Error: %p is not double-word aligned\n", line, bp);
        return false;
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("(check_heap at line %d) Error: header does not match footer\n", line);
        return false;
    }
    if (!GET_ALLOC(HDRP(bp)) && (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_ALLOC(HDRP(PREV_BLKP(bp))))){
	    printf("(check_heap at line %d) Error: block %p not fully coalesced\n", line, bp);
	    return false;
    }
    return true;
}

/*
 * print_heap -- Prints out the current state of the heap
 */
static void print_heap() {
    char *bp;

    printf("Heap (%p):\n", heap_start);

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        print_block(bp);
    }

    print_block(bp);
}
 /*
  * print_efl - prints out the currect state of the explicit free list;
  */
static void print_efl() {
	void *bp = head_free;
	while (bp != NULL){
		print_block(bp);
		bp = GET_NEXT_FREE(bp);
	}
}
/*
 * print_block -- Prints out the current state of a block
 */


static void print_block(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: End of free list\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
       hsize, (halloc ? 'a' : 'f'),
       fsize, (falloc ? 'a' : 'f'));
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}
