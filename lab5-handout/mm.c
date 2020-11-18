/*
 * CS 208 Lab 5: Malloc Lab
 *
 * <Please put your name and userid here>
 *
 * Simple allocator based on implicit free lists, first fit search,
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
 * if and only if the block is allocated. The list has the following form:
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

/* Setting next free block to the head */
#define SET_NEXT_FREE(bp, val) (PUT(bp, (size_t)val))
#define SET_PREV_FREE(bp, val) (PUT(PADD(bp, WSIZE), (size_t)val))

/* Global variables */

// Pointer to first block
static void *heap_start = NULL;

//Pointer to the first "free" block
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
static bool in_efl(void *bp);
static size_t max(size_t x, size_t y);

/*
 * mm_init -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
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
    check_heap(__LINE__);
    return 0;
}

/*
 * mm_malloc -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
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
    check_heap(__LINE__);
    return bp;
}


/*
 * add_efl - setting the next pointer of the current block to the curr_head of the free list
 * sett the prev_ptr of curr_head of the free list to the curr_block
*/
static void add_efl(void *bp){

    check_heap(__LINE__);
    // if head is null
    if (head_free == NULL){
        head_free = bp;
        SET_NEXT_FREE(head_free, NULL);
        SET_PREV_FREE(head_free, NULL);
    }
    else{
        //set next free pointer of the bp to the curr_head
        SET_NEXT_FREE(bp, head_free);

        //set the prev_free pointer of the head to the current block
        SET_PREV_FREE(head_free, bp); 
	SET_PREV_FREE(bp, NULL);
        // update head_free to show new head as the bp
        head_free = bp;
    }

    check_heap(__LINE__);
} 

/*
 * remove_efl - resetting pointers 
 * given a bp,
 * we set the prev_free of next block after the curr block to prev_free of curr block
 * we set the next_free of the prev block to the next block after curr block
*/
static void remove_efl(void*bp){
    //set head_free to the next block after the head
    // set the prev_free of the head ad to NULL
    assert(head_free!=NULL); // throws an error crash 

    check_heap(__LINE__);
    if (bp == head_free){
        if (GET_NEXT_FREE(bp)==NULL){
            head_free = NULL;
        }
        else{
            head_free = GET_NEXT_FREE(bp);
            SET_PREV_FREE(head_free, NULL);
	    SET_NEXT_FREE(bp, NULL);
        }
    }
    else if (GET_NEXT_FREE(bp) == NULL){
        SET_NEXT_FREE(GET_PREV_FREE(bp), NULL);
	SET_PREV_FREE(bp, NULL);
    }
    else{
        SET_PREV_FREE(GET_NEXT_FREE(bp), GET(GET_PREV_FREE(bp)));
	SET_NEXT_FREE(bp, NULL);
        SET_NEXT_FREE(GET_PREV_FREE(bp), GET(GET_NEXT_FREE(bp)));
	SET_PREV_FREE(bp, NULL);
    }
    check_heap(__LINE__);
}

static bool in_efl(void *bp){
	void *p;
	for (p = head_free; p != NULL; p = GET_NEXT_FREE(p)){
		if (p == bp) return true;
	}
	return false;
}


/*
 * mm_free -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void mm_free(void *bp) {
    check_heap(__LINE__);
    print_efl();
	PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
	PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), 0));
	coalesce(bp);
	print_efl();
    check_heap(__LINE__);
    /* set the allocated bit of the header and footer to 0; optionally - set the payload to 0;  coalesce with the prev block */
}

/* The remaining routines are internal helper routines */


/*
 * place -- Place block of asize bytes at start of free block bp
 *          and <How are you handling splitting?>
 * Takes a pointer to a free block and the size of block to place inside it
 * Returns nothing
 * <Are there any preconditions or postconditions?>
 */
static void place(void *bp, size_t asize) {
    check_heap(__LINE__);
    // What to do if the block is only 16 bytes bigger? it wouldn't make sense to make a block with only the header and footer.
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
    
    check_heap(__LINE__);
	return;

    // REPLACE THIS
    // currently does no splitting, just allocates the entire free block
    /* if fits, don't do anything; if it doesn't and its size is at least asize + 16, 
     * change the header to asize and allocated; add a footer at a correct distance from the header, set it to asize and allocated; the next block is the header of the remaining free stuff; set it to previous bp size - asize and unallocated; go to where its footer should be, set it to the same.
     * go to the footer of free block and set its size S to S - asize; `  */
}

/*
 * coalesce -- Boundary tag coalescing.
 * Takes a pointer to a free block
 * Return ptr to coalesced block
 * <Are there any preconditions or postconditions?>
 */
static void *coalesce(void *bp) {
    void *next = NEXT_BLKP(bp);
    void *prev = PREV_BLKP(bp);

    //if current block not alloc, next bloc not alloc, merge those two 
        // remove the next of bp

    if (GET_ALLOC(HDRP(next)) == 0){
        remove_efl(next);
        size_t size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(next));
        PUT(FTRP(next), PACK(size, 0));
        PUT(HDRP(bp), PACK(size, 0));   
    }

    //if current block not alloc, prev bloc not alloc, merge those two 
        // remove the bp
    if (GET_ALLOC(HDRP(prev)) == 0){
        size_t size = GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(prev), PACK(size, 0));
    check_heap(__LINE__);
    print_efl();
        return prev;
    }
    if (GET_ALLOC(HDRP(bp)) == 0) add_efl(bp);
    check_heap(__LINE__);
    print_efl();
	return bp;
/* if current or previous block is allocated, do nothing; if both are free, erase the footer of previous block and header of current block; go to the header of previous block and set its size to size of current block + size of previous block; go to the footer of current block and update the size; call coalesce with a pointer to the previous block as an argument  */	
}


/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize) {
    /* search from the start of the free list to the end */
    check_heap(__LINE__);
    assert(head_free!=NULL);
    for (char *cur_block = head_free; cur_block != NULL; cur_block = GET_NEXT_FREE(cur_block)) {
        if (!GET_ALLOC(HDRP(cur_block)) && (asize <= GET_SIZE(HDRP(cur_block))))
            return cur_block;
    }
    check_heap(__LINE__);
    return NULL;  /* no fit found */
}


/*
 * extend_heap - Extend heap with free block and return its block pointer
 *;*/
static void *extend_heap(size_t words) {
    // create the block and then add to explicit free list 
    char *bp;
    size_t size;

    check_heap(__LINE__);
    /* Allocate an even number of words to maintain alignment */
    size = words * WSIZE;
    if (words % 2 == 1)
        size += WSIZE;
    // printf("extending heap to %zu bytes\n", mem_heapsize());
    if ((long)(bp = mem_sbrk(size)) < 0)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    check_heap(__LINE__);
    return coalesce(bp);
}

/*
 * check_heap -- Performs basic heap consistency checks for an implicit free list allocator
 * and prints out all blocks in the heap in memory order.
 * Checks include proper prologue and epilogue, alignment, and matching header and footer
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
 * check_block -- Checks a block for alignment and matching header and footer
 */
static bool check_block(int line, void *bp) {
    if ((size_t)bp % DSIZE) {
        printf("(check_heap at line %d) Error: %p is not double-word aligned\n", line, bp);
        return false;
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("(check_heap at line %d) Error: header does not match footer\n", line);
        return false;
    }
    if (!GET_ALLOC(HDRP(bp)) && !in_efl(bp)){
	    printf("(check_heap at line %d) Error: free block not in explicit free list\n", line);
	    return false;
    }
    if (!GET_ALLOC(HDRP(bp)) && (!GET_ALLOC(NEXT_BLKP(bp)) || !GET_ALLOC(PREV_BLKP(bp)))){
	    printf("(check_heap at line %d) Error: block %lu not fully coalesced", line, (size_t) bp);
	    return false;
    }
    return true;
}

/*
 * print_heap -- Prints out the current state of the implicit free list
 */
static void print_heap() {
    char *bp;

    printf("Heap (%p):\n", heap_start);

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        print_block(bp);
    }

    print_block(bp);
}

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
