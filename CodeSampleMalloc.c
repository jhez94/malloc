/*
 *
 * Jeffrey He - jmhe@andrew.cmu.edu
 * Code originally written for Computer Systems (15213) course at CMU
 * This is code written to be implemented as part of the malloc library in C
 * Functions include malloc, calloc, free, and realloc. 
 *
 * This is an explicit list design for a general purpose dynamic memory allocator
 *
 * The heap is structured as follows
 * [ali][proH][proF][BLOCKS][epiH]
 *
 * ali = alignment block (size = WSIZE)
 * proH = prologue header (size = WSIZE)
 * proF = prologue footer (size = WSIZE)
 * epiH = epilogue header (size = WSIZE)
 *
 *
 * The BLOCKS is structured as follows
 * [bH]bp[data][op][bF] (for allocated blocks)
 * [bH]bp[pP][nP][op][bF] (for free blocks)
 *
 * bH = block header (size = WSIZE)
 * bF = block footer (size = WSIZE)
 * op = optional padding (for alignment)
 * 
 * pP = previous free block pointer (size = DSIZE)
 * nP = next free block pointer (size = DSIZE)
 *
 * bp = not part of the block, but where the block pointer points
 *
 *
 * The bH and bF (block header and block footer) is designed as follows
 * [block size][00x] (totally size = WSIZE)
 * where x is either 0 or 1, depending on whether it's allocated or not
 * 1 = allocated, 0 = not allocated
 *
 * - - - - - - - - - - - - - - - - - - - - - - 
 * Other details about implementation
 * -freed blocks are place at the front of the free list
 * -to find a free block, first fit is used
 * 
 *
 * - - - - - - - - - - - - - - - - - - - - - - 
 * heap_listp points to the beginning of the heap data (after prologue footer)
 * heap_free_listp points to the first free block 
 *
 *
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define HEAPSTART 0x800000000 /*minimum heap address*/
#define CHUNKSIZE (1<<9) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Read and write a Dword or pointer at address p */
#define GETL(p) (unsigned long)(*(unsigned int *)(p))+HEAPSTART
#define PUTL(p, val) (*(unsigned int *)(p) = (unsigned int)(unsigned long)((val)-HEAPSTART))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

 /* Given block ptr bp, compute address of next and previous pointers */
#define NEXT_PTR(bp) ((char *)(bp) + (unsigned int)WSIZE)
#define PREV_PTR(bp) ((char *)(bp))


//Function and Variable Declaration
int mm_init(void);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void add_free_list(void *bp);
static void rm_free_list(void *bp);
void *malloc(size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void free(void *ptr);
void *realloc(void *oldptr, size_t size);
void *calloc (size_t nmemb, size_t size);
void mm_checkheap(int verbose);
//static void printblock(void *bp);
static void printfreeblock(void *bp);
static void checkblock(void *bp);
static void checkfreeblock(void *bp);

static char* heap_listp;
static char* heap_free_listp;


/*
 * Initialize: return -1 on error, 0 on success.
 *
 * Initialized four words worth of space, and sets the alignment padding
 * the prologue header and footer, and the epilogue header
 * Then we extended the heap by Chunksize/Wsize
 *
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE);

    heap_free_listp = (void *)HEAPSTART;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * Extends the heap 
 *
 * After make sure the extention size is an even number of words
 * Set the header and footer of the new (extended) block
 * Then recreate the new epilogue header
 *
 */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;
 
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;


    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
 
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/*
 * Function that coalesces, or joins, two adjacent free blocks
 *
 * Description 
 * 1: No adjacent blocks are free, 
 *    so just add the new free block to the free list
 * 2: The following block is also free, 
 *    so remove the following block from the free list
 *    and then make them into one bigger block, and then 
 *    add the new block to the free list
 * 3: Same as above, except the previous block is free
 * 4: Both blocks are free, so join all three free blocks together
 *    and then add it to the free list
 *
 */
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    //1:If no adjacent blocks are free
    if (prev_alloc && next_alloc) {
        add_free_list(bp);
        return bp;
    }
    //2:If following block is free
    else if (prev_alloc && !next_alloc) {
        rm_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    //3:If previous block is free
    else if (!prev_alloc && next_alloc) {
    	rm_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //4:If both adjacent blocks are free
    else {
    	rm_free_list(PREV_BLKP(bp));
        rm_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_free_list(bp);
    return bp;
}

/*
 * add_free_list function;
 * adds a freed block to the free block list
 * implementation is to add it to the front of the list
 *
 */
static void add_free_list(void *bp){
    //heap_free_listp points to first block
    void *firstBlock = (heap_free_listp); //0 if free list empty
    
    //new block points to first block
    //nextPTR points to 0 if last/only element
    PUTL(NEXT_PTR(bp),(unsigned long)firstBlock);
    
    //if there existed a block on the free list
	//first block points back at new block
    if(heap_free_listp != (void *)HEAPSTART){ 
        PUTL(PREV_PTR(firstBlock),(unsigned long)bp);
    }
	
    //free list pointer points to new block
	heap_free_listp = bp;
	
    //new block points to 0, to denote first block
	PUTL(PREV_PTR(bp),(unsigned long)HEAPSTART);
}

/*
 * rm_free_list function;
 * once a block has been allocated, remove it from the free list
 * details of various cases below
 *
 */
static void rm_free_list(void *bp){
	void *preFreeBlock = (void *)(long)GETL(PREV_PTR(bp)); //0 if no preFreeBlock
	void *nextFreeBlock = (void *)(long)GETL(NEXT_PTR(bp)); //0 if no nextFreeBlock 

	//if there are blocks on either side
	//set the points of those two blocks to each other
	if ((preFreeBlock != (void *)HEAPSTART) && (nextFreeBlock != (void *)HEAPSTART)){
        PUTL(NEXT_PTR(preFreeBlock),(unsigned long)nextFreeBlock);
		PUTL(PREV_PTR(nextFreeBlock),(unsigned long)preFreeBlock);
	}
	//if there is only a block after
	//set the block after's previous block pointer to 0
	//set the free list pointer to the next block
	else if ((preFreeBlock == (void *)HEAPSTART) && (nextFreeBlock != (void *)HEAPSTART)){
        PUTL(PREV_PTR(nextFreeBlock),HEAPSTART);
		heap_free_listp = nextFreeBlock;
	}
	//if there is only a block before
	//set the block before's next block pointer to 0
	else if ((preFreeBlock != (void *)HEAPSTART) && (nextFreeBlock == (void *)HEAPSTART)){
        PUTL(NEXT_PTR(preFreeBlock),HEAPSTART);
	}
	//if there are no blocks on either side
	//simply set the free list pointer to 0
	else if ((preFreeBlock == (void *)HEAPSTART) && (nextFreeBlock == (void *)HEAPSTART)){
		heap_free_listp = (void *)HEAPSTART;
	}
	//you really shouldn't reach here as all cases should be covered
	else{
		printf("Something wrong with free list (in rm_free_list)");
	}
}


/*
 * 
 * allocate of block of memory that is big enough for the payload
 * as well as the header and footer
 *
 * must always allocate a size that is a multiple of the alignment 
 *
 */
void *malloc(size_t size){
    
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    
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
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
 }

/*
 * place a block of size (asize) into bp
 * split the block if it is big enough for another free block
 * adds / removes from the free list as appropriate
 *
 */
 static void place(void *bp, size_t asize){
 	//get the size of the choosen block
 	size_t csize = GET_SIZE(HDRP(bp));

 	//if there is more than 4*DSIZE (minimum) amount of space left
 	//split it and then give the extra space back to free list
    if ((csize - asize) >= (2*DSIZE)) {
        rm_free_list(bp);
    	//create appropriate headers/footers for the newly allocated block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
    	
        //mark the extra space as unallocated and add back to free list
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_free_list(bp);
    }
    else {
    	//simply mark block as allocated, and remove from free list
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        rm_free_list(bp);
    }
 }

/*
 * 
 * function that transverses the free list and finds
 * a block that is big enough for the given size
 *
 * if it finds an appropriate block, return the pointer to it
 * otherwise return null
 *
 */
static void *find_fit(size_t asize){
	void *bp;
	//if there are no elements on the free list, just abort and return NULL
	if (heap_free_listp == (void *)HEAPSTART) return NULL;

	//tranverse the free list until you find a block big enough
	//or until you reach the end of the free list
	for (bp = heap_free_listp; (long)NEXT_PTR(bp) > 0; 
            bp = (void *)(long)GETL(NEXT_PTR(bp))){
        if ((bp == (void *)0) || (bp == heap_listp-DSIZE)) return NULL;
        //you've reach the end of the free list
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
			return bp;
		}
	}
    return NULL;
}

/*
 * free the block by marking it as unallocated
 * also add to free list within coalesce
 *
 */
void free (void *ptr) {
    if (ptr == NULL)
       return;  
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}


/*
 * simply a wrapper function for malloc that also 
 * clears all the bits and sets them to 0
 *
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * resizes a block (oldptr) to the size requested
 *
 */
void *realloc(void *oldptr, size_t size) {

/* If size == 0 then this is just free, and we return NULL. */
  	if(size == 0) {
    	free(oldptr);
    	return 0;
  	}

 /* If oldptr is NULL, then this is just malloc. */
  	if(oldptr == NULL) {
   		return malloc(size);
  	}

    size_t oldsize;
    void *newptr;

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = *SIZE_PTR(oldptr);
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;

}

/*
 *
 * function that makes sure that the heap is not corrupted / has errors
 * These are the things it checks (typically what the print statments say)
 * -makes sure the heap doesnt extend past allocated memory
 * -makes sure the prologue header is not corrupt [size][allocated]
 * -makes sure the prologue footer is not corrupt [size][allocated]
 * -makes sure that the prologue header and footer match each other
 * -makes sure there are no contiguous free blocks in memory
 * -make sure all pointers accessed are in the heap
 * -make sure that pointers are aligned properly
 * -make sure blockpointers are doubleword aligned
 * -make sure that the header and footer match for blocks
 * -make sure that there are no circular lists
 * -make sure that the next block's prev block is self
 * -make sure that the prev block's next block is self
 *
 *
 */
void mm_checkheap(int verbose) {
    void *bp;
    size_t *heapStart = mem_heap_lo();
    size_t *heapEnd = mem_heap_hi();

    if (verbose)
    printf("Heap (%p):\n", heap_listp);

    if (heapStart + (char)mem_heapsize() > heapEnd){
        printf("%p\n",heapStart+(char)mem_heapsize());
    	printf("%p,%d,%p\n",heapStart,(int)mem_heapsize(),heapEnd);
        printf("heap extends past what was allocated\n");
    }

	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) 
			|| !GET_ALLOC(HDRP(heap_listp))){
    	printf("Bad prologue header\n");
	}

	if ((GET_SIZE(FTRP(heap_listp)) != DSIZE) 
			|| !GET_ALLOC(HDRP(heap_listp))){
    	printf("Bad prologue footer\n");
	}

    if (GET_SIZE(HDRP(heap_listp)) != GET_SIZE(FTRP(heap_listp))
        || GET_ALLOC(HDRP(heap_listp)) != GET_ALLOC(FTRP(heap_listp)))
        printf("Prologue header and footer don't match\n");

    int isFree = GET_ALLOC(HDRP(heap_listp));
    if (verbose) printf("\n Entire Heap \n");
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if ((isFree == 0) && ((isFree = GET_ALLOC(HDRP(bp))) == 0)){
           printf("Two contiguous free blocks in memory!");
           assert(0);
        } 
        if (verbose) printfreeblock(bp);
        checkblock(bp);
    }
    
    if (verbose) printf("\n Free List \n");
	for (bp = heap_free_listp; (long)NEXT_PTR(bp) > 0; 
            bp = (void *)(long)GETL(NEXT_PTR(bp))) {
        //If you've reach the end, or circled back around, stop
        if ((bp == (void *)0) || (bp == heap_listp-DSIZE)) return;
        if (verbose) printfreeblock(bp);
        checkfreeblock(bp);
    }
}
/*
//simply prints the entire heap
static void printblock(void *bp){
    
    size_t hsize, halloc, fsize, falloc;
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp)); 
    void *prevP, *nextP;
    prevP = (void *)PREV_PTR(bp);
    nextP = (void *)NEXT_PTR(bp);

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] | footer: [%d:%c]\n", 
    	bp, 
        (int)hsize, (halloc ? 'a' : 'f'), 
        (int)fsize, (falloc ? 'a' : 'f'));

}*/

//simply prints all the free blocks
static void printfreeblock(void *bp){
    
    size_t hsize, halloc, fsize, falloc;
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp)); 
    void *prevP, *nextP;
    prevP = (void *)PREV_PTR(bp);
    nextP = (void *)NEXT_PTR(bp);

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] | %p:%p | %p:%p | footer: [%d:%c]\n", 
    	bp, 
        (int)hsize, (halloc ? 'a' : 'f'), 
        prevP,(void *)(long)GETL(prevP), nextP,(void *)(long)GETL(nextP),
        (int)fsize, (falloc ? 'a' : 'f'));

}

//checks to see point is in heap
static int in_heap(const void *p){
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}
//checks to see point is aligned
static int aligned(const void *p){
    return (size_t)ALIGN(p)==(size_t)p;
}

//checks for double word alignment,headers/footers match
static void checkblock(void *bp){
    if ((size_t)bp % 8){
        printf("Error: %p is not doubleword aligned\n", bp);
        assert(0);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))){
        printf("Error: header does not match footer\n");
        assert(0);
    }
    if (!in_heap(bp)){
        printf("Error: pointer is not in heap\n");
        assert(0);
    }
    if (!aligned(bp)){
        printf("Error: pointer is not aligned\n");
        assert(0);
    }
}

//makes sure next block's prev block is self
static void nextPrev(void *bp){
    unsigned long next = GETL(NEXT_PTR(bp));
    //if null, end of block
    if ((next == 0) || (next == (unsigned long)heap_listp-DSIZE)) return; 
    unsigned long self = GETL(PREV_PTR(next));
    if (bp != (void *)self){
        printf("Error: Next Block's Prev Block not self");
        printf("    %p,%p\n",bp,(void *)self);
    }
}

//makes sure prev block's next block is self
static void prevNext(void *bp){
    unsigned long next = GETL(PREV_PTR(bp));
    if ((next == 0) || (next == (unsigned long)heap_listp-DSIZE)) return; 
    unsigned long self = GETL(NEXT_PTR(next));
    if (bp != (void *)self){
        printf("Error: Prev Block's Next Block not self");
        printf("    %p,%p\n",bp,(void *)self);
    }
}

//makes sure prev block's next block is self
//makes sure next block's prev block is self
static void checkfreeblock(void *bp){
    nextPrev(bp);
    prevNext(bp);
}

