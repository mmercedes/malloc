/*
 * mm.c
 * mmercede - Matthew Mercedes
 *
 *
 * Implements a seggregated free list
 * 24 free lists each repsenting block sizes of 2^5 - 2^29
 * Minimum block size is 64 bytes : 
 *      HEADER (12) + 1 + FOOTER (12) = 25 bytes
 *      This gets rounded to nearest power of 2 which is 32
 *
 * Segmented Free List block sizes diagram:
 *      [ 32 | 64 | 128 | 256 | 512 | 1024 | ... | 2^29 ]
 *
 * So index n corresponds to a size of 2^(n+5)
 * I make use of this in my get_free_list_index function
 *
 * Pointers to each free list are placed at beginning of the heap
 *
 */


#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 * Define constants
 * ----------------
 */

// Minimum block size is 64 bytes (16 + 16 + 1 rounds to 64)
 #define HEADER_SIZE 12
 #define FOOTER_SIZE 12
 #define NUM_FREE_LISTS 25
 #define MAX_SIZE 0x3FFFFFFF

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

// Calculate the nearest (rounding up) power of 2
// This becomes the block size for the allocation request
static size_t get_block_size(size_t size){
    size--;
    size += HEADER_SIZE;
    size += FOOTER_SIZE;
    size |= size >> 1;
    size |= size >> 2;
    size |= size >> 4;
    size |= size >> 8;
    size |= size >> 16;
    size += 1
    return size;
}

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block in multiples of the word size
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (block[0] & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    //unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    //block[next] = block[0];
}

// Return a pointer to the memory malloc should return
static inline void* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 2));

    return (void*)(block+1+sizeof(void*));
}

// Return the header to the previous block
static inline void* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return *((void*)(block+1));
}

// Return the header to the next block
static inline void* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block+(block_size(block)/sizeof(void*));
}


static int get_free_list_index(size_t size);
static void* find_free_block(int index, size_t block_size, size_t request_size);
static void* allocate_block();
static int split_block(int index, size_t block_size);
static void remove_block_from_list(int index);

/*
 * Define global variables
 * -----------------------
 */

 void** free_lists;
 void* heap_start;
 //void* heap_end;

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 * Allocates space for free list pointers.
 * Sets each to point to NULL which means the end of the list.
 */
int mm_init(void) {
    void** current;

    heap_start = mem_sbrk(NUM_FREE_LISTS * sizeof(void*));
    if(heap_start == NULL) return -1;

    //heap_end = heap_start + NUM_FREE_LISTS;
    free_lists = heap_start;
    current_index = heap_start;

    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        *current_index = NULL;
        current_index++;
    }
}

/*
 * malloc
 */
void *malloc (size_t request_size) {
    void* p;
    size_t block_size;
    checkheap(1);  // Let's make sure the heap is ok!

    if(request_size == 0) return NULL;
    block_size = get_block_size(request_size);
    if(size > MAX_SIZE) return NULL;

    list_index = get_free_list_index(block_size);
    p = find_free_block(index, block_size, request_size);
    if(p == NULL) p = allocate_block();

    return p;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) {
        return;
    }
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    oldptr = oldptr;
    size = size;
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    nmemb = nmemb;
    size = size;
    return NULL;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    verbose = verbose;
    return 0;
}

// Returns the index for a free list with a block to fit the size request
static int get_free_list_index(size_t size){
    REQUIRES(0 < size && size <= 0x3FFFFFFF);

    int index = 0;

    // calculate log base 2
    while (size >>= 1) index++;
    //lowest index is for size 2^5
    index -= 5; 
  
    ENSURES(0 <= index && index < NUM_FREE_LISTS);
    return index;
}

// Returns a pointer if block of sufficient  available 
static void* find_free_block(int index, size_t block_size, size_t request_size){
    REQUIRES(0 <= index && index < NUM_FREE_LISTS);

    void* p;
    int index_incr = 0; // set to 1 if index increased 

    while(free_lists[index] == NULL && index < NUM_FREE_LISTS){
        index++;
        index_incr = 1;
    }
    if(index == NUM_FREE_LISTS) return NULL;

    p = block_mem((int32_t*) free_lists[index]);
    block_mark((int32_t*) free_lists[index], 0);

    if(index_incr) index = split_block(index, block_size);
    remove_block_from_list(index);

    ENSURES(p != NULL);
    return p;
}

/*  UNWRITTEN FUNCTIONS 

static void* allocate_block(){}

static int split_block(int index, size_t block_size){}

static void remove_block_from_list(int index){}