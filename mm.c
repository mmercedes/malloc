/*
 * mm.c
 * mmercede - Matthew Mercedes
 *
 *
 * Implements a segregate free list
 * 24 free lists each repsenting block sizes of 2^5 - 2^29
 * Minimum block size is 64 bytes : 
 *      HEADER (12) + PADDING(4) + 1 + FOOTER (12) = 29 bytes
 *      This gets rounded to nearest power of 2 which is 32
 *
 * Segmented Free List block sizes diagram:
 *      [ 32 | 64 | 128 | 256 | 512 | 1024 | ... | 2^29 ]
 *
 * So index n corresponds to a size of 2^(n+5)
 * I make use of this in get_free_list_index
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

 #define HEADER_SIZE 24
 #define FOOTER_SIZE 8
 #define NUM_FREE_LISTS 25
 #define MAX_SIZE 0x3FFFFFFF

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(void* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(void* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

// Calculate the nearest (rounding up) power of 2
// This determines which free list a block is added to
static size_t nearest_power_2(size_t size){
    size--;
    size |= size >> 1;
    size |= size >> 2;
    size |= size >> 4;
    size |= size >> 8;
    size |= size >> 16;
    size += 1;
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
static inline unsigned int block_size(void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    return (*((uint32_t*) block) & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(uint32_t* block) {
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
static inline void* block_mem(uint64_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block));
    REQUIRES(aligned(block + 3));

    return (void*)(block+3);
}

// Return the pointer to the previous block
static inline void* block_prev(uint64_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (void*)(*(block+1));
}

// Return the pointer to the next block
static inline void* block_next(uint64_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (void*)(*(block+2));
}

static inline void set_prev_pointer(uint64_t* block, uint64_t* p){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    *(uint64_t**)(block+1) = p;
}

static inline void set_next_pointer(uint64_t* block, uint64_t* p){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    *(uint64_t**)(block+2) = p;   
}

static inline void set_size(uint32_t* block, size_t size){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    *block = size & 0x3FFFFFFF;
    *(block + block_size(block)/sizeof(uint32_t*) - 1) = size & 0x3FFFFFFF;
}

// returns the header of a block from a pointer malloc returned
static inline void* block_from_ptr(uint64_t* ptr){
    REQUIRES(ptr != NULL);

    return (void*)(ptr - 3);
}

static int get_free_list_index(size_t size);
static void* find_free_block(int index, size_t size);
static void* allocate_block(size_t size);
//static void* split_block(int index);
static void remove_block_from_list(int index, void* block);
static void add_block_to_list(int index, void* block);
static int coalesce(void* block, size_t* size);


/*
 * Define global variables
 * -----------------------
 */

 void** free_lists;
 void* heap_start;

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

    free_lists = heap_start;
    current = heap_start;

    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        *current = NULL;
        current++;
    }
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    void* p;
    int index;

    checkheap(1);  // Let's make sure the heap is ok!

    if(size == 0) return NULL;

    size += 8 - size%8;
    size += (HEADER_SIZE + FOOTER_SIZE);

    if(size > MAX_SIZE) return NULL;

    index = get_free_list_index(size);
    p = find_free_block(index, size);

    if(p == NULL) return NULL;

    p = block_mem(p);

    checkheap(1);
    return p;
}

/*
 * free
 */
void free (void *ptr) {
    size_t size;
    void* block;
    int index;

    checkheap(1);

    if (ptr == NULL) {
        return;
    }
    block = block_from_ptr(ptr);
    index = coalesce(block, &size);

    block_mark(block, 1);
    //set_prev_pointer(block, NULL);
    //set_next_pointer(block, NULL);

    add_block_to_list(index, block);

    checkheap(1);
    return;    
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void* realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

      /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return NULL;
    }

      /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

      /* If realloc() fails the original block is left untouched  */
    if(newptr == NULL) {
        return NULL;
    }

      /* Copy the old data. */
    oldsize = block_size(block_from_ptr(oldptr));
    oldsize = oldsize - (HEADER_SIZE + FOOTER_SIZE);
    if(size < oldsize) oldsize = size;

    newptr = memmove(newptr, oldptr, oldsize);

      /* Free the old block. */
    free(oldptr);

    checkheap(1);
    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void* calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *ptr;

    ptr = malloc(bytes);
    memset(ptr, 0, bytes);

    checkheap(1);
    return ptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    void* current;
    //void* prev;
    size_t size;

    for(int i = 0; i < NUM_FREE_LISTS; i++){
        current = free_lists[i];
        //prev = NULL;

        while(current != NULL){
            if(!in_heap(current)){
                if(verbose) printf("HEAP ERROR: block not in heap\n");
                printf("CURRENT: %p\n", current);
                return 1;
            }

            size = block_size(current);
            if(size > MAX_SIZE){
                if(verbose) printf("HEAP ERROR: invalid block size\n");
                return 1;
            }
            /*
            if(block_prev(current) != prev){
                if(verbose) printf("HEAP ERROR: invalid prev pointer\n");
                return 1;
            }
            */
            if(!block_free(current)){
                if(verbose) printf("HEAP ERROR: block in list not marked free\n");
                return 1;
            }

            if(!aligned(current) || !aligned(block_mem(current))){
            	if(verbose) printf("HEAP ERROR: block not aligned\n");
            	return 1;
            }
            //prev = current;
            current = block_next(current);
        }
    }
    return 0;
}


///////////////////////////////////////////////////////////////////////////////
//                          HELPER FUNCTIONS                                 //
///////////////////////////////////////////////////////////////////////////////


// Returns the index for a free list with a block to fit the size request
static int get_free_list_index(size_t size){
    REQUIRES(0 < size && size <= 0x3FFFFFFF);

    int index = 0;

    size = nearest_power_2(size);
    // calculate log base 2
    while (size >>= 1) index++;
    //lowest index is for size 2^5
    index -= 5; 
  
    ENSURES(0 <= index && index < NUM_FREE_LISTS);
    return index;
}

// Returns a pointer if block of sufficient size is available 
// will allocate a new block if none are free
static void* find_free_block(int index, size_t size){
    REQUIRES(0 <= index && index < NUM_FREE_LISTS);

    void* block;
    void* current;
    int new_index = index; 

    while(new_index < NUM_FREE_LISTS){
    	current = free_lists[new_index];

    	while(current != NULL){
    		if(block_size(current) >= size){
    			// if(new_index > index){
    			// 	block = split_block(new_index);
    			// 	block_mark(block, 0);
    			// 	return block;
    			// }
    			block = current;
    			block_mark(block, 0);
    			remove_block_from_list(new_index, block);
    		}
    		current = block_next(current);
    	}
        new_index++;
    }
    assert(aligned(block));
    block = allocate_block(size);

    ENSURES(block != NULL);
    return block;
}


static void remove_block_from_list(int index, void* block){
    REQUIRES(0 <= index && index < NUM_FREE_LISTS);

    void* next = block_next(block);
    void* prev = block_prev(block);

    if(free_lists[index] == block) free_lists[index] = next;

    if(prev != NULL) set_next_pointer(prev, next);
    if(next != NULL) set_prev_pointer(next, prev);

    set_next_pointer(block, NULL);
    set_prev_pointer(block, NULL);
}


static void add_block_to_list(int index, void* block){
    REQUIRES(0 <= index && index <= NUM_FREE_LISTS);
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    set_prev_pointer(block, NULL);
    set_next_pointer(block, free_lists[index]);

    if(free_lists[index] != NULL) set_prev_pointer(free_lists[index], block);
    free_lists[index] = block;
}

// split a block in half
// moves split piece to correct free list
// returns a pointer to the block that was split

// static void* split_block(int index){
//     REQUIRES(0 <= index && index < NUM_FREE_LISTS);

//     size_t new_size;
//     uint64_t* new_block;
//     uint64_t* block;
//     int new_index;

//     block = free_lists[index];
//     remove_block_from_list(index, block);

//     new_size = block_size(block)/2;
//     new_block = block + (new_size/sizeof(uint64_t*));

//     set_size((uint32_t*)block, new_size);
//     set_size((uint32_t*)new_block, new_size);

//     new_index = get_free_list_index(new_size);
//     add_block_to_list(new_index, new_block);

//     set_prev_pointer(block, NULL);
//     set_next_pointer(block, NULL);

//     return block;
// }

static void* allocate_block(size_t size){
    void* block;
    
    block = mem_sbrk(size);
    if(block == NULL) return NULL;
    set_size(block, size);
    set_prev_pointer(block, NULL);
    set_next_pointer(block, NULL);
    block_mark(block, 0);

    return block;
}


static int coalesce(void* block, size_t* size){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    //uint64_t* left_block;
    void* right_block;
    size_t new_size;
    int index;

    void* next;
    void* prev;

    *size = block_size(block);
    new_size = (*size) * 2;
    index = get_free_list_index(*size);

    if(new_size > MAX_SIZE) return index;

    right_block = ((uint64_t*)block)+(block_size(block)/sizeof(uint64_t*));

    // if(in_heap(left_block) && block_free(left_block)){
    //     if(block_size(left_block) == size){
    //         set_size(left_block, size*2);
    //         add_block_to_list(get_free_list_index(size*2), left_block);
    //     }
    // }
    
    if(in_heap(right_block) && block_free((uint32_t*)right_block)){
        if(block_size(right_block) == new_size/2){

            next = block_next(right_block);
            prev = block_prev(right_block);

            if(free_lists[index] == right_block) free_lists[index] = next;
            if(prev != NULL) set_next_pointer(prev, next);
            if(next != NULL) set_prev_pointer(next, prev);

            set_size(block, new_size);
            *size = new_size;
            index++;
        }
    }
    return index;
}

