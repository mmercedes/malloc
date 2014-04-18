/*
 * mm.c
 * mmercede - Matthew Mercedes
 *
 *
 * Implements a segregated free list
 * 25 free lists each repsenting block sizes of 2^5 - 2^29
 * Minimum block size is 32 bytes : 
 *      HEADER(8) + 2*POINTER(8) + FOOTER(8) = 32 bytes
 *  
 *
 * Segmented Free List block sizes diagram:
 *      [ 32-63 | 64-127 | 128-255 | 256-511 | ... | 2^29 ]
 *
 * So index n corresponds to a size of 2^(n+5) - 2^(n+6)-1
 * 
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

 #define HEADER_SIZE 8
 #define FOOTER_SIZE 8
 #define NUM_FREE_LISTS 25
 #define MIN_SIZE 32  // (HEADER + FOOTER + 8)
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

    return (void*)(block+1);
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


// sets the pointer to the previous free block
static inline void set_prev_pointer(uint64_t* block, uint64_t* p){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    *(uint64_t**)(block+1) = p;
}


// sets the pointer to the next free block
static inline void set_next_pointer(uint64_t* block, uint64_t* p){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    *(uint64_t**)(block+2) = p;   
}


// sets the size of a block of memory
static inline void set_size(uint32_t* block, size_t size){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    *block = size & 0x3FFFFFFF;
    *((uint64_t*)block + block_size(block)/sizeof(uint64_t*) - 1) = size & 0x3FFFFFFF;
}


// returns the header of a block from a pointer malloc returned
static inline void* block_from_ptr(uint64_t* ptr){
    REQUIRES(ptr != NULL);

    return (void*)(ptr - 1);
}

/*
 * Define helper functions
 * -----------------------
 */

static int get_free_list_index(size_t size);
static void* find_free_block(int index, size_t size);
static void* allocate_block(size_t size);
static void* split_block(void* p, size_t request_size);
static void remove_block_from_list(void* block);
static void add_block_to_list(int index, void* block);
static int coalesce(void** block);


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
    if(heap_start == (void*) -1) return -1;

    free_lists = heap_start;
    current = heap_start;

    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        *current = NULL;
        current++;
    }

    heap_start = (uint64_t*)current + 1;

    return 0;
}


// returns a pointer to memory of given size
void *malloc (size_t size) {
    void* p;
    int index;

    if(size == 0) return NULL;
    size += 8 - size%8;
    if(size < 16) size += 8;
    size += (HEADER_SIZE + FOOTER_SIZE);
    if(size > MAX_SIZE) return NULL;

    index = get_free_list_index(size);
    p = find_free_block(index, size);

    if(p == NULL) return NULL;

    p = block_mem(p);
    return p;
}


// return allocated memory
void free (void *ptr) {
    void* block;
    int index;

    if (ptr == NULL) {
        return;
    }
    block = block_from_ptr(ptr);
    
    index = coalesce(&block);

    block_mark(block, 1);
    add_block_to_list(index, block);

    return;    
}


// returns a pointer to a new allocation
// if ptr is null, acts like malloc
// if size is zero, acts like free
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
    return newptr;
}

// simple wrapper for malloc that sets mem to zero
void* calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *ptr;

    ptr = malloc(bytes);
    memset(ptr, 0, bytes);
    return ptr;
}


// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    void* current;
    void* prev;
    void* right;
    void* left;
    size_t size;
    size_t lb_size;

    // check the free list
    for(int i = 0; i < NUM_FREE_LISTS; i++){
        current = free_lists[i];
        prev = NULL;

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

            if(block_prev(current) != prev){
                if(verbose) printf("HEAP ERROR: invalid prev pointer\n");
                return 1;
            }
            
            if(!block_free(current)){
                if(verbose) printf("HEAP ERROR: free block marked wrong\n");
                return 1;
            }

            if(!aligned(current) || !aligned(block_mem(current))){
            	if(verbose) printf("HEAP ERROR: block not aligned\n");
            	return 1;
            }
            prev = current;
            current = block_next(current);
        }
    }
    current = heap_start;

    // check the heap
    while(in_heap(current)){
    	if(block_size(current) == 0) break;

    	size = block_size(current);
    	right = ((uint64_t*)current)+(block_size(current)/sizeof(uint64_t*));
	    lb_size = *((uint32_t*)current - 2) & MAX_SIZE;
    	left =  (uint64_t*)current - lb_size/sizeof(uint64_t*);

	   	if(!aligned(current)){
	   		if(verbose) printf("HEAP ERROR: block not aligned\n");
	   		return 1;
	    }

	   	if(*(uint32_t*)current != block_size(current)){
	   		if(verbose) printf("HEAP ERROR: header/footer not matching\n");
	   		return 1;
	    }

	   	if(block_free(current)){
    		if((in_heap(right) && block_free(right)) ||
	   		   (in_heap(left) && block_free(left))){
	   			if(verbose) printf("HEAP ERROR: two adjacent free blocks\n");
	   			return 1;
	   		}
	    }
    	current = right;
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

    // calculate log base 2
    while (size >>= 1) index++;
    //lowest index is for size 2^6
    index -= 5; 
  
    ENSURES(0 <= index && index < NUM_FREE_LISTS);
    return index;
}


// Returns a pointer if block of sufficient size is available 
// will allocate a new block if none are free
static void* find_free_block(int index, size_t size){
    REQUIRES(0 <= index && index < NUM_FREE_LISTS);

    void* block = NULL;
    void* current; 
    size_t curr_size;

    while(index < NUM_FREE_LISTS){
    	current = free_lists[index];

    	while(current != NULL){
    		curr_size = block_size(current);

    		if(curr_size > size+MIN_SIZE){
    			remove_block_from_list(current);
    			block = split_block(current, size);
    			block_mark(block, 0);
    			return block;
    		}
    		if(curr_size >= size){
    			remove_block_from_list(current);
    			block_mark(current, 0);
    			return current;
    		}
    		current = block_next(current);
    	}
        index++;
    }
    block = allocate_block(size);

    ENSURES(block != NULL);
    return block;
}


// removes a block from a free list
// does this by having the next and prev blocks
// point to each other instead of block
static void remove_block_from_list(void* block){
    REQUIRES(in_heap(block));

    void* next = block_next(block);
    void* prev = block_prev(block);

    int index = get_free_list_index(block_size(block));

    if(free_lists[index] == block) free_lists[index] = next;

    if(prev != NULL) set_next_pointer(prev, next);
    if(next != NULL) set_prev_pointer(next, prev);
}


// adds a block to the front of a free list
static void add_block_to_list(int index, void* block){
    REQUIRES(0 <= index && index <= NUM_FREE_LISTS);
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    set_prev_pointer(block, NULL);
    set_next_pointer(block, free_lists[index]);

    if(free_lists[index] != NULL){
    	set_prev_pointer(free_lists[index], block);
    }

    free_lists[index] = block;
}


// split a block
// moves split piece to correct free list
// returns a pointer to the block that was split
static void* split_block(void* p, size_t request_size){
	REQUIRES(p != NULL);
	REQUIRES(request_size <= MAX_SIZE);

    size_t b_size = block_size(p);
    size_t split_size = b_size - request_size;
    void* split;
    void* right;
    int new_index;

    if(split_size < MIN_SIZE) return p;

    split = (uint64_t*)p + request_size/sizeof(uint64_t*);
    right = (uint64_t*)p + b_size/sizeof(uint64_t*);

    // try to coalesce right
    if(right <= mem_heap_hi() && block_free(right)){
    	if(block_size(right) + split_size <= MAX_SIZE){
    		remove_block_from_list(right);
    		split_size += block_size(right);
    	}
    }

    set_size(p, request_size);
    set_size(split, split_size);

    block_mark(split, 1);
    new_index = get_free_list_index(split_size);   
    add_block_to_list(new_index, split);

    return p;
}


// calls mem_sbrk to extend heap for a single block
// returns a pointer to the new block
static void* allocate_block(size_t size){
	REQUIRES(size <= MAX_SIZE);

    void* block;
    
    // this is to reduce the # of mem_sbrk calls
    // 512 was chosen after testing multiple sizes
    if(size < 512){
    	block = mem_sbrk(512);
        if(block == (void*) -1) return NULL;
        set_size(block, 512);
        block = split_block(block, size);
        block_mark(block, 0);
        return block;
    }

    block = mem_sbrk(size);
    if(block == (void*) -1) return NULL;

    set_size(block, size);
    block_mark(block, 0);

    return block;
}


// looks left and right for free blocks
// forms bigger block if possible
static int coalesce(void** block){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(*block));

    void* right;
    void* left;
    uint32_t lb_size;
    size_t size = block_size(*block);
    size_t new_size = size;
    int index;

    right = ((uint64_t*)*block)+(block_size(*block)/sizeof(uint64_t*));

    lb_size = *((uint32_t*)*block - 2) & MAX_SIZE;
    left =  (uint64_t*)*block - lb_size/sizeof(uint64_t*); 

    if(left >= heap_start && block_free(left)){
    	new_size += lb_size;

    	if(new_size <= MAX_SIZE){
    		remove_block_from_list(left);
    		*block = left;
    		set_size(*block, new_size);
    	}
    	else new_size = size;
    }
    
    if(right <= mem_heap_hi() && block_free(right)){
    	new_size = new_size + block_size(right);

    	if(new_size <= MAX_SIZE){
    		remove_block_from_list(right);
    		set_size(*block, new_size);
    	}
    	else new_size -= block_size(right);
    }

    index = get_free_list_index(new_size);
    return index;
}
