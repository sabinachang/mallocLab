/*
 ******************************************************************************
 *                                   mm.c                                     *
 *                              Andrew ID: enhanc                             *
 *           64-bit struct-based segregated list memory allocator             *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 * The allocator support malloc, realloc, calloc and free operations on heap.
 * It manages block allocation and block freeing with optimized throughput 
 * and memory utilization.
 * 
 * Allocated block in the heap contains a header and payload. The header 
 * indicates the block size, if prev block has only 16 bytes, if prev block
 * is allocated, and the alloc status of block.
 * 
 * Free blocks in the heap are categorized as either small blocks (16 bytes)
 * or normal blocks (> 16 bytes). Small blocks are stored in a list pointed 
 * to by small_blocks_list and contain only a header and a pointer to next 
 * small block. Normal blocks are stored in one of the thirteen free lists, 
 * each pointed to by an element in free_lists array. The first list contains 
 * blocks of size in range [2^4, 2^5). The second list contains blocks of 
 * size in range [2^5, 2^6), so on until the 12th list. The 13th list holds 
 * any block of size >= 2^16. The data sturcture of normal free blocks has
 * both header and footer, plus prev/next pointers to adjacent blocks in 
 * the free list. 
 * 
 * When allocator performs malloc, realloc or calloc, it goes through 
 * small_blocks_list and free_lists to find a free block of appropriate 
 * size using first-fit approach. When free is called, the allocator first
 * coalesces the free block with any adjacent free blocks then inserts the 
 * free block back into the start of appropriate free list.
 * 
 * Alloc block structure
 *  -----------------------------------------------------------------
 *  |Header:  block size | prev_small bit | prev_alloc bit| alloc bit|
 *  |----------------------------------------------------------------|
 *  | payload                                                        |
 *  ------------------------------------------------------------------
 * 
 * Free block (larger than 16 bytes) structure
 *   -----------------------------------------------------------------
 *  |Header:  block size | prev_small bit | prev_alloc bit| alloc bit|
 *  |----------------------------------------------------------------|
 *  | next: pointer to next free block in free_lists[n]              |
 *  |----------------------------------------------------------------|
 *  | prev: pointer to prev free block in free_lists[n]              |
 *  |----------------------------------------------------------------|
 *  |Footer:  block size | prev_small bit | prev_alloc bit| alloc bit|
 *  ------------------------------------------------------------------
 * 
 *  Small free block (16 bytes) structure
 *   -----------------------------------------------------------------
 *  |Header:  block size | prev_small bit | prev_alloc bit| alloc bit|
 *  |----------------------------------------------------------------|
 *  | next: pointer to next free block in small_block_list           |
 *  ------------------------------------------------------------------
 *                                                                            *
 ******************************************************************************
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>
#include <unistd.h>
#include <inttypes.h>

#include "mm.h"
#include "memlib.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined (such as when running mdriver-dbg), these macros
 * are enabled. You can use them to print debugging output and to check
 * contracts only in debug mode.
 *
 * Only debugging macros with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...)     printf(__VA_ARGS__)
#define dbg_requires(expr)  assert(expr)
#define dbg_assert(expr)    assert(expr)
#define dbg_ensures(expr)   assert(expr)
#define dbg_printheap(...)  print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...)     (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr)  (sizeof(expr), 1)
#define dbg_assert(expr)    (sizeof(expr), 1)
#define dbg_ensures(expr)   (sizeof(expr), 1)
#define dbg_printheap(...)  ((void) sizeof(__VA_ARGS__))
#endif

// Total number of free lists
#define FREE_LIST_SIZE 13

// Min size class is 16, 2^4
#define MIN_SIZE_CLASS 4
/* Basic constants */

typedef uint64_t word_t;

// Word and header size (bytes)
static const size_t wsize = sizeof(word_t);

// Double word size (bytes)
static const size_t dsize = 2 * wsize;

// Minimum heap extend size each time an extend request is made (byte)
static const size_t chunksize = (1 << 12);

// Mask to get block allocation status from header/footer
static const word_t alloc_mask = 0x1;

// Mask to get previous block allocation status from header/footer
static const word_t prev_alloc_mask = 0x2;

// Mask to get indication if previous block is min size (16 bytes)
static const word_t prev_small_mask = 0x4;

// Mask to get block size from header/footer
static const word_t size_mask = ~(word_t)0xF;


/* Represents the header and payload of one block in the heap */
typedef struct block
{
    /* Header contains size + prev small flag + prev alloc flag 
     * + alloc flag.
     */
    word_t header;

    /*
     * The union data_t allows both payload and next/prev pointers to be stored 
     * in the same memory area. Using union prevents the need for casting 
     * pointers.
     */
    union data_t{
    
    /*
     * The struct link_t contains two pointers to next and previous free block  
     * in free lists. For small free blocks (16 bytes), only next is used to 
     * indicate next free block in small free list.
     * 
     */
    struct link_t
    {
        struct block* next;
        struct block* prev;

    } link;
    
    // Zero-length array to store payload
    char payload[0];

    } data;

    /*
     * Footer memory location depends on payload size. When footer is 
     * needed, we add header size and payload size to the start of 
     * block address to get acutal footer location.
     */
} block_t;


/* Global variables total size = 120 bytes */

// Pointer to the first block in heap
static block_t *heap_start = NULL;

/* List of pointers to the first free blocks in each size class.
 * First size class range is [2^4, 2^5). 
 * Second size class range is [2^5, 2^6), and so on until 12th size class.
 * The last, 13th size class, holds any blocks >= 2^16.
 */ 
static block_t *free_list[FREE_LIST_SIZE];

/* 
 * Pointer to the first small block (16 bytes). All blocks in this list
 * have 16 bytes.
 */ 
static block_t *small_blocks_list = NULL;

/* Function prototypes for internal helper routines */

bool mm_checkheap(int lineno);

static block_t *extend_heap(size_t size);
static block_t *find_fit(size_t asize);
static block_t *coalesce_block(block_t *block);
static void split_block(block_t *block, size_t asize);

static void remove_block_link(block_t *block);
static void reassign_blocks_link(block_t *free, block_t *alloc);
static void insert_free_block(block_t *block);


static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_small);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static bool extract_prev_alloc(word_t header);
static bool get_prev_alloc(block_t *block);

static bool extract_prev_small(word_t header);
static bool get_prev_small(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc, bool prev_small);
static void write_footer(block_t *block, size_t size, bool alloc,bool prev_alloc, bool prev_small);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static word_t *header_to_footer(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void print_free_list();
static void print_heap();
static void print_small_list();
bool exists_in_heap(block_t* find);
static void write_next_header();

/*
 * mm_init: Initialize the heap with boundary prologue and epilogue.
 *          Also initialize the free lists.
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *) (mem_sbrk(2 * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    // Initialize prologue and epilogue which mark the heap boundary
    start[0] = pack(0, true,false,false);  // Heap prologue (block footer)
    start[1] = pack(0, true,true, false);  // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *) &(start[1]);

    // Initialize free list
    int i;
    for (i = 0; i < FREE_LIST_SIZE; i++)
    {
        free_list[i] = NULL;
    }

    // Initialize small free list
    small_blocks_list = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }

    return true;
}

/*
 * malloc: Allocate a block of given size in heap. If current heap does 
 *         not contain enough space, extend heap. Return a pointer to 
 *         payload of allocated block.
 * 
 * size: New block's size
 */
void *malloc(size_t size)
{
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {   
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_header(block, block_size, true, get_prev_alloc(block), get_prev_small(block));

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/*
 * free: Free the block pointed to by the given pointer. If null pointer
 *       is given or the block pointed to is free, just return. 
 * 
 * bp: pointer to the block to be freed
 */
void free(void *bp)
{
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));
    if (!get_alloc(block))
    {
        return;
    }

    // Mark the block as free
    write_header(block, size, false, get_prev_alloc(block), get_prev_small(block));

    if (size > dsize)
    {
        write_footer(block, size, false, get_prev_alloc(block), get_prev_small(block));
    }

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * print_free_list: print eaach block in all the free lists
 */
static void print_free_list(void)
{
    block_t *block;
    int count = 1;
    int i;
    for (i = 0; i < FREE_LIST_SIZE; i++)
    {
        block = free_list[i];
        count = 1;
        dbg_printf("Class size 2 ^ %d\n", i + 4);
        while (block != NULL)
        {
            
            dbg_printf("free block #%d %p prev %p/ next %p size %zu\n",
            count, (void *)block, (void *)block->data.link.prev, (void *)block->data.link.next, get_size(block));
            count ++;
            block = block->data.link.next;
        }
        
    }
}

/*
 * print_small_list: print eaach block in the small_block_list
 */
static void print_small_list(void)
{
    block_t *block;
    int count = 1;

    for (block = small_blocks_list; block != NULL; block = block->data.link.next)
    {
        dbg_printf("small free block #%d %p next %p\n",
            count, (void *)block, (void *)block->data.link.next);
        count ++;
    }
}

/*
 * print_heap: print eaach block in the heap
 */
static void print_heap(void)
{
    block_t *block;
    int count = 1;
    for (block = heap_start; get_size(block) > 0;
                            block = find_next(block))
    {
        dbg_printf(" block #%d %p alloc %d p_alloc %d size %zu",
        count, (void *)block, get_alloc(block), get_prev_alloc(block),get_size(block));
        if (!get_alloc(block))
        {
            dbg_printf(" prev %p/ next %p\n",(void *)block->data.link.prev, (void *)block->data.link.next);

        } 
        else {
            dbg_printf("\n");
        }

        dbg_printf("payload: %p ", header_to_payload(block));
        if (get_size(block) > dsize)
        {
            dbg_printf("footer: %p", (void*) header_to_footer(block));
        }
        dbg_printf("\n");
        count++;
    }
    
}

/*
 * realloc: Reassign the memory pointed by the given pointer. Return  
 *          a new pointer to the new allocated block with a given size.
 *          If the given size is zero or the given pointer is NULL, just
 *          return NULL.
 * 
 * ptr: pointer to original allocated memmory
 * size: desired size of the new allocated block
 */
void *realloc(void *ptr, size_t size)
{
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    block_t *block = payload_to_header(ptr);
    if (!exists_in_heap(block))
    {
        return NULL;
    }
    
    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize)
    {
        copysize = size;
    }

    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * exists_in_heap: check if a block exist in current heap
 * 
 * find: target block to find 
 */
bool exists_in_heap(block_t* find)
{
    dbg_printf("exists_in_heap\n");
    block_t* block;
    for (block = heap_start; get_size(block) > 0;
                            block = find_next(block))
    {
        if (find == block && get_alloc(block))
        {
            dbg_printf("true\n");
            return true;
        }
        
    }
    dbg_printf("false\n");
    return false;
}
/*
 * calloc: Allocate an array of a given number of element of a given
 *         size. Initialize the payload to 0 and return pointer to 
 *         payload.
 * 
 * elements: the number of element in the array
 * size: the size of each element 
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Create new free block given a size at the end of epilogue.
 *              Update epilogue position and return the newly added
 *              free block.
 * 
 * size: Size for the new free block
 */
static block_t *extend_heap(size_t size)
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Get new free block position from payload
    block_t *block = payload_to_header(bp);
    
    // Get previous block information from old epilogue, 
    // which has become the new free block's header
    bool prev_alloc = extract_prev_alloc(block->header);
    bool prev_small = extract_prev_small(block->header);

    write_header(block, size, false, prev_alloc, prev_small);
    write_footer(block, size, false, prev_alloc, prev_small);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false, (get_size(block) <= dsize));

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}


/*
 * coalesce_block: Combine a free block with its adjacent neighbors. 
 *                 Four possible cases of block arrangements include: 
 *                 (prev_alloc + next_alloc), (prev_alloc + !next_alloc),
 *                 (!prev_alloc + next_alloc), (!prev_alloc + !next_alloc).
 *                 Each case is handled differently. Return a free block  
 *                 resulting from the coalescence.
 * 
 * block: free block to be checked for coalescence
 */
static block_t *coalesce_block(block_t *block)
{
    dbg_requires(!get_alloc(block));

    size_t size = get_size(block);

    block_t *block_next = find_next(block);

    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = get_alloc(block_next);

    if (prev_alloc && next_alloc)              // Case 1
    {   
        insert_free_block(block);
        write_next_header(block);
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        remove_block_link(block_next);

        write_header(block, size, false, get_prev_alloc(block), get_prev_small(block));
        write_footer(block, size, false, get_prev_alloc(block), get_prev_small(block));

        insert_free_block(block);
        write_next_header(block);  
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_t *block_prev = find_prev(block);
         
        size += get_size(block_prev);
        remove_block_link(block_prev);
        write_header(block_prev, size, false, get_prev_alloc(block_prev),get_prev_small(block_prev));
        write_footer(block_prev, size, false, get_prev_alloc(block_prev),get_prev_small(block_prev));
        
        insert_free_block(block_prev);
        write_next_header(block_prev);
        block = block_prev;
    }

    else                                        // Case 4
    {
        block_t *block_prev = find_prev(block);

        size += get_size(block_next) + get_size(block_prev);

        remove_block_link(block_prev);
        remove_block_link(block_next);

        write_header(block_prev, size, false, get_prev_alloc(block_prev), get_prev_small(block_prev));
        write_footer(block_prev, size, false, get_prev_alloc(block_prev), get_prev_small(block_prev));

        insert_free_block(block_prev);
        write_next_header(block_prev);
        block = block_prev;
    }

    dbg_ensures(!get_alloc(block));

    return block;
}

/*
 * split_block: Split unused free space of a block into a new free block 
 *              to decrease internal fragmentation. No need to split if 
 *              unused free space is less than 16 bytes.
 *                         
 * block: newly allocated block, might be larger than needed
 * asize: minimum required size for the block
 */
static void split_block(block_t *block, size_t asize)
{
    dbg_requires(get_alloc(block));

    if (!get_alloc(block))
    {
        return;
    }

    remove_block_link(block);

    size_t block_size = get_size(block);

    // Dont split blocks with not enough space
    if ((block_size - asize) < dsize )
    {   
        write_header(block, block_size, true, get_prev_alloc(block), get_prev_small(block));
       
        write_next_header(block);
        return;
    }

    // Split block
    // Update allocated section of original block
    write_header(block, asize, true, get_prev_alloc(block), get_prev_small(block));

    // Update free section of original block
    block_t *block_next = find_next(block);
    bool prev_small = get_size(block) <= dsize;
    write_header(block_next, block_size - asize, false, true, prev_small);

    if (get_size(block_next) > dsize)
    {
        write_footer(block_next, block_size - asize, false, true, prev_small);
    }

    coalesce_block(block_next);
    dbg_ensures(get_alloc(block));
    return;
}

/*
 * remove_block_link: Remove a block from the free list it originally 
 *                    resides in. If block if small, check small_free_list
 *  
 * block: target block to be removed                  
 */
static void remove_block_link(block_t *block)
{   

    size_t block_size = get_size(block);

    // Check if block is in small_free_list
    if (block_size <= dsize)
    {
        block_t *small_prev = NULL;
        block_t *small_cur = small_blocks_list;

        for (; small_cur != NULL; small_cur = small_cur->data.link.next)
        {
            if (small_cur == block)
            {
                break;
            }
            small_prev = small_cur;
        }

        if (small_prev == NULL)
        {
             // Remove from the start
            small_blocks_list = small_blocks_list->data.link.next;
        } else
        {
            // Remove from the middle
            small_prev->data.link.next = small_cur->data.link.next;
        }
        return;
    }

    block_t *prev_node = block->data.link.prev;
    block_t *next_node = block->data.link.next;
    int i;

    // Find the correct size class
    for (i = 0; i < FREE_LIST_SIZE; i ++)
    {
        // Already reach the last size class 
        // Block must belong here
        if (i == FREE_LIST_SIZE - 1)
        {
          break;      
        } 

        // Check if a block falls into the current size class  
        if ((block_size >= (1L << (i + MIN_SIZE_CLASS))) 
                && (block_size < (1L << (i + (MIN_SIZE_CLASS + 1)))))
        {
            break;
        }
        
    }

    // Removing from one single list
    if (prev_node == NULL && next_node == NULL)
    {
        free_list[i] = NULL;
    } 
    // Removing from start
    else if (prev_node == NULL && next_node != NULL)
    {
        next_node->data.link.prev = NULL;
        free_list[i] = next_node;
    }
    // Removing from middle
    else if (prev_node != NULL && next_node != NULL)
    {
        prev_node->data.link.next = next_node;
        next_node->data.link.prev = prev_node;
    }
    // Removing from end
    else 
    {
        prev_node->data.link.next = NULL;
    }
    return;
}

/*
 * insert_free_block: Insert a block into the start of the correct free list.
 *                    If the block is small, insert into small_free_list
 *  
 * block: target block to be inserted                  
 */
static void insert_free_block(block_t *block)
{   

    size_t block_size = get_size(block);
    int i;

    if (block_size <= dsize)
    {
        block->data.link.next = small_blocks_list;
        small_blocks_list = block;
        return;
    }

    // Find the correct size class
    for (i = 0; i < FREE_LIST_SIZE; i ++)
    {
        // Already reach the last size class
        // Block must belong here
        if (i == FREE_LIST_SIZE - 1)
        {
          break;      
        } 

        // Check if a block falls into the current size class  
        if ((block_size >= (1L << (i + MIN_SIZE_CLASS))) 
                && (block_size < (1L << (i + (MIN_SIZE_CLASS + 1)))))
        {
            break;
        }
        
    }

    // If list is empty, insert into empty list
    if (free_list[i] == NULL)
    {
        block->data.link.prev = NULL;
        block->data.link.next = NULL;
        free_list[i] = block;
        return;
    } 

    
    block_t *block_target = free_list[i];
    block_t *prev = NULL;
   
    if (prev == NULL && block_target != NULL)
    { 
        // Insert into start
        block->data.link.prev = NULL;
        block->data.link.next = block_target;
        block_target->data.link.prev = block;
        free_list[i] = block;
    }   

    return;
}

/*
 * find_fit: Look for free block in small_free_list if size is 16 bytes. 
 *           For larger size, start from free list of closest size class 
 *           and iterate through all free lists to get an appropriate one. 
 *           Return the found block or null
 * 
 * asize: The size that we need
 */
static block_t *find_fit(size_t asize)
{
    int i;

    // Use small block if asize fits
    // Use free_list blocks if small_blocks_list is empty
    if (asize <= dsize)
    {
        if (small_blocks_list != NULL)
        {
            return small_blocks_list;
        }
    }

    // Find the starting size class
    for (i = 0; i < FREE_LIST_SIZE; i ++)
    {
        if (i == FREE_LIST_SIZE -1)
        {
          break;      
        } 
        if ((asize >= (1L << (i + MIN_SIZE_CLASS))) 
                && (asize < (1L << (i + (MIN_SIZE_CLASS + 1)))))
        {
            break;
        }
        
    }
    block_t *block;

    // Look for 
    for (; i < FREE_LIST_SIZE; i ++)
    {
        block = free_list[i];
        while (block != NULL)
        {
            size_t block_size = get_size(block);
            if (block_size >= asize)
            {
                return block;
            }

            block = block->data.link.next;
        }
    
    }

    return NULL; // no fit found
}

/*
 * mm_checkheap: Check heap integrity after major operations
 *               Ensure blocks in heap, small_free_lsit and free_list 
 *               are correct. Return false if heap contains error,
 *               true if none.
 * 
 * line: from where the heap checker is called
 */
bool mm_checkheap(int line)
{   
    // Check prologue is created with correct flags
    word_t *prologue = find_prev_footer(heap_start);
    bool is_free = (extract_alloc(*prologue) == false);
    bool has_size = (extract_size(*prologue) == true);
    bool is_small = (extract_prev_small(*prologue) == true);
    bool is_prev_alloc = (extract_prev_alloc(*prologue) == true);
    if (is_free || has_size || is_small || is_prev_alloc) 
    {
        dbg_printf("Prologue is not properly created\n");
        return false;
    }

    block_t *block;
    int free_block_count = 0;
    bool prev_free = !get_alloc(heap_start);
    bool prev_alloc = extract_alloc(*prologue);
    bool prev_small = false;

    for (block = heap_start; get_size(block) > 0;
                            block = find_next(block))
    {
        // Check header stores correct size
        size_t payload_size = get_payload_size(block);
        if ((payload_size + wsize) != get_size(block))
        {
            dbg_printf("Size is inconsistent\n");
            dbg_printf("get_size %zu != (payload %zu + header %zu)", 
                    get_size(block), payload_size, wsize);
            return false;
        }

        // Check prev small status matches previous block
        if (prev_small != get_prev_small(block))
        {
            dbg_printf("Prev small doesnt match \n");
            dbg_printf("Expect %d get %d \n", prev_small, get_prev_small(block));
            return false;
        }
        prev_small = get_size(block) <= dsize;

        // Check prev alloc status matches previous block
        bool status = get_prev_alloc(block); 
        if (status != prev_alloc)
        {
            dbg_printf("Prev alloc status doesnt match\n");
            dbg_printf("Expect %d get %d \n", prev_alloc, status);
            return false;
        }

        prev_alloc = get_alloc(block);

        // Check payload alignment
        unsigned long payload_addr = (unsigned long) &(block->data.payload);
        if(( payload_addr & 0xFUL) != 0) 
        {
            dbg_printf("Payload not aligned \n");
            dbg_printf("Payload addr %p\n", (void *)&(block->data.payload));
            return false;
        }

        // Check block size
        if ((get_size(block)) % 16 != 0)
        {
            dbg_printf("Block is not multiple of 16\n");
            dbg_printf("Block size %zu\n", get_size(block));
            return false;
        }

        // Check coalescing
        if ((prev_free || get_alloc(block)) == 0) 
        {
            dbg_printf("Two consecutive free blocks\n");
            return false;
        }

        // increment if free block
        if (!get_alloc(block)) 
        {
            free_block_count += 1;
        }

        prev_free = get_alloc(block);

    }

    // Check epilogue prev status is correct
    if (prev_alloc != extract_prev_alloc(block->header))
    {
        dbg_printf("Epilogue prev status is wrong\n");
        dbg_printf("Expect %d get %d \n", prev_alloc, extract_prev_alloc(block->header));
        return false;
    }

    // Check epilogue is allocated with size 0
    if (!extract_alloc(block->header) || extract_size(block->header))
    {
        dbg_printf("Epilogue is not properly created\n");
        return false;
    }

    // Check small_block_lists 
    for (block = small_blocks_list; block != NULL; block = block->data.link.next)
    {   
        free_block_count -= 1;
        // All blocks have the same size
        if (get_size(block) != dsize)
        {
            dbg_printf("small blocks list not all dsize\n");
            return false;
        }

        // All blocks are free
        if (get_alloc(block))
        {
            dbg_printf("small blocks list contains allocated block\n");
            return false;
        }

        size_t payload_size = get_payload_size(block);
        if ((payload_size + wsize) != get_size(block))
        {
            dbg_printf("Size for small block is inconsistent\n");
            dbg_printf("get_size %zu != (payload %zu + header %zu)", 
                    get_size(block), payload_size, wsize);
            return false;
        }
    }

    // Check free_lists
    int i;
    for (i = 0; i < FREE_LIST_SIZE; i ++)
    {
        block_t *block = free_list[i];
        while (block != NULL)
        {
            free_block_count -= 1;

            // Check header footer match for free list block
            bool same_size = (extract_size(block->header) 
            == extract_size(*(header_to_footer(block))));

            bool same_alloc_status = (extract_alloc(block->header) 
            == extract_alloc(*(header_to_footer(block))));

            bool same_prev_alloc = (extract_prev_alloc(block->header)
            == extract_prev_alloc(*(header_to_footer(block))));

            bool same_prev_small = (extract_prev_small(block->header)
            == extract_prev_small(*(header_to_footer(block))));
        
            if (!same_size || !same_alloc_status || !same_prev_alloc || !same_prev_small)
            {
                dbg_printf("Header and footer do not match\n");
                dbg_printf("Header size %zu, alloc %d, prev alloc %d, prev small %d\n",
                    extract_size(block->header), 
                    extract_alloc(block->header),
                    extract_prev_alloc(block->header),
                    extract_prev_small(block->header));
                dbg_printf("Footer size %zu, alloc %d, prev alloc %d, prev small %d\n", 
                    extract_size(*(header_to_footer(block))), 
                    extract_alloc(*(header_to_footer(block))),
                    extract_prev_alloc(*(header_to_footer(block))),
                    extract_prev_small(*(header_to_footer(block))));
                
                return false;
            }

            // Check memory bound
            if((void *)(mem_heap_lo()) > (void *)(block) || (void *)(mem_heap_hi()) < (void *)(block))
            {
                dbg_printf("Free block outside of boundary\n");
                return false;
            }

            // Check size class
            size_t bsize = get_size(block);
            if (i == (FREE_LIST_SIZE -1)) 
            {
                if (bsize < (1L << (i + 4)))
                {
                    dbg_printf("Free block in wrong size class\n");
                    dbg_printf("Block size = %zu in largest size class %lu\n", bsize, (1L << (i +4)) );
                    return false;
                }
                
            } else if ((bsize < (1L << (i + 4))) || (bsize >= (1L << (i + 5))))
            {
                dbg_printf("Free block in wrong size class\n");
                dbg_printf("Block size = %zu in size class %lu\n", bsize, (1L << (i +4)) );
                return false;
            }

            // Check pointer consistency
            block_t *node_next = block->data.link.next;
            if (node_next == NULL) 
            {   
                break;
            }

            if (node_next->data.link.prev != block)
            {
                dbg_printf("Prev and next pointers not consistent\n");
                return false;
            }   

           block = node_next;

        }
    }
    
    // Check free_list size + small_free_list = total free blocks in heap
    if (free_block_count != 0)
    {
        dbg_printf("Free list count and heap's free blocks do not match\n");
        print_heap();
        print_free_list();
        print_small_list();
        return false;
    }

    return true;
}



/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ba c1 e1 52 13 0a               *
 *                                                                           *
 *****************************************************************************
 */


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 * 
 */
static size_t round_up(size_t size, size_t n)
{
    return n * ((size + (n-1)) / n);
}

/*
 * pack: returns a header reflecting a specified size , its alloc status, 
 *       previous block's alloc status and previous block's small size status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 *       If the previous block is alloc, the second lowest bit is 1, 0 otherwise.
 *       If the previous block is small, the third lowest bit is 1, 0 otherwise.
 * 
 * size: size of the block
 * alloc: block's allocation flag
 * prev_alloc: previous block's allocation flag
 * prev_small: flag to show if previous block is small 
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_small)
{
    
    if (alloc)
    {
        size = size | alloc_mask;
    } 

    if (prev_alloc) 
    {
        size = size | prev_alloc_mask;
    }
    
    if (prev_small)
    {
        size = size | prev_small_mask;
    }

    return size;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 * 
 * word: find the size here
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 * 
 * block: find its size
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 *                   If block has no footer, minus just the header size.
 * 
 * block: find its payload size
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);

    // Alloc block has no footer
    if (get_alloc(block))
    {
        return asize - wsize;
    }
    
    // Small free block has no footer
    return asize <= dsize ? asize - wsize : asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 * 
 * word: extract bit from here
 */
static bool extract_alloc(word_t word)
{
    return (bool) (word & alloc_mask);
}


/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 * 
 * block: extract bit from its header
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * extract_prev_alloc: returns true when previous block is allocated based
 *                     on the second lowest bit, false if otherwise.
 * 
 * word: extract bit from here
 */
static bool extract_prev_alloc(word_t word)
{
    return (bool) (word & prev_alloc_mask);
}


/*
 * get_prev_alloc: returns true when previous block is allocated based
 *                 on the block header's second lowest bit, fales if otherwise
 * 
 * block: extract bit from its header
 */
static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}

/*
 * extract_prev_small: returns true when previous block is allocated based
 *                     on the third lowest bit, false if otherwise.
 * 
 * word: extract bit from here
 */
static bool extract_prev_small(word_t header)
{
    return (bool) (header & prev_small_mask);
}

/*
 * get_prev_small: returns true when previous block is allocated based
 *                 on the block header's third lowest bit, false if otherwise.
 * 
 * block: extract bit from its header
 */
static bool get_prev_small(block_t *block)
{
    return extract_prev_small(block->header);
}

/*
 * write_footer: given a block, its size, allocation status, alloc status of
 *               previous block and small size indication of previous block,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer. If block is null or
 *               the size from header and parameter doesn't match, just return.
 * 
 * block: block to write footer to
 * size: size of the block
 * alloc: block's allocation flag
 * prev_alloc: previous block's allocation flag
 * prev_small: flag to show if previous block is small 
 */
static void write_footer(block_t *block, size_t size, bool alloc, bool prev_alloc, bool prev_small)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) == size && size > 0);

    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc,prev_alloc, prev_small);
}

/*
 * write_header: given a block, its size, allocation status, alloc status of
 *               previous block and small size indication of previous block,
 *               writes an appropriate value to the block header.
 *               If block is null, just return.
 * 
 * block: block to write footer to
 * size: size of the block
 * alloc: block's allocation flag
 * prev_alloc: previous block's allocation flag
 * prev_small: flag to show if previous block is small 
 */
static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc, bool prev_small)
{
    dbg_requires(block != NULL);
    block->header = pack(size, alloc, prev_alloc, prev_small);
}

/*
 * write_next_header: update header value in the next block based on 
 *                    header value of the given block.
 * 
 * block: use this block to get next block and header value
 */
static void write_next_header(block_t *block)
{
    block_t *block_next = find_next(block);
    bool prev_alloc = get_alloc(block);
    bool alloc = get_alloc(block_next);
    bool prev_small = (get_size(block) <= dsize);

    write_header(block_next, 
                    get_size(block_next),
                    alloc,
                    prev_alloc,
                    prev_small);
    
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 * 
 * block: use this block to get next block
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    return (block_t *) ((char *) block + get_size(block));
}


/*
 * find_prev_footer: returns the footer of the previous block.
 * 
 * block: find previous footer from this block
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}


/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size. If no footer exists because previous block
 *            is small, just subtract 16 bytes to get correct location
 * 
 * block: use this to find previous block
 */
static block_t *find_prev(block_t *block)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);

    // Small blocks case
    if (get_prev_small(block))
    {
        return (block_t *) ((char *) block - dsize);
    }

    // Other blocks
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *) ((char *) block - size);
}


/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 * 
 * bp: pointer to payload
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *) ((char *) bp - offsetof(block_t, data.payload));
}


/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 * 
 * block: find payload of this block
 */
static void *header_to_payload(block_t *block)
{   
    return (void *) (block->data.payload);
}


/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer.
 * 
 * block: find footer of this block
 */
static word_t *header_to_footer(block_t *block)
{
    return (word_t *) (block->data.payload + get_size(block) - dsize);
}
