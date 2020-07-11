/*
 ******************************************************************************
 *                                   mm.c                                     *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                  TODO: insert your documentation here. :)                  *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
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

// Minimum block size (bytes)
// static const size_t min_block_size = 2 * dsize;

// TODO: explain what chunksize is
// (Must be divisible by dsize)
static const size_t chunksize = (1 << 12);

// TODO: explain what alloc_mask is
static const word_t alloc_mask = 0x1;

static const word_t prev_alloc_mask = 0x2;

static const word_t prev_small_mask = 0x4;

// TODO: explain what size_mask is
static const word_t size_mask = ~(word_t)0xF;


/* Represents the header and payload of one block in the heap */
typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;

    /*
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GCC compiler extension. This will
     * allow us to obtain a pointer to the start of the payload.
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    union data_t{

    struct link_t
    {
        struct block* prev;
        struct block* next;
    } link;
    
   
  
    char payload[0];

    } data;

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Why can't we declare the block footer here as part of the struct?
     * Why do we even have footers -- will the code work fine without them?
     * which functions actually use the data contained in footers?
     */
} block_t;


/* Global variables */

// Pointer to first block
static block_t *heap_start = NULL;
static block_t *free_list[FREE_LIST_SIZE];
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
// static word_t pack(size_t size, bool alloc);
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

// static void write_header(block_t *block, size_t size, bool alloc);
static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc, bool prev_small);
// static void write_footer(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc,bool prev_alloc, bool prev_small);
static void write_link(block_t *block, block_t *prev, block_t *next);

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
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *) (mem_sbrk(2 * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

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

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }

    return true;
}


/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
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
    // TODO change to only contain header
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {   
        // dbg_printf("calling extend_heap in malloc\n");
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
    // write_footer(block, block_size, true);

    // Try to split the block if too large
    split_block(block, asize);

    // dbg_printf("split in malloc complete\n");
    bp = header_to_payload(block);
    // dbg_printf("done get payload\n");
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}


/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
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
    // insert_free_block(block);
    block = coalesce_block(block);
    dbg_ensures(mm_checkheap(__LINE__));
}

static void print_free_list()
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

static void print_small_list()
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

static void print_heap()
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

        count++;
    }
    
}


/*
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
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
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
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
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
static block_t *extend_heap(size_t size)
{
    // dbg_printf("extend_heap\n");
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about what bp represents. Why do we write the new block
     * starting one word BEFORE bp, but with the same size that we
     * originally requested?
     */

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    
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
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
static block_t *coalesce_block(block_t *block)
{
    dbg_requires(!get_alloc(block));

    size_t size = get_size(block);

    block_t *block_next = find_next(block);
    // block_t *block_prev = find_prev(block);

    // bool prev_alloc = extract_alloc(*find_prev_footer(block));
    bool prev_alloc = get_prev_alloc(block);

    bool next_alloc = get_alloc(block_next);

    if (prev_alloc && next_alloc)              // Case 1
    {   
        dbg_printf("Case 1\n");
        
        insert_free_block(block);
        write_next_header(block);
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        dbg_printf("Case 2\n");

        size += get_size(block_next);
        remove_block_link(block_next);

        write_header(block, size, false, get_prev_alloc(block), get_prev_small(block));
        write_footer(block, size, false, get_prev_alloc(block), get_prev_small(block));

        insert_free_block(block);
        write_next_header(block);  
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        dbg_printf("Case 3\n");

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
        dbg_printf("Case 4\n");
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
 * split_block: Split unused free space of a block 
 *              into a new free block to decrease 
 *              internal fragmentation. No need to
 *              split if unused free space is less 
 *              than min_block_size. 
 *                
 * block: newly allocated block, might be larger
 *        than needed
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
    if ((block_size - asize) < dsize )
    {   
        // No need to split, just update header/footer
        write_header(block, block_size, true, get_prev_alloc(block), get_prev_small(block));
        // write_footer(block, block_size, true);
        write_next_header(block);
        return;
    }

    write_header(block, asize, true, get_prev_alloc(block), get_prev_small(block));
    // write_footer(block, asize, true);

    block_t *block_next = find_next(block);
    bool prev_small = get_size(block) <= dsize;
    write_header(block_next, block_size - asize, false, true, prev_small);
    write_footer(block_next, block_size - asize, false, true, prev_small);

    coalesce_block(block_next);
    dbg_ensures(get_alloc(block));
    return;
}

/*
 * remove_block_link: Remove a block from the free list it
 *                    originally resides in
 *  
 * block: target block to be removed                  
 */
static void remove_block_link(block_t *block)
{   

    size_t block_size = get_size(block);

    // Check removing from small_blocks_list
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
            small_blocks_list = small_blocks_list->data.link.next;
        } else
        {
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
 * insert_free_block: Insert a block into the start of 
 *                    the correct free list
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
    // for (; block_target != NULL;
    //         block_target = block_target->data.link.next)
    // {
    //     size_t target = get_size(block_target);
    //     if (block_size <= target)
    //     {
    //         break;
    //     }
    //     prev = block_target;
    // }      
    
    if (prev == NULL && block_target != NULL)
    { 
        // Insert into start
        block->data.link.prev = NULL;
        block->data.link.next = block_target;
        block_target->data.link.prev = block;
        free_list[i] = block;
    }   
    // // Insert into middle
    // else if (prev != NULL && block_target != NULL)
    // {   
    //      if (find_next(block) == block_target) 
    //     {
    //         dbg_printf("adjacent block %p target %p", (void *)block, (void *) block_target);
    //     }
    //     prev->data.link.next = block;
    //     block_target->data.link.prev = block;
    //     block->data.link.prev = prev;
    //     block->data.link.next = block_target;
    // }
    // else if (prev != NULL && block_target == NULL)
    // {   
    //      if (find_next(block) == block_target) 
    //     {
    //         dbg_printf("adjacent block %p target %p", (void *)block, (void *) block_target);
    //     }
    //     prev->data.link.next = block;
    //     block->data.link.prev = prev;
    //     block->data.link.next = NULL;
    // }
    
        
    
    return;
}

/*
 * <What does this function do?>
 * find_fit: Look for free block starting from free list
 *           of closest size class. Iterate through all 
 *           free lists to check. Return an appropriate
 *           block or null
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
            block_t *block = small_blocks_list;
            small_blocks_list = small_blocks_list->data.link.next;
            return block;
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
 *               Ensure block,list and heap level are correct.
 *               Return false if find an error, true if none
 */
bool mm_checkheap(int line)
{   
    // Check prologue is allocated with size 0
    word_t *prologue = find_prev_footer(heap_start);
    if (!extract_alloc(*prologue) || extract_size(*prologue)) 
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

    }

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
    
    // Check free_list size and total free blocks in heap
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
 */
static size_t round_up(size_t size, size_t n)
{
    return n * ((size + (n-1)) / n);
}


/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
// static word_t pack(size_t size, bool alloc)
// {
//     return alloc ? (size | alloc_mask) : size;
// }

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
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}


/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}


/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}


/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool) (word & alloc_mask);
}


/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

static bool extract_prev_alloc(word_t word)
{
    return (bool) (word & prev_alloc_mask);
}

static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}


static bool extract_prev_small(word_t header)
{
    return (bool) (header & prev_small_mask);
}

static bool get_prev_small(block_t *block)
{
    return extract_prev_small(block->header);
}
/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 * TODO: Are there any preconditions or postconditions?
 */
// static void write_header(block_t *block, size_t size, bool alloc)
// {
//     dbg_requires(block != NULL);
//     block->header = pack(size, alloc);
// }


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 * TODO: Are there any preconditions or postconditions?
 */
// static void write_footer(block_t *block, size_t size, bool alloc)
// {
//     dbg_requires(block != NULL);
//     dbg_requires(get_size(block) == size && size > 0);
//     word_t *footerp = header_to_footer(block);
//     *footerp = pack(size, alloc);
// }

static void write_footer(block_t *block, size_t size, bool alloc, bool prev_alloc, bool prev_small)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) == size && size > 0);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc,prev_alloc, prev_small);
}

static void write_link(block_t *block, block_t *prev, block_t *next)
{
    dbg_requires(block != NULL);
    // block->data.link.prev = prev;
    // block->data.link.next = next;
}

static void write_header(block_t *block, size_t size, bool alloc, bool prev_alloc, bool prev_small)
{
    dbg_requires(block != NULL);
    block->header = pack(size, alloc, prev_alloc, prev_small);
}

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
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    return (block_t *) ((char *) block + get_size(block));
}


/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}


/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);

    if (get_prev_small(block))
    {
        return (block_t *) ((char *) block - dsize);
    }


    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *) ((char *) block - size);
}


/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *) ((char *) bp - offsetof(block_t, data.payload));
}


/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{   
    // dbg_printf("getting payload");
    return (void *) (block->data.payload);
}


/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer.
 */
static word_t *header_to_footer(block_t *block)
{
    return (word_t *) (block->data.payload + get_size(block) - dsize);
}
