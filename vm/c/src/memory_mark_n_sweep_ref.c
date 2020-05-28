#include <assert.h>
#include <stdalign.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "engine.h"
#include "fail.h"
#include "memory.h"

/* for compatibility with non-clang compilers */
#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

/* a simple bit array structure ******************************************************************/
typedef struct {
  size_t size;
  value_t *bits; // the bit array data; points to a region of the memory allocated for the program
} bitarray_t;

/* contains the bitmap size and address (bitmap is embedded into the heap) */
static bitarray_t bitmap = {0, NULL};

/* The bits per cell in the bit array */
static const unsigned cell_bits = sizeof(*bitmap.bits) * CHAR_BIT;
/* log2(cell_bits) - used for fast division when finding the appropriate cell of the bitmap */
static value_t log2_cell_bits; // initialized in the memory_setup function

/* base-2 log of a power of 2 */
#if __has_builtin(__builtin_ctz)
#define log2_p2(x) (__builtin_ctz(x))
#else
/**
 * Counts trailing zeroes **of a power of 2**.
 * If b is not a power of 2, then the behaviour is undefined.
 *
 * Defined in case there is no built-in to count trailing zeroes (unlikely).
 * Used only once, so inefficiency not a real problem.
 */
static unsigned myctz(unsigned b) {
  unsigned n = 0;
  while ((b >>= 1) && ++n)
    ;
  return n;
}
#define log2_p2(x) (myctz(x))
#endif

/* macros to divide x (which is 32 or 64 bits; pick accordingly) by 2^k */
#define div32_p2(x, k) (((x) + (((x) >> 31) & ((1 << (k)) - 1))) >> (k))
#define div64_p2(x, k) (((x) + (((x) >> 63) & ((1 << (k)) - 1))) >> (k))

/* macro to divide x by n, where n is a power of 2 */
#define mod_p2(x, n) ((x) & ((n)-1))

/* macros to help with bit array operations */
#define cell(idx) (div32_p2((idx), log2_cell_bits))
#define set_mask(idx) (1u << mod_p2(idx, cell_bits))
#define clear_mask(idx) (~(set_mask(idx)))

/* macro to swap the values of two variables */
#define swap(x, y) (((x) ^= (y)), ((y) ^= (x)), ((x) ^= (y)))

/* min, max */
#define min(a, b) ((a) < (b) ? (a) : (b))
#define max(a, b) ((a) > (b) ? (a) : (b))

// Initializes the bit array size and pointer, as well as the log2(cell_bits) quantity.
static void bitarray_init(size_t size, value_t *base) {
  bitmap.size = size;
  bitmap.bits = base;
  log2_cell_bits = log2_p2(cell_bits); // used for quick division, see div32_p2 macro above
}

/* bit array operations */
#define bitarray_set(idx) (bitmap.bits[cell(idx)] |= set_mask(idx))
#define bitarray_clear(idx) (bitmap.bits[cell(idx)] &= clear_mask(idx))
#define bitarray_test(idx) (bitmap.bits[cell(idx)] & set_mask(idx))

/* garbage collector starts here *****************************************************************/
static value_t *memory_start = NULL; // points to VM memory start
static value_t *heap_start = NULL;   // points to the VM heap start
static value_t *memory_end = NULL;   // points to the VM memory end

#define HEADER_SIZE 1
#define NUM_FREE_LISTS 32

/**
 * Segregated lists of free blocks. List at index `i` only contains blocks of size `i+1`,
 * for each `i` in [0, NUM_FREE_LISTS-2]. The list at the last index contains all other blocks.
 *
 * Lists always point to allocated heap via virtual pointers.
 * A list is empty if and only if it points to virtual address 0.
 */
static value_t free_lists[NUM_FREE_LISTS] = {0}; // initialize NUM_FREE_LISTS empty free lists

/* virtual -> physical address translation */
static void *addr_v_to_p(value_t v_addr) {
  return (char *)memory_start + v_addr;
}

/* physical -> virtual address translation */
static value_t addr_p_to_v(void *p_addr) {
  assert(memory_start <= p_addr && p_addr <= memory_end);
  return (value_t)((char *)p_addr - (char *)memory_start);
}

/* Header management */
static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8u) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8u;
}

char *memory_get_identity() {
  return "Mark-n-Sweep GC";
}

/* Allocates the VM memory and sets the start, end pointers */
void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = memory_start + (total_byte_size / sizeof(value_t));
}

/* Cleans up the VM memory; should be called before exiting the VM */
void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);
  memory_start = heap_start = memory_end = NULL;
}

/* Returns a pointer to the VM memory start */
void *memory_get_start() {
  return memory_start;
}

/* Returns a pointer to the VM memory end */
void *memory_get_end() {
  return memory_end;
}

/* Prints the heap to stdout - useful for debugging */
static void print_heap(unsigned cells_per_row) {
  size_t heap_size = memory_end - memory_start;
  for (size_t p = 0; p != heap_size; ++p) {
    if (!(p % cells_per_row))
      printf("\n%#010lx:", p * sizeof(value_t));
    printf(" %#010x", memory_start[p]);
  }
}

#define calc_bitmap_size(hs) ((hs)&31 ? ((hs) >> 5) + 1 : (hs) >> 5)
/**
 * Called to set the heap start. This is necessary because the loaded code occupies memory
 * in the virtual address space allocated by the VM. Therefore, the heap memory block will
 * start after the loaded code block.
 *
 * This method should be called with a pointer pointing past the end of the loaded code.
 *
 * This function also embeds the bitmap, therefore the actual heap will start some bytes
 * after the end of the memory block containing the code.
 */
void memory_set_heap_start(void *indicated_heap_start) {
  assert(heap_start == NULL);
  size_t total_heap_size = (char *)memory_end - (char *)indicated_heap_start;

  // make sure total heap size is not negative
  assert(!(total_heap_size >> ((sizeof(size_t) * CHAR_BIT) - 1)));
  size_t bitmap_size, heap_size_left = total_heap_size;

  do { // calculate the bitmap size and the remaining heap size
    bitmap_size = calc_bitmap_size(heap_size_left);
    heap_size_left = total_heap_size - bitmap_size;
  } while (calc_bitmap_size(heap_size_left) != bitmap_size);

  // initialize the bitmap
  bitarray_init(bitmap_size, indicated_heap_start);
  // 'align' to multiple of alignof(value_t)
  bitmap_size += alignof(value_t) - (bitmap_size & (alignof(value_t) - 1));

  // set the heap start, usable for allocation requests
  heap_start = (value_t *)((char *)indicated_heap_start + bitmap_size);
  // write the header of the initial block (tag_None means the block is unallocated)
  *heap_start = header_pack(tag_None, (value_t)(memory_end - heap_start) - HEADER_SIZE);

  // initialize the free lists with just one element: the whole memory block
  long fls = min(NUM_FREE_LISTS - 1, memory_end - heap_start - 1);
  free_lists[fls] = addr_p_to_v(heap_start);
}

/**
 * Splitting of blocks during allocation.
 *
 * If the block pointed to by `blockp` has size larger than `size`,
 * then the former is split into two blocks. The result is that the first block is
 * the one pointed to by `blockp`, only trimmed to `size`, and the remaining space
 * creates another block, which is added to the appropriate free list.
 */
static void split_block(value_t *blockp, value_t size) {
  value_t block_size = header_unpack_size(*blockp);
  if (block_size == size)
    return; // block has exactly the requested size, nothing to do

  // block is bigger than requested size, we have to split it
  const value_t rem_size = block_size - size - HEADER_SIZE; // calculate remaining size
  value_t *sblock = blockp + (size + HEADER_SIZE);          // get a pointer to the split block
  *sblock = header_pack(tag_None, rem_size);                 // write header

  // add split block to the appropriate free list
  const value_t fls = min(NUM_FREE_LISTS - 1, rem_size - 1);
  sblock[1] = free_lists[fls];           // point to existing first block of `flist`
  free_lists[fls] = addr_p_to_v(sblock); // insert at start of `flist`
}

static value_t *get_free_block(const value_t size) {
  // iterate over the free lists, until we find a free block of at least `size`
  // except for blocks with size equal to `size + 1` (as these blocks are unsplittable)
  for (value_t i = size - 1; i < NUM_FREE_LISTS; ++i)
    if (i != size && free_lists[i]) {                // if the list is not empty
      value_t *blockp = addr_v_to_p(free_lists[i]); // get first block in the list
      free_lists[i] = blockp[HEADER_SIZE];           // advance list pointer
      split_block(blockp, size);                     // split the block, if necessary
      return blockp;
    }

  // still no block found, we need to look for one in the "rest" free list
  value_t *previous = &free_lists[NUM_FREE_LISTS - 1];
  value_t *blockp = addr_v_to_p(free_lists[NUM_FREE_LISTS - 1]);
  while (blockp != memory_start) {
    value_t block_size = header_unpack_size(*blockp);
    if (block_size == size || block_size > size + 1) { // found an appropriate block
      *previous = blockp[HEADER_SIZE];                 // link previous list node with next one
      split_block(blockp, size);                       // split the block, if necessary
      return blockp;
    }
    previous = &blockp[HEADER_SIZE];
    blockp = addr_v_to_p(blockp[HEADER_SIZE]);
  }

  return memory_start; // no appropriate block was found
}

#define is_allocated_block(va)                                                                     \
  (heap_start < (va) && (va) < memory_end && bitarray_test((va)-heap_start - HEADER_SIZE))

static void mark_rec(value_t *addr) {
  if (!addr_p_to_v(addr))
    return;

  bitarray_clear(addr - heap_start - HEADER_SIZE); // mark the current block

  value_t s = header_unpack_size(addr[-1]); // get size of this block
  for (value_t i = 0; i != s; ++i) {        // for each block element
    if (addr[i] & 0b11)
      continue; // if element cannot be a pointer, go to next
    value_t *blockp = (value_t *)addr_v_to_p(addr[i]);
    if (is_allocated_block(blockp)) // this element points to a heap allocated block
      mark_rec(blockp);             // recursively mark the block it points to
  }
}

/**
 * Marking phase.
 *
 * The L3 VM has four base registers:
 *   - PC: the program counter; we don't bother with this register for garbage collection
 *   - Ib: the input base register; a function gets its parameters through these registers
 *   - Lb: the local base register; a function stores its local variables to these registers
 *   - Ob: the output base register; a function uses these registers to pass call parameters
 *
 * For garbage collection, we need to traverse the graph formed by the interconnection
 * (via pointers) of the input, local and output blocks, marking all reachable blocks
 * while we do so.
 */
static void mark() {
  value_t *reg = NULL;

  reg = engine_get_Ob();
  mark_rec(reg); // recursively mark block pointed to by Ob

  reg = engine_get_Lb();
  mark_rec(reg); // recursively mark block pointed to by Lb

  reg = engine_get_Ib();
  mark_rec(reg); // recursively mark block pointed to by Ib
}

// Coalesce the memory region from start until end into a continuous memory block.
static void coalesce(value_t *start, const value_t *end) {
  if (start == end)
    return; // region size is 0, nothing to do

  value_t fsize = (value_t)(end - start) - HEADER_SIZE;
  *start = header_pack(tag_None, fsize); // write header
  // insert coalesced free block to free list
  value_t fls = min(NUM_FREE_LISTS - 1, fsize - 1);
  start[HEADER_SIZE] = free_lists[fls];
  free_lists[fls] = addr_p_to_v(start);
}

/**
 * Sweep phase.
 *
 * Sweeps the memory, by reclaiming the unreachable blocks and coalescing
 * any consecutive free blocks into bigger ones.
 */
static void sweep() {
  // clear the free list (will populate it from scratch)
  memset(free_lists, 0, sizeof(free_lists));

  // perform sweeping
  value_t *swp = heap_start;                  // sweeping pointer
  value_t *free_start = swp;                  // current free space start virtual pointer
  while (swp != memory_end) {                  // go through the heap sequentially
    const tag_t tag = header_unpack_tag(*swp); // extract current block tag
    value_t size = header_unpack_size(*swp);  // extract current block size
    size += (size == 0);                       // smallest block we allocate is of size 1

    if (bitarray_test(swp - heap_start) || (!bitarray_test(swp - heap_start) && tag == tag_None)) {
      // block is unreachable or unallocated
      bitarray_clear(swp - heap_start); // clear bitmap entry, as this block is now unallocated
      swp += (size + HEADER_SIZE);      // advance sweeping pointer
      continue;
    }

    // block is reachable
    coalesce(free_start, swp);      // coalesce blocks between `free_start` and `free_limit`
    bitarray_set(swp - heap_start); // reset the bitmap entry
    swp += (size + HEADER_SIZE);    // advance sweeping pointer
    free_start = swp;
  }

  // coalesce the last free block, if any
  coalesce(free_start, swp);
}

static void garbage_collect() {
  mark();  // mark reachable blocks
  sweep(); // sweep unreachable blocks
}

/* out of memory if block == NULL (in virtual address terms) */
#define out_of_memory(blockp) ((blockp) == memory_start)
/**
 * Serves a block allocation request for the given tag and size.
 * Triggers garbage collection if no block is found to satisfy the request.
 *
 * Returns a pointer to the allocated block.
 */
value_t *memory_allocate(tag_t tag, value_t size) {
  assert(heap_start != NULL);

  value_t real_size = size + (size == 0);
  value_t *blockp = get_free_block(real_size);

  if (out_of_memory(blockp)) {          // no block of the requested size was found
    garbage_collect();                  // trigger garbage collection
    blockp = get_free_block(real_size); // try again
    if (out_of_memory(blockp))          // still no block can be found, fail
      fail("no memory left (block of size %u requested)", size);
  }

  *blockp = header_pack(tag, size);                              // write block header
  memset(blockp + HEADER_SIZE, 0, real_size * sizeof(value_t)); // clear block before returning it
  bitarray_set(blockp - heap_start); // mark block address as allocated in the bitmap

  return blockp + HEADER_SIZE;
}

/* Returns the size of an allocated block */
value_t memory_get_block_size(value_t *block) {
  return header_unpack_size(block[-1]);
}

/* Returns the tag of an allocated block */
tag_t memory_get_block_tag(value_t *block) {
  return header_unpack_tag(block[-1]);
}