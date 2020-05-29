#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#include <stdalign.h>


#include "memory.h"
#include "fail.h"
#include "engine.h"


static value_t* memory_start = NULL;
static value_t* memory_end = NULL;
static value_t* blocks_start = NULL;

#define HEADER_SIZE 1

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

// address managment 

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  assert(memory_start <= (value_t*)p_addr && (value_t*)p_addr <= memory_end);
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Memory/size alignment

static size_t align_down(size_t value, size_t align) {
  assert(align > 0 && (align & (align - 1)) == 0); /* check power of 2 */
  return value & ~(align - 1);
}

static void* align_up(void* address, size_t align) {
  assert(align > 0 && (align & (align - 1)) == 0); /* check power of 2 */
  uintptr_t int_address = (uintptr_t)address;
  uintptr_t aligned_address = (int_address + align - 1) & ~(align - 1);
  return (void*)aligned_address;
}

char* memory_get_identity() {
  return "no GC (memory is never freed)";
}

void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = memory_start + (total_byte_size / sizeof(value_t)); //memory_end is outside of memory! not inclusive!
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);
  memory_start = memory_end = blocks_start = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}



// BITMAP =================================================================================================================================
typedef struct {
  size_t size;
  value_t *bits; // the bit array data; points to a region of the memory allocated for the program
} bitmap_t;
static bitmap_t bitmap = {0, NULL};

static const unsigned cell_bits = sizeof(*bitmap.bits) * CHAR_BIT;
static value_t log2_cell_bits; // initialized in the memory_setup function

static unsigned myctz(unsigned b) {
  unsigned n = 0;
  while ((b >>= 1) && ++n)
    ;
  return n;
}
#define log2_p2(x) (myctz(x))
#define div32_p2(x, k) (((x) + (((x) >> 31) & ((1 << (k)) - 1))) >> (k))
#define mod_p2(x, n) ((x) & ((n)-1))
/* macros to help with bit array operations */
#define cell(idx) (div32_p2((idx), log2_cell_bits))
#define set_mask(idx) (1u << mod_p2(idx, cell_bits))
#define clear_mask(idx) (~(set_mask(idx)))
/* bit array operations */
#define bitarray_set(idx) (bitmap.bits[cell(idx)] |= set_mask(idx))
#define bitarray_clear(idx) (bitmap.bits[cell(idx)] &= clear_mask(idx))
#define bitarray_test(idx) (bitmap.bits[cell(idx)] & set_mask(idx))

// Initializes the bit array size and pointer, as well as the log2(cell_bits) quantity.
static void bitarray_init(size_t size, value_t *base) {
  bitmap.size = size;
  bitmap.bits = base;
  log2_cell_bits = log2_p2(cell_bits); // used for quick division, see div32_p2 macro above
}
// ==============================================================================================================================

static value_t free_list_head = 0x0;  //virtual address to where the freelist start, used stack-wise
// now pointing (virtually) to memory_start but will be updated to point to blocks_start
// end of the free list is marked by a virtual pointer = 0, cf. physical pointer to memory_start


// calculate number of bytes to store a bitmap for a heap of 32-bit words
#define calc_bitmap_size(hs) ((hs)&31 ? ((hs) >> 5) + 1 : (hs) >> 5)

/*
 setup structures and variables for the garbage collector &  memory allocator
*/
void memory_set_heap_start(void* heap_start) {
  assert(blocks_start == NULL);
  size_t total_heap_size = (size_t)((char *)memory_end - (char *)heap_start); //todo change
  
  size_t bitmap_size, heap_size_left = total_heap_size;
  do { // calculate the bitmap size and the remaining heap size
    bitmap_size = calc_bitmap_size(heap_size_left);
    heap_size_left = total_heap_size - bitmap_size;
  } while (calc_bitmap_size(heap_size_left) != bitmap_size);
  //do until bitmap_size converges down to correct size

  
  bitarray_init(bitmap_size, heap_start);
  //bitmap_size += alignof(value_t) - (bitmap_size & (alignof(value_t) - 1));
  blocks_start = (value_t *)((char *)heap_start + bitmap_size);
  blocks_start = align_up(blocks_start, alignof(value_t));
  
  if ((void*) (blocks_start + HEADER_SIZE) >= memory_end)
    fail("not enough memory to load bitmap");

  *blocks_start = header_pack(tag_None, (value_t)(memory_end - blocks_start) - HEADER_SIZE);

  free_list_head = addr_p_to_v(blocks_start);
  blocks_start[HEADER_SIZE] = 0x0; // end of the free list is marked by a pointer to memory_start !
}

// a block is allocated if withing valid bounds and its bit is set in the bitmap
// do not follow if bit is not set -> random part of heap considered as block would break the vm (no valid size etc.)
// the bitmap bits are set at the physical block address (before HEADER) not virtual block (after HEADER)
#define is_allocated_block(va)                                                                     \
  (blocks_start < (va) && (va) < memory_end && bitarray_test((va)-blocks_start - HEADER_SIZE))

/*
  Sets the bit of all reachable block, starting from a register block, to 0
  So it is more of an "Unmark Reachable Blocks" function

  :input value_t *addr: physical pointer to the block (register block or other) to mark recursively
  :result: - blocks marked with 0
               a) Allocated Blocks Reachable: that were unmarked during this phase
               b) Unallocated blocks: that where already in the free list before this phase -> distinguishable by tag_None !
           - blocks marked with 1
               c) Allocated Blocks UnReachable

  --> during sweep phase, the free list has to be built with b) and c)
      c) can be recognized by bit set to 1
      b) can be recognized by bit set to 0 and distinguished from a) with tag_None
*/
static void mark_rec(value_t *addr) {

    if (!addr_p_to_v(addr))  //null block
    return;

    bitarray_clear(addr - blocks_start - HEADER_SIZE); // mark the current physical block, before header!
    printf("\n  mark cleared a bit at virtual address %d because the block is reachable", addr_p_to_v(addr));
    value_t size = header_unpack_size(addr[-1]); // get size of this block
    for(value_t i = 0; i<size; ++i){
      if (addr[i] & 0x3)  //pointers value contains address to 32 bits words! 4 bytes aligned!
        continue; // if element cannot be a pointer, go to next
      value_t *blockp = (value_t *)addr_v_to_p(addr[i]);
      if (is_allocated_block(blockp)) // this element points to a heap allocated block
        mark_rec(blockp);             // recursively mark the block it points to
    }
}


/*
  apply mark_rec to all register_banks which are treated like regular blocks
*/
static void mark(){
  value_t *reg = engine_get_Cb();
  mark_rec(reg);
  reg = engine_get_Ob();
  mark_rec(reg);
  reg = engine_get_Lb();
  mark_rec(reg);
  reg = engine_get_Ib();
  mark_rec(reg);
}

/*
  :input - value_t *start: start of new coalesced block
         - value_t *end: end of new coalesced block
  :return: new coalesced physical block with  header 
           added to the top of the free list (stack-wise)
*/
static void coalesce(value_t *start, value_t *end) {
  if (start == end) return;
  value_t size = (value_t)(end - start) - HEADER_SIZE; // calc coalesced block size
  *start = header_pack(tag_None, size); // create coalesced block
  start[HEADER_SIZE] = free_list_head; //push new block on top of stack
  free_list_head = addr_p_to_v(start); //push new block on top of stack
} 

/*
  :state1:  - blocks marked with 0
                      a) Allocated Blocks (supposed) Reachable. (we might be wrong because of untagged int)
                      b) Free blocks (tag_None)
            - blocks marked with 1
                      c) Allocated Blocks Unreachable ==> Free block
  :state2: - blocks marked with 0
                    a) free blocks
           - blocks marked with 1
                    b) allocated blocks (supposed reachable)
  
  free list rebuilt with - b) 0-bit and tag_None
                         - c) 1-bit
  we can iterate through all blocks of the heap by reading size from header
  and making jumps of the appropriate length
*/
static void sweep(){

  value_t *sweeper = blocks_start;                 
  value_t *first_free_block = sweeper;  

  free_list_head = 0x0; //end of free list is marked (virtually) by pointer to memory_start!

  while (sweeper != memory_end){ //memory_end not inclusive, if block sizes are correct

    const tag_t tag = header_unpack_tag(*sweeper);
    value_t size = header_unpack_size(*sweeper);
    size += (size == 0);
    if (bitarray_test(sweeper - blocks_start) ||  tag == tag_None) {
        bitarray_clear(sweeper - blocks_start); 
        printf("\n  sweeping found free block at %d", sweeper -  blocks_start);
        sweeper += size + HEADER_SIZE;
        continue;
    }

    // Allocated Reachable Block
    coalesce(first_free_block, sweeper); // coalesce blocks between first_free_block and sweeper
    bitarray_set(sweeper - blocks_start); // set the bitmap entry (was 0)
    sweeper += size + HEADER_SIZE; // advance sweeper
    first_free_block = sweeper;

  }

  // coalesce the last free block, if any
  coalesce(first_free_block, sweeper);
}


/*
  Mark & Sweep garbage collector
*/
static void garbage_collect(){
  printf("\nMARKING ----------------------------------------------");
  mark();
  printf("\nSWEEPING ---------------------------------------------");
  sweep();
  printf("\nENDING garbage collect -------------------------------\n");
  fflush(stdout);
}


/*
  :input  - block_p: physical pointer to the block to be splitted
              --> requirement: size(block_p)==size || size(block_p)>size+1
          - size: size of the desired block
  :result: Creating of rest_block with HEADER(tag_None,remaining_size)
           tag_None is used to distinguish this block from allocated unreachable blocks during sweep
           rest_block is added on top (stack-wise) of the free list
*/
static void add_split_to_free(value_t* block_p, value_t size){
  const value_t block_size = header_unpack_size(*block_p);

  if (block_size == size) //nothing to do
    return;
  
  const value_t remaining_size = block_size - size - HEADER_SIZE; 
  value_t *rest_block = block_p + (size + HEADER_SIZE);  
  *rest_block = header_pack(tag_None, remaining_size);

  rest_block[HEADER_SIZE] = free_list_head; // first element of the rest block contains virtual address (points to) free_list_head
  free_list_head = addr_p_to_v(rest_block); // update free_list_head to the virtual address of first block of free list (STACK)
}

/*
* Looks for a free block in of @size in free list and creates it with tag = @tag
* If the block was too big(by more than 1), splits the block and puts the rest on top of the free list
* :input - tag: tag to put in header of physical block
*        - size: size to put in header of physical block = total_size - HEADER_SIZE - 1(if zero-block)
* :output: - Null if no block was found => out of memory
*          - pointer to the HEADER(tag,size) of the physical block if succesfsull
*/
static value_t* get_physical_block(tag_t tag, value_t size){
  const value_t real_size = size + (size == 0); // no blocks of size 0, need room for storing a link !
  const value_t total_size = real_size + HEADER_SIZE; // physical block with metadata in header

  value_t* block_pointer = addr_v_to_p(free_list_head); // pointer to current block
  value_t* previous_virtual = &free_list_head; //pointer to virtual link to current block

    while(block_pointer != memory_start){ 
    value_t block_size = header_unpack_size(*block_pointer);
    if (block_size == real_size || block_size > real_size + 1) { //cannot be size + 1 ! -> split problem
      *previous_virtual = block_pointer[HEADER_SIZE]; // remove block from freeList
       add_split_to_free(block_pointer, real_size); //add splitted block on top of the freeList
      *block_pointer = header_pack(tag, size); // write block header
       bitarray_set(block_pointer - blocks_start); // Allocated block has 1-bit in bitmap
      return block_pointer;
    }
  previous_virtual = &block_pointer[HEADER_SIZE]; // update pointer to virtual link to current block
  block_pointer = addr_v_to_p(block_pointer[HEADER_SIZE]); // update physical pointer to current block
  }

  return NULL;
}



value_t* memory_allocate(tag_t tag, value_t size) {
  assert(blocks_start != NULL);
  value_t* pBlock = get_physical_block(tag,size);
  if(pBlock == NULL){
    garbage_collect();
    pBlock = get_physical_block(tag, size);
    if(pBlock == NULL){
        fail("no memory left (block of size %u requested)", size);
    }
  }
  value_t* vBlock = pBlock + HEADER_SIZE;
  printf("\nAllocated block at virtual address %d of size: %d", addr_p_to_v(vBlock), memory_get_block_size(vBlock));
  return vBlock;
}



value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}