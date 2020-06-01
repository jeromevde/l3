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



// BITMAP =========================================================================================================================
typedef value_t * bitmap_t; // the bit array data; points to a region of the memory allocated for the program
static bitmap_t bitmap = NULL;

/* BITMAP constants */
static unsigned log2_p2(unsigned x) {
  unsigned n = 0;
  while (x >>= 1) {++n;}
  return n;
}
static const unsigned bits_per_word = sizeof(*bitmap) * CHAR_BIT;
static value_t log2_bits_per_word;

/* BITMAP macros */
#define div32_p2(x, k) (((x) + (((x) >> 31) & ((1 << (k)) - 1))) >> (k))
#define mod_p2(x, n) ((x) & ((n)-1))
#define index(idx) (div32_p2((idx), log2_bits_per_word))
#define one_mask(idx) (1u << mod_p2(idx, bits_per_word))
#define zero_mask(idx) (~(one_mask(idx)))
#define bitarray_set(idx) (bitmap[index(idx)] |= one_mask(idx))
#define bitarray_clear(idx) (bitmap[index(idx)] &= zero_mask(idx))
#define bitarray_test(idx) (bitmap[index(idx)] & one_mask(idx))

static void bitmap_init(value_t *base) {
  bitmap = base;
  log2_bits_per_word = log2_p2(bits_per_word); 
}
// ================================================================================================================================

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
  bitmap_init(heap_start);

  char * blocks_start_unaligned = ((char *)heap_start + bitmap_size);
  blocks_start = (value_t *)align_up(blocks_start_unaligned, alignof(value_t));
  if ((blocks_start + HEADER_SIZE) >= memory_end)
    fail("not enough memory to load bitmap");
  *blocks_start = header_pack(tag_None, (value_t)(memory_end - blocks_start) - HEADER_SIZE);

  blocks_start[HEADER_SIZE] = 0x0; // end of the free list is marked by a pointer to memory_start !
  free_list_head = addr_p_to_v(blocks_start);
}



//=================================================================================================================================
// start of GARBAGE COLLECTOR
//=================================================================================================================================

// a block is allocated if withing valid bounds and its bit is set in the bitmap
// do not follow if bit is not set -> random part of heap considered as block would break the vm (no valid size etc.)
// the bitmap bits are set at the physical block address (before HEADER) not the virtual block (after HEADER)
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

    //printf("\n  mark cleared a bit for virtual address %d because the block is reachable", addr_p_to_v(addr));
    value_t size = header_unpack_size(addr[-1]); // get size of this block
    for(value_t i = 0; i<size; ++i){
      if (!(addr[i] & 0x3)){   //pointers value contains address to 32 bits words! 4 bytes aligned!
        value_t *blockp = (value_t *)addr_v_to_p(addr[i]);
        if (is_allocated_block(blockp)) mark_rec(blockp);            
      }
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

    if (bitarray_test(sweeper - blocks_start) ||  tag == tag_None) { // Allocated Unreachable or Free Block
      bitarray_clear(sweeper - blocks_start); 
      //printf("\n  sweeping found free block at %d", sweeper -  blocks_start);
      sweeper += size + HEADER_SIZE;
    } else { // Allocated Reachable Block
      coalesce(first_free_block, sweeper); // coalesce cleared block preceding this block
      bitarray_set(sweeper - blocks_start); // bitmap from 0 to 1 because it is a reachable block
      sweeper += size + HEADER_SIZE;
      first_free_block = sweeper;
    }
  }

  // coalesce the (possible) last free block
  coalesce(first_free_block, sweeper);
}


/*
  Mark & Sweep SINGLE FREE LIST garbage collector
*/
static void garbage_collect(){
  //printf("\nMARKING ----------------------------------------------");
  mark();
  //printf("\nSWEEPING ---------------------------------------------");
  sweep();
  //printf("\nENDING garbage collect -------------------------------\n");
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
static void add_rest_to_free(value_t* block_p, value_t size){
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

  value_t* block_pointer = addr_v_to_p(free_list_head); // pointer to current block
  value_t* previous_virtual = &free_list_head; //pointer to virtual link to current block

    while(block_pointer != memory_start){ 
    value_t block_size = header_unpack_size(*block_pointer);
    if (block_size == real_size || block_size > real_size +  HEADER_SIZE) { //either exact size or splittable (enough room for 2 headers)
      *previous_virtual = block_pointer[HEADER_SIZE]; // remove block from freeList
       add_rest_to_free(block_pointer, real_size); //add splitted block on top of the freeList
      *block_pointer = header_pack(tag, size); // write block header
       bitarray_set(block_pointer - blocks_start); // Allocated block has 1-bit in bitmap
      return block_pointer;
    }
  previous_virtual = &block_pointer[HEADER_SIZE]; // update pointer to virtual link to current block
  block_pointer = addr_v_to_p(block_pointer[HEADER_SIZE]); // update physical pointer to current block
  }

  return NULL;
}

//=================================================================================================================================
// end of GARBAGE COLLECTOR
//=================================================================================================================================




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
  //printf("\nAllocated block at virtual address %d of size: %d", addr_p_to_v(vBlock), memory_get_block_size(vBlock));
  return vBlock;
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}
