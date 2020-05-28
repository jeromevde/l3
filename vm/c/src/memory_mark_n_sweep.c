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

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  assert(memory_start <= (value_t*)p_addr && (value_t*)p_addr <= memory_end);
  return (value_t)((char*)p_addr - (char*)memory_start);
}

char* memory_get_identity() {
  return "no GC (memory is never freed)";
}

void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = memory_start + (total_byte_size / sizeof(value_t));
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



/* a simple bit array structure ******************************************************************/
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

static value_t free_list_head = {0};  //virtual address to where the freelist start (=STACK!)


#define calc_bitmap_size(hs) ((hs)&31 ? ((hs) >> 5) + 1 : (hs) >> 5)

void memory_set_heap_start(void* heap_start) {
  assert(blocks_start == NULL);
  size_t total_heap_size = (size_t)((char *)memory_end - (char *)heap_start); //todo change
  
  size_t bitmap_size, heap_size_left = total_heap_size;
  do { // calculate the bitmap size and the remaining heap size
    bitmap_size = calc_bitmap_size(heap_size_left);
    heap_size_left = total_heap_size - bitmap_size;
  } while (calc_bitmap_size(heap_size_left) != bitmap_size);
  
  bitarray_init(bitmap_size, heap_start);

  bitmap_size += alignof(value_t) - (bitmap_size & (alignof(value_t) - 1));
  
  blocks_start = (value_t *)((char *)heap_start + bitmap_size);
  *blocks_start = header_pack(tag_None, (value_t)(memory_end - blocks_start) - HEADER_SIZE);

  free_list_head = addr_p_to_v(blocks_start);

  //printf("\nMemory start:: %p\n", (void*)memory_start);
  //printf("\nBitmap size:%d", bitmap_size);
  //printf("\nBlock start: %p\n", (void*)blocks_start);
  //printf("\nMemory_end: %p\n", (void*)memory_end);
}


#define is_allocated_block(va)                                                                     \
  (blocks_start < (va) && (va) < memory_end && bitarray_test((va)-blocks_start - HEADER_SIZE))

static void mark_rec(value_t *addr) {
     printf("memory start: %p" , memory_start);
     printf("memory end: %p",  memory_end);
     printf("addr:%p" , addr);
     printf("test");

    if (!addr_p_to_v(addr))  //null block
    return;

    printf("\nmemory start %p \n", (void*)memory_start);
    printf("\nmemory end %p \n", (void*)memory_end);
    printf("\nblock start %p \n", (void*)blocks_start);
    printf("\nchecking address %p \n", (void*)addr);
    printf("---------------------cleared alloc bloc bit at heap address:%ld", (addr - blocks_start - HEADER_SIZE));

    bitarray_clear(addr - blocks_start - HEADER_SIZE); // mark the current block, before header!
    fflush(stdout);
    value_t size = header_unpack_size(addr[-1]); // get size of this block
    printf("checking block at address:%p of size %d", (void*)addr, size );
    fflush(stdout);
    for(value_t i = 0; i<size; ++i){
      printf("i:%d and addr[i]%p, size %d:",i,(void*)addr+i, size);
      fflush(stdout);
      if (addr[i] & 0x3)  //pointers value contains address to 32 bits words! 4 bytes aligned!
        continue; // if element cannot be a pointer, go to next
      value_t *blockp = (value_t *)addr_v_to_p(addr[i]);
      if (is_allocated_block(blockp)) // this element points to a heap allocated block
        mark_rec(blockp);             // recursively mark the block it points to
    }

}



static void mark(){
  value_t *reg = NULL;
  reg = engine_get_Ob();
  mark_rec(reg);
  engine_get_Lb();
  mark_rec(reg);
  engine_get_Ib();
  mark_rec(reg);
  reg = engine_get_Lb();
  mark_rec(reg);
}

static void sweep(){
  
}

static void garbage_collect(){
  mark();
  sweep();
}

static void split_add_to_free(value_t* block_p, value_t size){
  value_t block_size = header_unpack_size(*block_p);
  if (block_size == size)
    return;
  
  const value_t rem_size = block_size - size - HEADER_SIZE; // calculate remaining size
  value_t *sblock = block_p + (size + HEADER_SIZE);          // get a pointer to the split block
  *sblock = header_pack(tag_None, rem_size); // free blocks are written with real size, header included
  sblock[HEADER_SIZE] = free_list_head;     // push new block on top of the free list stack
  free_list_head = addr_p_to_v(sblock); // push new block on top of the free list stack
}

/*
* looks for a free block
* returns memory_start if not found
*/
static value_t* get_physical_block(tag_t tag, value_t size){
  value_t real_size = size + (size == 0); // no blocks of size 0!
  value_t total_size = real_size + HEADER_SIZE; // physical block with metadata

  value_t* block_pointer = addr_v_to_p(free_list_head); // pointer to current block
  value_t* previous_virtual = &free_list_head; //pointer to virtual link to current block

  printf("first element of first block %p",addr_v_to_p(block_pointer[HEADER_SIZE]));
  //while( block_pointer != memory_start){ //last block
  printf("\nblockpointer:%p", block_pointer);
  printf("\nmemory_start:%p", memory_start);
  printf("\nblocks start:%p", blocks_start);
  printf("\nmemory end:%p", memory_end);
  fflush(stdout);
    while( block_pointer != memory_start){ //last block
    value_t block_size = header_unpack_size(*block_pointer);
    if (block_size == real_size || block_size > real_size + 1) { //cannot be size + 1 ! -> split problem
      *previous_virtual = block_pointer[HEADER_SIZE];
      split_add_to_free(block_pointer, real_size);
      *block_pointer = header_pack(tag, size); // write block header
      return block_pointer;
    }
  previous_virtual = &block_pointer[HEADER_SIZE];
  block_pointer = addr_v_to_p(block_pointer[HEADER_SIZE]);
  }

  return memory_start;
}



value_t* memory_allocate(tag_t tag, value_t size) {
  assert(blocks_start != NULL);

  value_t* pBlock = get_physical_block(tag,size);
  if(pBlock == memory_start){
    garbage_collect();
    pBlock = get_physical_block(tag, size);
    if(pBlock == memory_start){
        fail("no memory left (block of size %u requested)", size);
    }
  }

  bitarray_set(pBlock - blocks_start); // mark block address as allocated in the bitmap
  value_t* vBlock = pBlock + HEADER_SIZE;
  return vBlock;
  }



value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}
