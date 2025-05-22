#ifndef VM_VM_H
#define VM_VM_H
#include <stdint.h>

typedef void* vm_map_t;
typedef uintptr_t vm_offset_t;

#define VM_PROT_READ 1
#define VM_PROT_WRITE 2
#define KERN_SUCCESS 0
#define FALSE 0

int vm_fault(vm_map_t map, vm_offset_t addr, int prot, int wired);

#endif
