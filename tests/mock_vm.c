#include <stdint.h>
#include <stdbool.h>

typedef void* vm_map_t;
typedef uintptr_t vm_offset_t;

vm_map_t kernel_map;

int vm_fault(vm_map_t map, vm_offset_t addr, int prot, int wired)
{
    (void)map; (void)addr; (void)prot; (void)wired;
    return 0; /* KERN_SUCCESS */
}
