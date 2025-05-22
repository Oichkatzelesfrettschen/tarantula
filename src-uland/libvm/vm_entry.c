/* Minimal page fault hook used by the exokernel. */
#include <vm/vm.h>
#include "libvm.h"

extern vm_map_t kernel_map;

bool
uland_vm_fault(void *addr)
{
    return vm_fault(kernel_map, (vm_offset_t)addr, VM_PROT_READ|VM_PROT_WRITE,
                    FALSE) == KERN_SUCCESS;
}
