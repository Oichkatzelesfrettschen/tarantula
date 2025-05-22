#include "../include/exokernel.h"
#include <stdbool.h>
/* Stubs delegating to user-space VM library */
extern bool uland_vm_fault(void *addr);
bool kern_vm_fault(void *addr) { return uland_vm_fault(addr); }
