#include <stdio.h>
/* Stubs delegating to user-space VM library */
extern int uland_vm_fault(void *addr);
int
kern_vm_fault(void *addr)
{
    return uland_vm_fault(addr);
}
