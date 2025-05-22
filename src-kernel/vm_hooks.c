#include "../include/exokernel.h"
#include <stdbool.h>
#include "ipc.h"
/* Stubs delegating to user-space VM library */
extern bool uland_vm_fault(void *addr);

bool
kern_vm_fault(void *addr)
{
    struct ipc_message msg = { .type = IPC_MSG_VM_FAULT, .a = (uintptr_t)addr };
    ipc_queue_send(&kern_ipc_queue, &msg);
    /* Synchronous reply */
    struct ipc_message reply;
    if (ipc_queue_recv(&kern_ipc_queue, &reply))
        return reply.a != 0;
    return uland_vm_fault(addr);
}
