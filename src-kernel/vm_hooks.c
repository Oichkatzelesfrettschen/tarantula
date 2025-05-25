#include "exokernel.h"
#include <stdbool.h>
#include "ipc.h"
#include <exo_ipc.h>
/* Stubs delegating to user-space VM library */
extern bool uland_vm_fault(void *addr);

bool
kern_vm_fault(void *addr)
{
    struct ipc_message msg = { .type = IPC_MSG_VM_FAULT, .a = (uintptr_t)addr };
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    /* Synchronous reply */
    struct ipc_message reply;
    struct ipc_mailbox *mb = ipc_mailbox_current();
    if (ipc_queue_recv_timed(&mb->queue, &reply, 1000) == EXO_IPC_OK) {
        if (reply.type != IPC_MSG_VM_FAULT)
            return reply.a != 0;
    }
    return uland_vm_fault(addr);
}
