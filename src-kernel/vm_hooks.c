#include "exokernel.h"
#include <stdbool.h>
#include "ipc.h"
#include <unistd.h>
/* Stubs delegating to user-space VM library */
extern bool uland_vm_fault(void *addr);

bool
kern_vm_fault(void *addr)
{
    struct ipc_mailbox *mb = ipc_get_mailbox();
    struct ipc_message msg = { .type = IPC_MSG_VM_FAULT, .a = (uintptr_t)addr };
    ipc_queue_send(mb, &msg);
    /* Synchronous reply */
    struct ipc_message reply;
    if (ipc_queue_recv(mb, &reply)) {
        if (reply.type != IPC_MSG_VM_FAULT)
            return reply.a != 0;
    }
    return uland_vm_fault(addr);
}
