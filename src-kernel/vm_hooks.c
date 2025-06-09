#include "exo_ipc.h"
#include "exokernel.h"
#include "ipc.h"
#include <stdbool.h>
/* Stubs delegating to user-space VM library */
extern bool uland_vm_fault(void *addr);

/**
 * @brief Handle a virtual memory fault in user space.
 *
 * Dispatches an IPC message to the VM library and waits for a reply.
 * If the reply is missing the local handler is used as a fallback.
 *
 * @param addr Faulting address.
 * @return true if the fault was handled successfully.
 */
bool kern_vm_fault(void *addr) {
    struct ipc_message msg = {.type = IPC_MSG_VM_FAULT, .a = (uintptr_t)addr};
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
