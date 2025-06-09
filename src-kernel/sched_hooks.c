#include "exokernel.h"
#include "ipc.h"
#include <stdio.h>
/* Stubs delegating to user-space scheduler */
extern void uland_sched_init(void);
/**
 * @brief Initialize the scheduler from user space.
 *
 * Sets up the IPC queue and notifies the user-space scheduler of
 * system startup.
 */
void kern_sched_init(void) {
    /* Initialize scheduler lock and IPC queue before sending messages */
    spinlock_init(&sched_lock);
    ipc_queue_init(&kern_ipc_queue);

    struct ipc_message msg = {.type = IPC_MSG_SCHED_INIT};
    (void)ipc_queue_send(&kern_ipc_queue, &msg);
    /* For now also directly call user library */
    uland_sched_init();
}
