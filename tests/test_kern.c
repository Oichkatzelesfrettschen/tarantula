#include "ipc.h"
#include <stdio.h>

int main(void) {
    /* Initialize subsystems needed by IPC. Keeping both sides of the merge:
     * - ipc_mailbox_init and kern_sched_init from master
     * - ipc_queue_init from feature branch
     * Order here prefers bringing up lower-level facilities first.
     */
    ipc_mailbox_init();
    kern_sched_init();
    ipc_queue_init(&kern_ipc_queue);

    /* Send a heartbeat through the queue */
    struct ipc_message msg = {
        .type = IPC_MSG_HEARTBEAT,
        .a = 0xdeadbeef,
    };

    int rc = ipc_queue_send(&kern_ipc_queue, &msg);
    if (rc != EXO_IPC_OK) {
        fprintf(stderr, "IPC send failed: rc=%d\n", rc);
        return 1;
    }

    /* Receive the message back immediately (tiny timeout to ensure non-blocking smoke test) */
    struct ipc_message out;
    rc = ipc_queue_recv_timed(&kern_ipc_queue, &out, 1);
    if (rc != EXO_IPC_OK) {
        fprintf(stderr, "IPC receive failed: rc=%d\n", rc);
        return 1;
    }

    if (out.type != IPC_MSG_HEARTBEAT || out.a != 0xdeadbeef) {
        fprintf(stderr, "IPC receive mismatch: got type=%u a=0x%x\n",
                (unsigned)out.type, (unsigned)out.a);
        return 1;
    }

    puts("ipc_loopback_smoke: all ok");
    return 0;
}