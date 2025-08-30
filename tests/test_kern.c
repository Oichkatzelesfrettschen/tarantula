#include "ipc.h"
#include <stdio.h>

int main(void) {
    /* Initialize the global kernel IPC queue */
    ipc_queue_init(&kern_ipc_queue);

    /* Send a heartbeat through the queue */
    struct ipc_message msg = {
        .type = IPC_MSG_HEARTBEAT,
        .a = 0xdeadbeef,
    };
    if (ipc_queue_send(&kern_ipc_queue, &msg) != EXO_IPC_OK) {
        fprintf(stderr, "send failed\n");
        return 1;
    }

    /* Receive the message back immediately */
    struct ipc_message out;
    if (ipc_queue_recv_timed(&kern_ipc_queue, &out, 1) != EXO_IPC_OK ||
        out.type != IPC_MSG_HEARTBEAT || out.a != 0xdeadbeef) {
        fprintf(stderr, "receive mismatch\n");
        return 1;
    }

    puts("all ok");
    return 0;
}
