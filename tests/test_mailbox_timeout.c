#include "ipc.h"
#include "mailbox_t.h"
#include <stdio.h>
#include <time.h>

int main(void)
{
    ipc_mailbox_init();
    struct ipc_mailbox *a = ipc_mailbox_lookup(1);
    struct ipc_mailbox *b = ipc_mailbox_lookup(2);

    struct ipc_mailbox *boxes[] = { a, b };
    struct ipc_message msg;
    struct timespec ts = { .tv_sec = 0, .tv_nsec = 1000000 }; /* 1 ms */

    if (ipc_recv_t(boxes, 2, &msg, 5, &ts) != IPC_STATUS_TIMEOUT) {
        printf("unexpected receive\n");
        return 1;
    }

    printf("timeout ok\n");
    return 0;
}
