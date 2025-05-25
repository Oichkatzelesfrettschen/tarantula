#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 700
#include <pthread.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>
#include <unistd.h>
#include "ipc.h"

struct mailbox {
    struct ipc_queue q;
};

static void mailbox_init(struct mailbox *mb) {
    ipc_queue_init(&mb->q);
}

static bool mailbox_send(struct mailbox *mb, const struct ipc_message *m) {
    return ipc_queue_send(&mb->q, m);
}

static bool mailbox_recv_timeout(struct mailbox *mb, struct ipc_message *m, int ms) {
    struct timespec start, now;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (;;) {
        if (ipc_queue_recv(&mb->q, m))
            return true;
        clock_gettime(CLOCK_MONOTONIC, &now);
        long elapsed = (now.tv_sec - start.tv_sec) * 1000 +
                       (now.tv_nsec - start.tv_nsec) / 1000000;
        if (elapsed >= ms)
            return false;
        struct timespec ts = {0, 1000000};
        nanosleep(&ts, NULL);
    }
}

struct sender_arg {
    struct mailbox *mb;
    int delay_ms;
};

static void *sender(void *arg) {
    struct sender_arg *s = arg;
    struct ipc_message msg = { .type = 42 };
    struct timespec ts = { s->delay_ms / 1000, (s->delay_ms % 1000) * 1000000 };
    nanosleep(&ts, NULL);
    mailbox_send(s->mb, &msg);
    return NULL;
}

int main(void) {
    struct mailbox a, b, empty;
    mailbox_init(&a);
    mailbox_init(&b);
    mailbox_init(&empty);

    pthread_t t1, t2;
    struct sender_arg sa = { &a, 100 };
    struct sender_arg sb = { &b, 200 };
    pthread_create(&t1, NULL, sender, &sa);
    pthread_create(&t2, NULL, sender, &sb);

    struct ipc_message msg;
    bool ok1 = mailbox_recv_timeout(&a, &msg, 500);
    bool ok2 = mailbox_recv_timeout(&b, &msg, 500);
    bool timeout = !mailbox_recv_timeout(&empty, &msg, 100);

    pthread_join(t1, NULL);
    pthread_join(t2, NULL);

    if (ok1 && ok2 && timeout) {
        printf("mailbox tests passed\n");
        return 0;
    }
    printf("mailbox tests failed\n");
    return 1;
}
