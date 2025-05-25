#include "timer.h"
#include "spinlock.h"
#include <time.h>
#include <unistd.h>
#include <errno.h>

#define MAX_PROC_TIMERS 32

struct proc_timer {
    pid_t pid;
    unsigned long long ns;
};

static struct proc_timer timers[MAX_PROC_TIMERS];
SPINLOCK_DEFINE(timer_lock);

void timer_init(void)
{
    for (int i = 0; i < MAX_PROC_TIMERS; ++i)
        timers[i].pid = -1;
    spinlock_init(&timer_lock);
}

static struct proc_timer *lookup_timer(pid_t pid)
{
    for (int i = 0; i < MAX_PROC_TIMERS; ++i) {
        if (timers[i].pid == pid)
            return &timers[i];
    }
    for (int i = 0; i < MAX_PROC_TIMERS; ++i) {
        if (timers[i].pid == -1) {
            timers[i].pid = pid;
            timers[i].ns = 0;
            return &timers[i];
        }
    }
    return NULL;
}

void timer_add_sleep(pid_t pid, unsigned long long ns)
{
    SCOPED_SPINLOCK(g, &timer_lock);
    struct proc_timer *t = lookup_timer(pid);
    if (t)
        t->ns += ns;
}

unsigned long long timer_get_sleep(pid_t pid)
{
    SCOPED_SPINLOCK(g, &timer_lock);
    struct proc_timer *t = lookup_timer(pid);
    return t ? t->ns : 0;
}

static unsigned long long diff_ns(const struct timespec *a, const struct timespec *b)
{
    return (b->tv_sec - a->tv_sec) * 1000000000ull + (b->tv_nsec - a->tv_nsec);
}

int nanosleep(const struct timespec *req, struct timespec *rem)
{
    if (!req) {
        errno = EINVAL;
        return -1;
    }

    struct timespec ts = *req;
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    int err;
    do {
        err = clock_nanosleep(CLOCK_MONOTONIC, 0, &ts, &ts);
    } while (err == EINTR);
    clock_gettime(CLOCK_MONOTONIC, &end);

    if (err) {
        if (rem)
            *rem = ts;
        errno = err;
        return -1;
    }

    if (rem) {
        rem->tv_sec = 0;
        rem->tv_nsec = 0;
    }

    timer_add_sleep(getpid(), diff_ns(&start, &end));
    return 0;
}

