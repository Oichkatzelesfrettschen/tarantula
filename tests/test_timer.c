#include "timer.h"
#include <stdio.h>
#include <time.h>
#include <unistd.h>

int main(void)
{
    timer_init();
    struct timespec ts = { .tv_sec = 0, .tv_nsec = 50000000 }; /* 50ms */
    if (nanosleep(&ts, NULL) != 0) {
        perror("nanosleep");
        return 1;
    }
    unsigned long long ns = timer_get_sleep(getpid());
    if (ns < 50000000ull) {
        printf("timer tracking failed: %llu\n", ns);
        return 1;
    }
    printf("timer ok\n");
    return 0;
}
