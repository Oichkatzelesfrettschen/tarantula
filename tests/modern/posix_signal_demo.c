#define _DEFAULT_SOURCE
#define _XOPEN_SOURCE 700
#include "../../src-headers/posix_signal.h"
#include <assert.h>
#include <unistd.h>
#include <signal.h>

static volatile sig_atomic_t got;

static void handler(int signo)
{
    (void)signo;
    got = 1;
}

int main(void)
{
    struct sigaction sa = {0};
    sa.sa_handler = handler;
    sigemptyset(&sa.sa_mask);
    assert(posix_sigaction(SIGUSR1, &sa, NULL) == 0);

    assert(posix_killpg(getpgrp(), SIGUSR1) == 0);
    for (int i = 0; i < 100 && !got; ++i)
        usleep(1000);
    assert(got);

    sigset_t set;
    sigemptyset(&set);
    assert(posix_sigprocmask(SIG_BLOCK, &set, NULL) == 0);

    return 0;
}
