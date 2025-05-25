#define _DEFAULT_SOURCE
#define _XOPEN_SOURCE 700
#include "../../src-headers/posix_signal.h"
#include <stdio.h>
#include <unistd.h>
#include <signal.h>

static volatile sig_atomic_t got;

static void handler(int s) {
    (void)s;
    got = 1;
}

int main(void)
{
    struct sigaction sa = {0};
    sa.sa_handler = handler;
    sigemptyset(&sa.sa_mask);
    if (posix_sigaction(SIGUSR1, &sa, NULL) != 0) {
        perror("sigaction");
        return 1;
    }

    if (posix_killpg(getpgrp(), SIGUSR1) != 0) {
        perror("killpg");
        return 1;
    }

    for (int i = 0; i < 100 && !got; ++i)
        usleep(1000);
    if (!got) {
        fprintf(stderr, "handler not called\n");
        return 1;
    }

    sigset_t set;
    sigemptyset(&set);
    if (posix_sigprocmask(SIG_BLOCK, &set, NULL) != 0) {
        perror("sigprocmask");
        return 1;
    }

    return 0;
}
