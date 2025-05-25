#include "posix_signal.h"
#include <signal.h>
#include <unistd.h>

int posix_sigaction(int signum, const struct sigaction *act,
                    struct sigaction *oldact)
{
    return sigaction(signum, act, oldact);
}

int posix_sigprocmask(int how, const sigset_t *set, sigset_t *oldset)
{
    return sigprocmask(how, set, oldset);
}

int posix_killpg(int pgrp, int sig)
{
    return killpg(pgrp, sig);
}
