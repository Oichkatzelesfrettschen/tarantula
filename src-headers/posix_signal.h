#ifndef POSIX_SIGNAL_H
#define POSIX_SIGNAL_H

#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#include <signal.h>
#if defined(__GNUC__)
#include_next <signal.h>
#endif

int posix_sigaction(int signum, const struct sigaction *act,
                    struct sigaction *oldact);
int posix_sigprocmask(int how, const sigset_t *set, sigset_t *oldset);
int posix_killpg(int pgrp, int sig);

#endif /* POSIX_SIGNAL_H */
