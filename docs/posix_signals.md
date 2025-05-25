# POSIX signal helpers

`libposix` wraps a few signal-related system calls to keep the interface
uniform across platforms.

```c
int posix_sigaction(int signum, const struct sigaction *act,
                    struct sigaction *oldact);
int posix_sigprocmask(int how, const sigset_t *set, sigset_t *oldset);
int posix_killpg(int pgrp, int sig);
```

The program `modern/tests/posix_signal_demo.c` demonstrates installing a
custom handler and sending a signal to the current process group.
