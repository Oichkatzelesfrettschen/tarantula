#include <stdio.h>
#include "../include/exokernel.h"
/* Stubs delegating to user-space process manager */
extern int pm_fork(void);
extern int pm_exec(const char *path, char *const argv[]);

int
kern_fork(void)
{
    return pm_fork();
}

int
kern_exec(const char *path, char *const argv[])
{
    return pm_exec(path, argv);
}

