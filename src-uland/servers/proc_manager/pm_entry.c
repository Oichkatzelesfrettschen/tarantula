/* Entry points used by kernel stubs to perform fork and exec in user space. */
#include <unistd.h>
#include "proc_manager.h"

int
pm_fork(void)
{
    return fork();
}

int
pm_exec(const char *path, char *const argv[])
{
    return execv(path, argv);
}
