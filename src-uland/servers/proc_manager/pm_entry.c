/* Entry points used by kernel stubs to perform fork and exec in user space. */
#include <unistd.h>
#include <sys/wait.h>
#include "proc_manager.h"

int
pm_fork(void)
{
    return fork();
}

int
pm_execve(const char *path, char *const argv[], char *const envp[])
{
    return execve(path, argv, envp);
}

int
pm_waitpid(int pid, int *status, int options)
{
    return waitpid(pid, status, options);
}
