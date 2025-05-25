#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>
#include "../../tests/include/proc_manager.h"
#include "../../src-headers/exokernel.h"

int pm_fork(void) { return fork(); }
int pm_execve(const char *p, char *const a[], char *const e[]) { return execve(p, a, e); }
int pm_waitpid(int pid, int *st, int opt) { return waitpid(pid, st, opt); }

int main(void)
{
    char *argv[] = { "/bin/echo", "spawned", NULL };
    char *envp[] = { "DEMO=1", NULL };

    int pid = kern_fork();
    if (pid < 0) {
        perror("kern_fork");
        return 1;
    }
    if (pid == 0) {
        kern_execve(argv[0], argv, envp);
        perror("kern_execve");
        _exit(1);
    }

    int status;
    if (kern_waitpid(pid, &status, 0) < 0) {
        perror("kern_waitpid");
        return 1;
    }

    if (WIFEXITED(status))
        printf("child exited %d\n", WEXITSTATUS(status));

    return 0;
}
