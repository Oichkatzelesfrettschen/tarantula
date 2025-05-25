#ifndef PROC_MANAGER_H
#define PROC_MANAGER_H
int pm_fork(void);
int pm_execve(const char *path, char *const argv[], char *const envp[]);
int pm_waitpid(int pid, int *status, int options);
#endif
