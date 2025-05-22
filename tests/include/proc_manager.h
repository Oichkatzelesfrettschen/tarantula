#ifndef PROC_MANAGER_H
#define PROC_MANAGER_H
int pm_fork(void);
int pm_exec(const char *path, char *const argv[]);
#endif
