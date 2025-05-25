#pragma once
#ifndef PROC_MANAGER_H
#define PROC_MANAGER_H

/* Derived from sys/kern/kern_proc.c */

#include <sys/types.h>
#include <sys/proc.h>

void procinit(void);
int chgproccnt(uid_t uid, int diff);
int inferior(struct proc *p);
struct proc *pfind(pid_t pid);
struct pgrp *pgfind(pid_t pgid);
int enterpgrp(struct proc *p, pid_t pgid, int mksess);
int leavepgrp(struct proc *p);
void pgdelete(struct pgrp *pgrp);
void fixjobc(struct proc *p, struct pgrp *pgrp, int entering);
void pgrpdump(void);

int pm_fork(void);
int pm_exec(const char *path, char *const argv[]);

#endif /* PROC_MANAGER_H */
