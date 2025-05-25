#pragma once
#ifndef POSIX_IPC_H
#define POSIX_IPC_H

#include <mqueue.h>
#include <semaphore.h>
#include <sys/mman.h>
#include <fcntl.h>

mqd_t cap_mq_open(int dirfd, const char *name, int oflag, mode_t mode,
                  struct mq_attr *attr);
int   cap_mq_unlink(int dirfd, const char *name);

sem_t *cap_sem_open(int dirfd, const char *name, int oflag, mode_t mode,
                    unsigned value);
int    cap_sem_unlink(int dirfd, const char *name);

int cap_shm_open(int dirfd, const char *name, int oflag, mode_t mode);
int cap_shm_unlink(int dirfd, const char *name);

#endif /* POSIX_IPC_H */
