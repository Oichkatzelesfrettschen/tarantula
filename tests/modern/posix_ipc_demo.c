#define _GNU_SOURCE  /* expose AT_FDCWD on glibc */
#include "../../src-headers/posix_ipc.h"
#include <assert.h>
#include <unistd.h>
#include <fcntl.h>
#include <mqueue.h>
#include <semaphore.h>

int main(void)
{
    mqd_t mq = cap_mq_open(AT_FDCWD, "/demo_q", O_CREAT | O_RDWR, 0600, NULL);
    assert(mq != (mqd_t)-1);
    assert(cap_mq_unlink(AT_FDCWD, "/demo_q") == 0);
    assert(mq_close(mq) == 0);

    sem_t *sem = cap_sem_open(AT_FDCWD, "/demo_sem", O_CREAT, 0600, 1);
    assert(sem != SEM_FAILED);
    assert(sem_post(sem) == 0);
    assert(sem_close(sem) == 0);
    assert(cap_sem_unlink(AT_FDCWD, "/demo_sem") == 0);

    int fd = cap_shm_open(AT_FDCWD, "/demo_shm", O_CREAT | O_RDWR, 0600);
    assert(fd >= 0);
    assert(cap_shm_unlink(AT_FDCWD, "/demo_shm") == 0);
    assert(close(fd) == 0);

    return 0;
}
