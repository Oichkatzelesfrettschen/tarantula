#include "pthread.h"
#include <sys/wait.h>
#include <unistd.h>

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg) {
    (void)attr; /* attributes unused */
    pid_t pid = fork();
    if (pid < 0)
        return -1;
    if (pid == 0) {
        start_routine(arg);
        _exit(0);
    }
    thread->pid = pid;
    return 0;
}

int pthread_join(pthread_t thread, void **retval) {
    (void)retval; /* return value ignored */
    int status;
    if (waitpid(thread.pid, &status, 0) < 0)
        return -1;
    return 0;
}
