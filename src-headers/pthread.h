#pragma once
#ifndef TARANTULA_PTHREAD_H
#define TARANTULA_PTHREAD_H

#include <unistd.h>

typedef struct {
    pid_t pid;
} pthread_t;

typedef int pthread_attr_t;

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);

#endif /* TARANTULA_PTHREAD_H */
