#pragma once
#ifndef POSIX_H
#define POSIX_H

#include <stddef.h>
#include <sys/types.h>

void *posix_mmap(void *addr, size_t len, int prot, int flags, int fd, off_t off);
int posix_munmap(void *addr, size_t len);
int posix_mprotect(void *addr, size_t len, int prot);
int posix_msync(void *addr, size_t len, int flags);
int posix_get_prot(void *addr);

#endif /* POSIX_H */
