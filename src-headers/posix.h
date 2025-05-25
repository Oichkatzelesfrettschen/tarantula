#ifndef POSIX_H
#define POSIX_H

#include <stddef.h>
#include <sys/types.h>

int mkfifo(const char *path, int perm);
int posix_open(const char *path, int flags);
int posix_dup(int fd);
ssize_t posix_read(int fd, void *buf, size_t n);
ssize_t posix_write(int fd, const void *buf, size_t n);
int posix_close(int fd);

#endif /* POSIX_H */
