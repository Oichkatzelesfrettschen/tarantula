#pragma once
#ifndef POSIX_HELPERS_H
#define POSIX_HELPERS_H

#include <sys/socket.h>

int posix_setsockopt(int fd, int level, int optname,
                     const void *optval, socklen_t optlen);
int posix_getsockopt(int fd, int level, int optname,
                     void *optval, socklen_t *optlen);
int posix_inet_pton(int af, const char *src, void *dst);
const char *posix_inet_ntop(int af, const void *src, char *dst, socklen_t size);

#endif /* POSIX_HELPERS_H */
