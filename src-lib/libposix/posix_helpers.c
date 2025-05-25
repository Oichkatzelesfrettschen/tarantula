#include "posix_helpers.h"
#include <sys/types.h>
#include <sys/socket.h>
#include <arpa/inet.h>

int posix_setsockopt(int fd, int level, int optname,
                     const void *optval, socklen_t optlen)
{
    return setsockopt(fd, level, optname, optval, optlen);
}

int posix_getsockopt(int fd, int level, int optname,
                     void *optval, socklen_t *optlen)
{
    return getsockopt(fd, level, optname, optval, optlen);
}

int posix_inet_pton(int af, const char *src, void *dst)
{
    return inet_pton(af, src, dst);
}

const char *posix_inet_ntop(int af, const void *src, char *dst, socklen_t size)
{
    return inet_ntop(af, src, dst, size);
}
