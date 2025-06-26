/* Simple wrapper used by the exokernel file hook. */
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include "fs_server.h"

int
fs_open(const char *path, int flags)
{
    return open(path, flags, 0);
}
