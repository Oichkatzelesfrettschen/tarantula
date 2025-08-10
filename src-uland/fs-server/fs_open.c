/* Simple wrapper used by the exokernel file hook. */
#include "fs_server.h"
#include <fcntl.h>
#include <sys/types.h>
#include <unistd.h>

int fs_open(const char *path, int flags) { return open(path, flags, 0); }
