/* Simple wrapper used by the exokernel file hook. */
#include "fs_server.h"
/* clang-format off */
#include <sys/types.h>
/* clang-format on */
#include <fcntl.h>
#include <unistd.h>

int fs_open(const char *path, int flags) { return open(path, flags, 0); }
