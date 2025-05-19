#include <stdio.h>
/* Stubs delegating to user-space file server */
extern int fs_open(const char *path, int flags);
int
kern_open(const char *path, int flags)
{
    return fs_open(path, flags);
}
