#include "posix.h"
#include <sys/mman.h>
#include <stdbool.h>
#include <stddef.h>

#define MAX_MAPS 128

struct mapping {
    void *addr;
    size_t len;
    int prot;
    bool used;
};

static struct mapping maps[MAX_MAPS];

static struct mapping *find_mapping(void *addr, size_t len)
{
    for (int i = 0; i < MAX_MAPS; ++i) {
        if (!maps[i].used)
            continue;
        char *start = maps[i].addr;
        char *end = start + maps[i].len;
        char *a = addr;
        char *b = a + len;
        if (a >= start && b <= end)
            return &maps[i];
    }
    return NULL;
}

void *posix_mmap(void *addr, size_t len, int prot, int flags, int fd, off_t off)
{
    void *p = mmap(addr, len, prot, flags, fd, off);
    if (p == MAP_FAILED)
        return p;
    for (int i = 0; i < MAX_MAPS; ++i) {
        if (!maps[i].used) {
            maps[i].addr = p;
            maps[i].len = len;
            maps[i].prot = prot;
            maps[i].used = true;
            break;
        }
    }
    return p;
}

int posix_munmap(void *addr, size_t len)
{
    int r = munmap(addr, len);
    if (r == 0) {
        struct mapping *m = find_mapping(addr, len);
        if (m)
            m->used = false;
    }
    return r;
}

int posix_mprotect(void *addr, size_t len, int prot)
{
    int r = mprotect(addr, len, prot);
    if (r == 0) {
        struct mapping *m = find_mapping(addr, len);
        if (m)
            m->prot = prot;
    }
    return r;
}

int posix_msync(void *addr, size_t len, int flags)
{
    return msync(addr, len, flags);
}

int posix_get_prot(void *addr)
{
    struct mapping *m = find_mapping(addr, 0);
    return m ? m->prot : -1;
}
