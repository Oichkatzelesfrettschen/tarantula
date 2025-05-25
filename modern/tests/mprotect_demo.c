#include "posix.h"
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>

int main(void)
{
    void *p = posix_mmap(NULL, 4096, PROT_READ|PROT_WRITE,
                         MAP_ANON|MAP_PRIVATE, -1, 0);
    if (p == MAP_FAILED) {
        perror("mmap");
        return 1;
    }
    strcpy(p, "demo");
    if (posix_mprotect(p, 4096, PROT_READ) != 0) {
        perror("mprotect");
        return 1;
    }
    if (posix_msync(p, 4096, MS_SYNC) != 0) {
        perror("msync");
        return 1;
    }
    posix_munmap(p, 4096);
    printf("demo ok\n");
    return 0;
}
