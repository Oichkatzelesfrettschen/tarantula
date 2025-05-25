#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/mman.h>
#include "exokernel.h"
#include "fs_server.h"
#include "libvm.h"
#include "posix.h"
#include "proc_manager.h"
#include "ipc.h"

int main(void) {
    /* start scheduler which also sets up the IPC queue */
    kern_sched_init();

    int fd = kern_open("README.md", O_RDONLY);
    if (fd < 0) {
        perror("kern_open");
        return 1;
    }
    close(fd);

    if (!kern_vm_fault((void *)0x1000)) {
        fprintf(stderr, "kern_vm_fault failed\n");
        return 1;
    }

    int pid = kern_fork();
    if (pid < 0) {
        perror("kern_fork");
        return 1;
    }
    if (pid == 0) {
        exit(0);
    } else {
        int status; waitpid(pid, &status, 0);
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
            fprintf(stderr, "child failed: pid=%d status=%d\n", pid, status);
            return 1;
        }
    }

    void *region = posix_mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                               MAP_ANON | MAP_PRIVATE, -1, 0);
    if (region == MAP_FAILED) {
        perror("mmap");
        return 1;
    }
    if (posix_mprotect(region, 4096, PROT_READ) != 0) {
        perror("mprotect");
        return 1;
    }
    if (posix_get_prot(region) != PROT_READ) {
        fprintf(stderr, "prot not updated\n");
        return 1;
    }
    if (posix_msync(region, 4096, MS_SYNC) != 0) {
        perror("msync");
        return 1;
    }
    if (posix_munmap(region, 4096) != 0) {
        perror("munmap");
        return 1;
    }

    printf("all ok\n");
    return 0;
}
