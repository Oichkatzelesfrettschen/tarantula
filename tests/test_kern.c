#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
#include "exokernel.h"
#include "fs_server.h"
#include "libvm.h"
#include "proc_manager.h"
#include "ipc.h"

int main(void) {
    ipc_queue_init(&kern_ipc_queue);

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
            fprintf(stderr, "child failed\n");
            return 1;
        }
    }

    printf("all ok\n");
    return 0;
}
