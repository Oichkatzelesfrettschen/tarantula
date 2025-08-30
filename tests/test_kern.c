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
    ipc_mailbox_init();
    kern_sched_init();

    int fd = kern_open("README.md", O_RDONLY);
    if (fd < 0) {
        perror("kern_open");
        return 1;
    }
    close(fd);


    /*
     * VM and process management hooks are stubs only.  In this
     * lightweight smoke test we merely invoke the file-open path
     * to verify that basic IPC wiring works.
     */

    printf("all ok\n");
    return 0;
}
