#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <unistd.h>
#include <time.h>
#include "ipc.h"
#include "../libipc/ipc.h"

struct managed {
    const char *path;
    pid_t pid;
    time_t last_beat;
};

static struct managed managed_servers[] = {
    {"/usr/libexec/proc_manager", 0, 0},
    {"/usr/libexec/fs_server", 0, 0},
    {NULL, 0, 0}
};

static void spawn_servers(void)
{
    for (struct managed *m = managed_servers; m->path; ++m) {
        pid_t pid = fork();
        if (pid == -1) {
            perror("fork");
            continue;
        }
        if (pid == 0) {
            execl(m->path, m->path, (char *)NULL);
            perror("execl");
            _exit(1);
        }
        m->pid = pid;
        m->last_beat = time(NULL);
    }
}

int main(void)
{
    spawn_servers();

    struct ipc_message msg;
    for (;;) {
        if (ipc_recv(&msg) && msg.type == IPC_MSG_HEARTBEAT) {
            for (struct managed *m = managed_servers; m->path; ++m) {
                if (m->pid == (pid_t)msg.a)
                    m->last_beat = time(NULL);
            }
        }

        time_t now = time(NULL);
        for (struct managed *m = managed_servers; m->path; ++m) {
            if (m->pid > 0 && now - m->last_beat > 5) {
                fprintf(stderr, "%s missed heartbeat\n", m->path);
                m->last_beat = now;
            }
        }
        usleep(500000);
    }
    return 0;
}
