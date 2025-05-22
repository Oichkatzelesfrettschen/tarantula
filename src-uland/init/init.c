#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

static const char *servers[] = {
    "/usr/libexec/proc_manager",
    "/usr/libexec/fs_server",
    NULL
};

int
main(void)
{
    for (const char **srv = servers; *srv != NULL; ++srv) {
        pid_t pid = fork();
        if (pid == -1) {
            perror("fork");
            return 1;
        }
        if (pid == 0) {
            execl(*srv, *srv, (char *)NULL);
            perror("execl");
            _exit(1);
        }
    }

    /* Replace this init with a shell once servers start. */
    execl("/bin/sh", "sh", (char *)NULL);
    perror("exec shell");
    return 1;
}
