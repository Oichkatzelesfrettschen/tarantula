#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>

extern char **environ;

int main(void) {
    char cwd[256];
    if (getcwd(cwd, sizeof(cwd)))
        printf("cwd=%s\n", cwd);

    int fd = open("/tmp/pathtrans_test/orig/file.txt", O_RDONLY);
    if (fd >= 0) {
        printf("open success\n");
        close(fd);
    }

    if (link("/tmp/pathtrans_test/orig/file.txt",
             "/tmp/pathtrans_test/orig/link.txt") == 0) {
        printf("link success\n");
        unlink("/tmp/pathtrans_test/orig/link.txt");
    }

    if (chdir("/tmp/pathtrans_test/orig") == 0) {
        getcwd(cwd, sizeof(cwd));
        printf("after chdir cwd=%s\n", cwd);
    }

    char *const argv[] = {"/bin/echo", "demo", NULL};
    execve("/bin/echo", argv, environ);
    perror("execve");
    return 1;
}
