#include <stdio.h>
#include <unistd.h>

extern char **environ;

int main(void) {
    const char *prog = "/tmp/pathtrans_test/orig/prog.sh";
    char *const argv[] = {(char *)prog, NULL};
    execve(prog, argv, environ);
    perror("execve");
    return 1;
}
