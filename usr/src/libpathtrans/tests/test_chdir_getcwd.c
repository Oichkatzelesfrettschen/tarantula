#include <stdio.h>
#include <unistd.h>
#include <string.h>

int main(void) {
    char buf[256];
    if (chdir("/tmp/pathtrans_test/orig") != 0) {
        perror("chdir");
        return 1;
    }
    if (!getcwd(buf, sizeof(buf))) {
        perror("getcwd");
        return 1;
    }
    if (strstr(buf, "/tmp/pathtrans_test/new") != buf) {
        fprintf(stderr, "unexpected cwd: %s\n", buf);
        return 1;
    }
    return 0;
}
