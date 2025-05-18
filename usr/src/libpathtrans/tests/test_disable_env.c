#include <stdio.h>
#include <sys/stat.h>

int main(void) {
    struct stat st;
    if (stat("/tmp/pathtrans_test/orig/file.txt", &st) == 0) {
        fprintf(stderr, "unexpected success\n");
        return 1;
    }
    return 0;
}
