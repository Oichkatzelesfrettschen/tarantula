#include <stdio.h>
#include <sys/stat.h>

int main(void) {
    struct stat st;
    if (stat("/tmp/pathtrans_test/orig/file.txt", &st) == 0) {
        printf("translated\n");
        return 0;
    }
    perror("stat");
    return 1;
}
