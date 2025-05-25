#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

int main(void) {
    const char *orig = "/tmp/pathtrans_test/orig/file.txt";
    const char *linkpath = "/tmp/pathtrans_test/orig/link.txt";
    if (link(orig, linkpath) != 0) {
        perror("link");
        return 1;
    }
    struct stat st;
    if (stat(linkpath, &st) != 0) {
        perror("stat link");
        return 1;
    }
    if (unlink(linkpath) != 0) {
        perror("unlink");
        return 1;
    }
    return 0;
}
