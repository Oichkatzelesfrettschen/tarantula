#include "posix.h"
#include <string.h>
#include <stdio.h>
#include <fcntl.h>

int main(void)
{
    if (mkfifo("fifo1", 3) != 0) {
        perror("mkfifo");
        return 1;
    }

    int w = posix_open("fifo1", O_WRONLY);
    int r = posix_open("fifo1", O_RDONLY);
    if (w < 0 || r < 0) {
        perror("posix_open");
        return 1;
    }

    const char msg[] = "hello";
    if (posix_write(w, msg, sizeof(msg)) != sizeof(msg)) {
        fprintf(stderr, "write failed\n");
        return 1;
    }

    char buf[16];
    if (posix_read(r, buf, sizeof(msg)) != sizeof(msg)) {
        fprintf(stderr, "read failed\n");
        return 1;
    }

    if (memcmp(buf, msg, sizeof(msg)) != 0) {
        fprintf(stderr, "data mismatch\n");
        return 1;
    }

    posix_close(w);
    posix_close(r);
    return 0;
}
