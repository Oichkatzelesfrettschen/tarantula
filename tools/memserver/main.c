#include <stdio.h>
#include <stdlib.h>
#include "../../third_party/libcapnp/message.h"

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <file>\n", argv[0]);
        return 1;
    }

    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        perror("fopen");
        return 1;
    }
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = malloc(size);
    if (!buf) {
        fclose(f);
        return 1;
    }
    fread(buf, 1, size, f);
    fclose(f);

    struct capnp_message msg;
    capnp_parse(buf, size, &msg);
    printf("parsed message of %zu bytes\n", msg.size);

    free(buf);
    return 0;
}
