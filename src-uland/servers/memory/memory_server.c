#include <stdio.h>
#include <unistd.h>
#include "libcapnp.h"

int main(void)
{
    char buf[128];
    ssize_t n = read(STDIN_FILENO, buf, sizeof(buf));
    if (n <= 0)
        return 1;

    struct capnp_request req;
    if (!capnp_parse_request(buf, (size_t)n, &req)) {
        fprintf(stderr, "capnp parse failed\n");
        return 1;
    }

    printf("request id %u\n", req.id);
    return 0;
}
