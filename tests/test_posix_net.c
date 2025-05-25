#include "posix_helpers.h"
#include <assert.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>

int main(void) {
    int s = socket(AF_INET, SOCK_STREAM, 0);
    assert(s >= 0);

    int val = 1;
    assert(posix_setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &val, sizeof(val)) == 0);

    int got = 0; socklen_t len = sizeof(got);
    assert(posix_getsockopt(s, SOL_SOCKET, SO_REUSEADDR, &got, &len) == 0);
    assert(got == val);

    struct in_addr addr;
    assert(posix_inet_pton(AF_INET, "127.0.0.1", &addr) == 1);
    char buf[INET_ADDRSTRLEN];
    assert(posix_inet_ntop(AF_INET, &addr, buf, sizeof(buf)) != NULL);
    assert(strcmp(buf, "127.0.0.1") == 0);

    close(s);
    return 0;
}
