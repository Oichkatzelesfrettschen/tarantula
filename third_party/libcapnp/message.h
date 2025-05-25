#ifndef CAPNP_MESSAGE_H
#define CAPNP_MESSAGE_H

#include <stddef.h>

struct capnp_message {
    const char *data;
    size_t size;
};

int capnp_parse(const char *buf, size_t size, struct capnp_message *msg);

#endif /* CAPNP_MESSAGE_H */
