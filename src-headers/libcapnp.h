#ifndef LIBCAPNP_H
#define LIBCAPNP_H

#include <stddef.h>
#include <stdbool.h>

struct capnp_request {
    unsigned id;
};

bool capnp_parse_request(const void *data, size_t len, struct capnp_request *out);

#endif /* LIBCAPNP_H */
