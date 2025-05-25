#include "message.h"

int capnp_parse(const char *buf, size_t size, struct capnp_message *msg)
{
    msg->data = buf;
    msg->size = size;
    return 0;
}
