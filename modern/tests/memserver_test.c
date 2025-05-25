#include "../../third_party/libcapnp/message.h"
#include <assert.h>
#include <string.h>

int main(void)
{
    const char data[] = "abc";
    struct capnp_message msg;
    capnp_parse(data, sizeof(data)-1, &msg);
    assert(msg.size == sizeof(data)-1);
    assert(memcmp(msg.data, "abc", 3) == 0);
    return 0;
}
