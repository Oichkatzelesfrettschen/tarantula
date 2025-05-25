#include "libcapnp.h"
#include <string.h>

bool capnp_parse_request(const void *data, size_t len, struct capnp_request *out)
{
    if (!data || !out)
        return false;

#ifdef HAVE_CAPNP
    /* Real parsing would use Cap'n Proto here. */
    (void)len;
    /* TODO: implement using capnp library */
    out->id = 0;
    return true;
#else
    /* Simplistic stub: accept "id=<num>" text */
    const char *buf = data;
    if (len > 4 && memcmp(buf, "id=", 3) == 0) {
        out->id = (unsigned)atoi(buf + 3);
        return true;
    }
    return false;
#endif
}
