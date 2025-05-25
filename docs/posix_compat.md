# POSIX Compatibility Helpers

This short library exposes wrappers around common networking functions.
It lives under `src-lib/libposix` and installs the header
`posix_helpers.h` in `src-headers/`.

## API

```
int posix_setsockopt(int fd, int level, int optname,
                     const void *optval, socklen_t optlen);
int posix_getsockopt(int fd, int level, int optname,
                     void *optval, socklen_t *optlen);
int posix_inet_pton(int af, const char *src, void *dst);
const char *posix_inet_ntop(int af, const void *src,
                            char *dst, socklen_t size);
```

The functions simply forward to the host system's `setsockopt`,
`getsockopt`, `inet_pton` and `inet_ntop`.  They provide a stable
interface for the microkernel tests without relying on the full C
library.
