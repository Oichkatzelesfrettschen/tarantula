# POSIX Compatibility Notes

This repository provides a minimal pthread implementation under
`src-lib/pthread`.  The current code uses `fork()` and `waitpid()` to
simulate thread creation and joining.  Only `pthread_create()` and
`pthread_join()` are available and thread attributes are ignored.

This stub is sufficient for simple test programs but lacks most of the
POSIX thread semantics such as detached state, mutexes and condition
variables.  Future work may replace the process based approach with a
true threading model.
