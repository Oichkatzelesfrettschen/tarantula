# Timer Library

The timer library implements a small wrapper around `nanosleep()` and
records the total time each process has slept.  The implementation lives
in `src-lib/libtimer/timer.c` with headers under `src-headers/timer.h`.

## Usage

Call `timer_init()` once at startup.  Use `nanosleep()` as usual.  The
nanoseconds a process has slept can be queried with
`timer_get_sleep(pid)`.
