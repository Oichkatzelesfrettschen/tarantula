CC ?= cc
CPPFLAGS ?= -I../../third_party/libcapnp
CFLAGS ?= -O2 -std=c23 -Wall -Werror
LIBS = ../../third_party/libcapnp/libcapnp.a

all: memserver_test mprotect_demo

memserver_test: memserver_test.o $(LIBS)
$(CC) $(CFLAGS) memserver_test.o $(LIBS) -o $@

mprotect_demo: mprotect_demo.o ../../src-lib/posix/libposix.a
$(CC) $(CFLAGS) mprotect_demo.o ../../src-lib/posix/libposix.a -o $@

memserver_test.o: memserver_test.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

mprotect_demo.o: mprotect_demo.c
$(CC) -I../../src-headers -I../../include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f memserver_test.o memserver_test mprotect_demo.o mprotect_demo

.PHONY: all clean
