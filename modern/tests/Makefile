CC ?= cc
CPPFLAGS ?= -I../../src-headers -I../../third_party/libcapnp
CFLAGS ?= -O2 -std=c23 -Wall -Werror
LIBS = ../../third_party/libcapnp/libcapnp.a

all: memserver_test posix_ipc_demo

memserver_test: memserver_test.o $(LIBS)
$(CC) $(CFLAGS) memserver_test.o $(LIBS) -o $@

memserver_test.o: memserver_test.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

posix_ipc_demo: posix_ipc_demo.o
$(CC) $(CFLAGS) posix_ipc_demo.o -lrt -o $@

posix_ipc_demo.o: posix_ipc_demo.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f memserver_test.o memserver_test posix_ipc_demo.o posix_ipc_demo

.PHONY: all clean
