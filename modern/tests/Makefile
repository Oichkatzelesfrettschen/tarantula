CC ?= cc
CPPFLAGS ?= -I../../third_party/libcapnp
CFLAGS ?= -O2 -std=c23 -Wall -Werror
LIBS = ../../third_party/libcapnp/libcapnp.a

all: memserver_test

memserver_test: memserver_test.o $(LIBS)
$(CC) $(CFLAGS) memserver_test.o $(LIBS) -o $@

memserver_test.o: memserver_test.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f memserver_test.o memserver_test

.PHONY: all clean
