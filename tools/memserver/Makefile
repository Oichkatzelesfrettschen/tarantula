CC ?= cc
CPPFLAGS ?= -I../../third_party/libcapnp
CFLAGS ?= -O2 -std=c23 -Wall -Werror
LIBS = ../../third_party/libcapnp/libcapnp.a

all: memserver

memserver: main.o $(LIBS)
$(CC) $(CFLAGS) main.o $(LIBS) -o $@

main.o: main.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f main.o memserver

.PHONY: all clean
