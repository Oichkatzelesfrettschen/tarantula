SRCS = memory_server.c
OBJS = $(SRCS:.c=.o)
PROG = memory_server

CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c2x
CPPFLAGS ?= -I../../../src-headers
CFLAGS += $(CSTD)
CAPNP_LIBS ?= $(shell pkg-config --libs capnp 2>/dev/null)
LIBS = ../../libcapnp/libcapnp.a $(CAPNP_LIBS)

all: $(PROG)

$(PROG): $(OBJS)
$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) $(LIBS) -o $@

%.o: %.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f $(OBJS) $(PROG)

.PHONY: all clean
