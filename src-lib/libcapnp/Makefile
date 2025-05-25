OBJS = libcapnp.o
LIB = libcapnp.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2
CSTD ?= -std=c2x
CPPFLAGS ?= -I../../src-headers
CFLAGS += $(CSTD)
CAPNP_LIBS ?= $(shell pkg-config --libs capnp 2>/dev/null)

all: $(LIB)

$(LIB): $(OBJS)
$(AR) rcs $@ $(OBJS)

%.o: %.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f $(OBJS) $(LIB)

.PHONY: all clean
