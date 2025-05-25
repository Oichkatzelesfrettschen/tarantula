LIB  = libcapnp.a
LIBDIR = ../../src-lib/libcapnp
LIBFILE = $(LIBDIR)/libcapnp.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers
CFLAGS ?= -O2
CSTD ?= -std=c2x
CFLAGS += $(CSTD)
CAPNP_LIBS ?= $(shell pkg-config --libs capnp 2>/dev/null)

all: $(LIBFILE) $(LIB)

$(LIB): $(LIBFILE)
cp $(LIBFILE) $(LIB)

$(LIBFILE):
$(MAKE) -C $(LIBDIR)

clean:
rm -f $(LIB)
$(MAKE) -C $(LIBDIR) clean

.PHONY: all clean
