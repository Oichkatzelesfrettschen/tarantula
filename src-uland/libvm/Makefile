LIB = libvm.a
LIBDIR = ../../src-lib/libvm
LIBFILE = $(LIBDIR)/libvm.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
        -I../../sys -I../../sys/sys \
        -I../../sys/i386/include
CFLAGS ?= -O2
CSTD ?= -std=c2x
CFLAGS += $(CSTD) -DKERNEL
CAPNP_LIBS ?= $(shell pkg-config --libs capnp 2>/dev/null)

all: $(LIBFILE) $(LIB)

$(LIB): $(LIBFILE)
cp $(LIBFILE) $(LIB)
ifneq ($(CAPNP_LIBS),)
$(CC) -shared $(LIBFILE) $(CAPNP_LIBS) -o $(LIB:.a=.so)
endif

$(LIBFILE):
$(MAKE) -C $(LIBDIR)

clean:
rm -f $(LIB)
$(MAKE) -C $(LIBDIR) clean

.PHONY: all clean
