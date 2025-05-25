LIB = libvm.a
LIBDIR = ../../src-lib/libvm
LIBFILE = $(LIBDIR)/libvm.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
        -I../../sys -I../../sys/sys \
        -I../../sys/i386/include
CFLAGS ?= -O2
CSTD ?= -std=c23
CFLAGS += $(CSTD) -DKERNEL -Wall -Werror

all: $(LIBFILE) $(LIB)

$(LIB): $(LIBFILE)
cp $(LIBFILE) $(LIB)

$(LIBFILE):
$(MAKE) -C $(LIBDIR)

clean:
rm -f $(LIB)
$(MAKE) -C $(LIBDIR) clean

.PHONY: all clean
