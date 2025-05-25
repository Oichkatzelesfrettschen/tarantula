LIB = libtimer.a
LIBDIR = ../../src-lib/libtimer
LIBFILE = $(LIBDIR)/libtimer.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers -I../../include
CFLAGS ?= -O2
CSTD ?= -std=c23
CFLAGS += $(CSTD) -Wall -Werror

all: $(LIBFILE) $(LIB)

$(LIB): $(LIBFILE)
cp $(LIBFILE) $(LIB)

$(LIBFILE):
$(MAKE) -C $(LIBDIR)

clean:
rm -f $(LIB)
$(MAKE) -C $(LIBDIR) clean

.PHONY: all clean
