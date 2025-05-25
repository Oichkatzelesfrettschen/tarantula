LIB  = libposix.a
DIR = ../../src-lib/libposix
LIBFILE = $(DIR)/libposix.a

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
	$(MAKE) -C $(DIR)

clean:
	rm -f $(LIB)
	$(MAKE) -C $(DIR) clean

.PHONY: all clean
