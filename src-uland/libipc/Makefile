LIB  = libipc.a
LIBIPC_DIR = ../../src-lib/libipc
LIBIPC = $(LIBIPC_DIR)/libipc.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers
CFLAGS ?= -O2
CSTD ?= -std=c2x
CFLAGS += $(CSTD)

all: $(LIBIPC) $(LIB)

$(LIB): $(LIBIPC)
	cp $(LIBIPC) $(LIB)

$(LIBIPC):
	$(MAKE) -C $(LIBIPC_DIR)

clean:
	rm -f $(LIB)
	$(MAKE) -C $(LIBIPC_DIR) clean

.PHONY: all clean
