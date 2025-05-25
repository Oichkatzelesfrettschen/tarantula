LIB  = libipc.a
LIBIPC_DIR = ../../src-lib/libipc
LIBIPC = $(LIBIPC_DIR)/libipc.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers -I../../include
CFLAGS ?= -O2
CSTD ?= -std=c23
CFLAGS += $(CSTD) -Wall -Werror

all: $(LIBIPC) $(LIB)

$(LIB): $(LIBIPC)
	cp $(LIBIPC) $(LIB)

$(LIBIPC):
	$(MAKE) -C $(LIBIPC_DIR)

clean:
	rm -f $(LIB)
	$(MAKE) -C $(LIBIPC_DIR) clean

.PHONY: all clean
