OBJS = posix_helpers.o
LIB = libposix.a
CFLAGS ?= -O2 -std=c23 -Wall -Werror -I../../src-headers

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean
