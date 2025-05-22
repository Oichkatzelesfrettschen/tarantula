OBJS = ipc.o
LIB  = libipc.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-kernel
CFLAGS ?= -O2
CLANG_TIDY ?= ../../tools/run_clang_tidy.sh

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean tidy

tidy:
	$(CLANG_TIDY) $(OBJS:.o=.c) -- $(CC) $(CPPFLAGS) $(CFLAGS)
