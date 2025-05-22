SRCS = fs_open.c $(wildcard vfs_*.c)
OBJS = $(SRCS:.c=.o)
PROG = fs_server

CC ?= cc
CFLAGS ?= -O2
CLANG_TIDY ?= ../../tools/run_clang_tidy.sh
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
            -I../../include -I../../sys -I../../sys/sys \
            -I../../sys/i386/include
CFLAGS   += -DKERNEL

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)


.PHONY: all clean tidy

tidy:
	$(CLANG_TIDY) $(SRCS) -- $(CC) $(CPPFLAGS) $(CFLAGS)
