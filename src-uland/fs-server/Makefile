SRCS = $(wildcard vfs_*.c)
OBJS = $(SRCS:.c=.o)
PROG = fs_server

CC ?= cc
CFLAGS ?= -O2

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean
