SRCS = init.c
OBJS = $(SRCS:.c=.o)
PROG = init

CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c2x
CPPFLAGS ?= -I../../src-headers
CFLAGS += $(CSTD)

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean
