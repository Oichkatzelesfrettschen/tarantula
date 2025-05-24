SRCS = reincarnation.c
OBJS = $(SRCS:.c=.o)
PROG = reincarnation

CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c2x
CPPFLAGS ?= -I../../../src-headers -I../../libipc
CFLAGS += $(CSTD)

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) ../../libipc/libipc.a -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean
