SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
LIB  = libvm.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
            -I../../include -I../../sys -I../../sys/sys \
            -I../../sys/i386/include

all: $(LIB)

$(LIB): $(OBJS)
        $(AR) rcs $@ $(OBJS)

%.o: %.c
        $(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean
