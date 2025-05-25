OBJS = posix.o posix_signal.o
LIB  = libposix.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-headers -I../../include
CFLAGS ?= -O2
CSTD ?= -std=c23
CFLAGS += $(CSTD) -Wall -Werror

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean
