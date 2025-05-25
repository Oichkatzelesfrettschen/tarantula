OBJS = pthread.o
LIB  = libpthread_compat.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2
CSTD ?= -std=c23
CPPFLAGS ?= -I../../src-headers
CFLAGS   += $(CSTD) -Wall -Werror

all: $(LIB)

$(LIB): $(OBJS)
$(AR) rcs $@ $(OBJS)

%.o: %.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f $(OBJS) $(LIB)

.PHONY: all clean
