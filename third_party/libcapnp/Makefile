OBJS = message.o
LIB  = libcapnp.a

CC ?= cc
AR ?= ar
CPPFLAGS ?=
CFLAGS ?= -O2 -std=c23 -Wall -Werror

all: $(LIB)

$(LIB): $(OBJS)
$(AR) rcs $@ $(OBJS)

%.o: %.c
$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f $(OBJS) $(LIB)

.PHONY: all clean
