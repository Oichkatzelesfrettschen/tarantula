SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
LIB  = libvm.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean
