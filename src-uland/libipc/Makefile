OBJS = ipc.o
LIB  = libipc.a

CC ?= cc
AR ?= ar
CPPFLAGS ?= -I../../src-kernel
CFLAGS ?= -O2

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean
