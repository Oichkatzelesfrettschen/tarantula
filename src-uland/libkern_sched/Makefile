OBJS = kern_sched.o
LIB  = libkern_sched.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean

