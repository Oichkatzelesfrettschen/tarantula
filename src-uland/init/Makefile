SRCS = init.c
OBJS = $(SRCS:.c=.o)
PROG = init

CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c23
CPPFLAGS ?= -I../../src-headers
CFLAGS += $(CSTD) -Wall -Werror

SUBDIRS = ../servers/reincarnation

all: $(PROG) subdirs

subdirs:
	$(MAKE) -C $(SUBDIRS)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)
	$(MAKE) -C $(SUBDIRS) clean

.PHONY: all clean subdirs
