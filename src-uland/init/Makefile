SRCS = init.c
OBJS = $(SRCS:.c=.o)
PROG = init

CC ?= cc
CFLAGS ?= -O2
CLANG_TIDY ?= ../../tools/run_clang_tidy.sh

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean tidy

tidy:
	$(CLANG_TIDY) $(SRCS) -- $(CC) $(CPPFLAGS) $(CFLAGS)
