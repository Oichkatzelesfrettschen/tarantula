# Simplified GNU makefile for the config utility
PROG = config
CFLAGS += -I. -I$(CURDIR)
SRCS = config.c main.c lang.c mkioconf.c mkmakefile.c mkglue.c mkheaders.c \
       mkswapconf.c
LDADD = -ll
CLEANFILES = y.tab.h lang.c config.c y.tab.c

OBJS = $(SRCS:.c=.o)

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LDADD) -o $@

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(PROG) $(OBJS) $(CLEANFILES)

.PHONY: all clean
