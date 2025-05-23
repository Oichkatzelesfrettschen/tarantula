# Simplified GNU makefile for the config utility
PROG = config
CFLAGS += -I. -I$(CURDIR)
SRCS = config.c main.c lang.c mkioconf.c mkmakefile.c mkglue.c mkheaders.c \
       mkswapconf.c
LDADD = -ll
CLEANFILES = y.tab.h lang.c config.c y.tab.c lex.yy.c

OBJS = $(SRCS:.c=.o)

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LDADD) -o $@

config.c y.tab.h: config.y
	$(YACC) -d $<
	mv y.tab.c config.c

lang.c: lang.l
	$(LEX) $<
	mv lex.yy.c lang.c

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(PROG) $(OBJS) $(CLEANFILES)

.PHONY: all clean
