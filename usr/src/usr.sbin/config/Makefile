# 4.4BSD style Makefile for the config utility

PROG=   config
SRCS=   config.c main.c lang.c mkioconf.c mkmakefile.c mkglue.c mkheaders.c \
        mkswapconf.c mkubglue.c
CFLAGS+=-I${.CURDIR} -I.
DPADD=  ${LIBL}
LDADD=  -ll
CLEANFILES=config.c y.tab.c y.tab.h lang.c lex.yy.c

config.c y.tab.h: config.y
        ${YACC} -d ${.CURDIR}/config.y
        mv y.tab.c config.c

lang.c: lang.l
        ${LEX} ${.CURDIR}/lang.l
        mv lex.yy.c lang.c

.include <bsd.prog.mk>
