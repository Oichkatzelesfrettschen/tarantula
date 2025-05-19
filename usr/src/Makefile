# Makefile for building additional components with GNU make

SUBDIRS := libpathtrans

all:
	@for d in $(SUBDIRS); do $(MAKE) -C $$d CC="$(CC)" CFLAGS_EXTRA="$(CFLAGS_EXTRA)"; done

clean:
	@for d in $(SUBDIRS); do $(MAKE) -C $$d clean CC="$(CC)" CFLAGS_EXTRA="$(CFLAGS_EXTRA)"; done

.PHONY: all clean $(SUBDIRS)
