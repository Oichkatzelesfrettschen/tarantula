
.PHONY: all inventory test

CFLAGS ?= -O2 -std=c23 -Wall -Werror
CXXFLAGS ?= -O2 -std=c++23 -Wall -Werror

SUBDIRS = \
    src-lib/libipc \
    src-lib/libkern_sched \
    src-lib/libvm \
    src-kernel \
    src-uland/libipc \
    src-uland/libkern_sched \
    src-uland/libvm \
    src-uland/fs-server \
    src-uland/servers/proc_manager \
    src-uland/init \
    tests

all:
	@for dir in $(SUBDIRS); do \
	$(MAKE) -C $$dir CPPFLAGS="$(CPPFLAGS)" CFLAGS="$(CFLAGS)"; \
	done

inventory:
	python3 tools/create_inventory.py

test:
	$(MAKE) -C tests
