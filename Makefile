.PHONY: all inventory

SUBDIRS = \
    src-lib/libipc \
    src-kernel \
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
