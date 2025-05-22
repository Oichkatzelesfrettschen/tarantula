OBJS = proc_hooks.o sched_hooks.o vm_hooks.o vfs_hooks.o
LIB = libkern_stubs.a

CC ?= cc
AR ?= ar
CLANG_TIDY ?= clang-tidy
CFLAGS ?= -O2 -std=c2x

all: $(LIB)
	
$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)
	
%.o: %.c
	@$(CLANG_TIDY) $< -- $(CC) $(CFLAGS) || true
	$(CC) $(CFLAGS) -c $< -o $@
	
clean:
	rm -f $(OBJS) $(LIB)
	
tidy:
	$(CLANG_TIDY) $(OBJS:.o=.c) -- $(CC) $(CFLAGS)
