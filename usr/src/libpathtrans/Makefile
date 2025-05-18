CC = gcc
CFLAGS = -Wall -Wextra -fPIC -O2 -D_GNU_SOURCE
LDFLAGS = -shared -ldl -lpthread

# Allow callers to pass additional flags, e.g. -m32 or -m64
CFLAGS += $(CFLAGS_EXTRA)
LDFLAGS += $(LDFLAGS_EXTRA)
INCLUDES = -Iinclude

SRC_DIR = src
BUILD_DIR = build
INCLUDE_DIR = include
TEST_DIR = tests
TOOL_DIR = tools

LIB = libpathtrans.so

SRCS = $(wildcard $(SRC_DIR)/*.c)
OBJS = $(patsubst $(SRC_DIR)/%.c,$(BUILD_DIR)/%.o,$(SRCS))

all: directories $(LIB) tools tests

directories:
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

$(LIB): $(OBJS)
	$(CC) $(LDFLAGS) -o $@ $^

tools: $(LIB)
	$(MAKE) -C $(TOOL_DIR) \
                CFLAGS_EXTRA="$(CFLAGS_EXTRA)" LDFLAGS_EXTRA="$(LDFLAGS_EXTRA)"

tests: $(LIB)
	$(MAKE) -C $(TEST_DIR) \
                CFLAGS_EXTRA="$(CFLAGS_EXTRA)" LDFLAGS_EXTRA="$(LDFLAGS_EXTRA)"

clean:
	rm -rf $(BUILD_DIR) $(LIB)
	$(MAKE) -C $(TOOL_DIR) clean
	$(MAKE) -C $(TEST_DIR) clean

install: $(LIB)
	mkdir -p $(DESTDIR)/usr/lib
	mkdir -p $(DESTDIR)/usr/bin
	mkdir -p $(DESTDIR)/etc/pathtrans
	install -m 755 $(LIB) $(DESTDIR)/usr/lib/
	install -m 755 $(TOOL_DIR)/pathtrans_db $(DESTDIR)/usr/bin/
	install -m 644 config/config.conf $(DESTDIR)/etc/pathtrans/

.PHONY: all directories tools tests clean install
