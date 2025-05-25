#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#include "path_database.h"

static int (*real_open)(const char *, int, ... ) = NULL;
static int (*real_stat)(const char *, struct stat *) = NULL;
static int (*real_link)(const char *, const char *) = NULL;
static int (*real_unlink)(const char *) = NULL;
static char *(*real_getcwd)(char *, size_t) = NULL;
static int (*real_chdir)(const char *) = NULL;
static int (*real_execve)(const char *, char *const [], char *const []) = NULL;

static __thread int translation_disabled = 0;

static int is_disabled(void) {
    const char *env = getenv("PATHTRANS_DISABLE");
    return translation_disabled || (env && strcmp(env, "1") == 0);
}

__attribute__((constructor))
static void init(void) {
    real_open = dlsym(RTLD_NEXT, "open");
    real_stat = dlsym(RTLD_NEXT, "stat");
    real_link = dlsym(RTLD_NEXT, "link");
    real_unlink = dlsym(RTLD_NEXT, "unlink");
    real_getcwd = dlsym(RTLD_NEXT, "getcwd");
    real_chdir = dlsym(RTLD_NEXT, "chdir");
    real_execve = dlsym(RTLD_NEXT, "execve");
    path_database_init();
}

__attribute__((destructor))
static void fini(void) {
    path_database_cleanup();
}

int open(const char *pathname, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, int);
        va_end(ap);
    }

    const char *use_path = pathname;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(pathname)) {
        if (translate_path(pathname, buf, sizeof(buf))) {
            use_path = buf;
        }
    }

    int ret;
    translation_disabled = 1;
    if (flags & O_CREAT)
        ret = real_open(use_path, flags, mode);
    else
        ret = real_open(use_path, flags);
    translation_disabled = 0;
    return ret;
}

int stat(const char *pathname, struct stat *statbuf) {
    const char *use_path = pathname;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(pathname)) {
        if (translate_path(pathname, buf, sizeof(buf))) {
            use_path = buf;
        }
    }

    int ret;
    translation_disabled = 1;
    ret = real_stat(use_path, statbuf);
    translation_disabled = 0;
    return ret;
}

int link(const char *oldpath, const char *newpath) {
    const char *use_old = oldpath;
    const char *use_new = newpath;
    char buf_old[MAX_PATH_LENGTH];
    char buf_new[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(oldpath)) {
        if (translate_path(oldpath, buf_old, sizeof(buf_old)))
            use_old = buf_old;
    }
    if (!is_disabled() && path_needs_translation(newpath)) {
        if (translate_path(newpath, buf_new, sizeof(buf_new)))
            use_new = buf_new;
    }
    int ret;
    translation_disabled = 1;
    ret = real_link(use_old, use_new);
    translation_disabled = 0;
    return ret;
}

int unlink(const char *pathname) {
    const char *use_path = pathname;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(pathname)) {
        if (translate_path(pathname, buf, sizeof(buf)))
            use_path = buf;
    }
    int ret;
    translation_disabled = 1;
    ret = real_unlink(use_path);
    translation_disabled = 0;
    return ret;
}

char *getcwd(char *buf, size_t size) {
    char *ret;
    translation_disabled = 1;
    ret = real_getcwd(buf, size);
    translation_disabled = 0;
    return ret;
}

int chdir(const char *path) {
    const char *use_path = path;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(path)) {
        if (translate_path(path, buf, sizeof(buf)))
            use_path = buf;
    }
    int ret;
    translation_disabled = 1;
    ret = real_chdir(use_path);
    translation_disabled = 0;
    return ret;
}

int execve(const char *pathname, char *const argv[], char *const envp[]) {
    const char *use_path = pathname;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(pathname)) {
        if (translate_path(pathname, buf, sizeof(buf)))
            use_path = buf;
    }
    int ret;
    translation_disabled = 1;
    ret = real_execve(use_path, argv, envp);
    translation_disabled = 0;
    return ret;
}

