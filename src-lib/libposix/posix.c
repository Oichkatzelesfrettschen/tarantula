#include "posix.h"
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#define MAX_FDS 32
#define MAX_FIFOS 16
#define FIFO_BUF_SIZE 1024

enum fd_type { FD_NONE = 0, FD_FILE, FD_FIFO };

struct fifo {
    char *buf;
    size_t size;
    size_t rpos;
    size_t wpos;
    int refs;
    int perm; /* bitmask: 1=read 2=write */
    const char *name;
};

struct fd_entry {
    enum fd_type type;
    int perm;
    union {
        int file;
        struct fifo *fifo;
    } u;
};

static struct fifo fifos[MAX_FIFOS];
static struct fd_entry fds[MAX_FDS];

static struct fifo *find_fifo(const char *path)
{
    for (int i = 0; i < MAX_FIFOS; ++i) {
        if (fifos[i].name && strcmp(fifos[i].name, path) == 0)
            return &fifos[i];
    }
    return NULL;
}

int mkfifo(const char *path, int perm)
{
    if (find_fifo(path))
        return -1;
    for (int i = 0; i < MAX_FIFOS; ++i) {
        if (!fifos[i].name) {
            fifos[i].buf = malloc(FIFO_BUF_SIZE);
            if (!fifos[i].buf)
                return -1;
            fifos[i].size = FIFO_BUF_SIZE;
            fifos[i].rpos = fifos[i].wpos = 0;
            fifos[i].refs = 0;
            fifos[i].perm = perm;
            fifos[i].name = strdup(path);
            return 0;
        }
    }
    return -1;
}

static int alloc_fd(void)
{
    for (int i = 0; i < MAX_FDS; ++i) {
        if (fds[i].type == FD_NONE) {
            return i;
        }
    }
    return -1;
}

int posix_open(const char *path, int flags)
{
    struct fifo *f = find_fifo(path);
    int perm = 0;
    if ((flags & O_ACCMODE) == O_RDONLY)
        perm = 1;
    else if ((flags & O_ACCMODE) == O_WRONLY)
        perm = 2;
    else
        perm = 3;

    int fd = alloc_fd();
    if (fd < 0)
        return -1;

    if (f) {
        if ((perm & f->perm) != perm)
            return -1;
        fds[fd].type = FD_FIFO;
        fds[fd].perm = perm;
        fds[fd].u.fifo = f;
        f->refs++;
        return fd;
    }

    int realfd = open(path, flags, 0);
    if (realfd < 0)
        return -1;
    fds[fd].type = FD_FILE;
    fds[fd].perm = perm;
    fds[fd].u.file = realfd;
    return fd;
}

int posix_dup(int fd)
{
    if (fd < 0 || fd >= MAX_FDS || fds[fd].type == FD_NONE)
        return -1;
    int newfd = alloc_fd();
    if (newfd < 0)
        return -1;
    fds[newfd] = fds[fd];
    if (fds[fd].type == FD_FILE) {
        int dupfd = dup(fds[fd].u.file);
        if (dupfd < 0)
            return -1;
        fds[newfd].u.file = dupfd;
    } else if (fds[fd].type == FD_FIFO) {
        fds[fd].u.fifo->refs++;
    }
    return newfd;
}

static size_t fifo_available(struct fifo *f)
{
    return f->wpos - f->rpos;
}

static size_t fifo_space(struct fifo *f)
{
    return f->size - (f->wpos - f->rpos);
}

static ssize_t fifo_read(struct fifo *f, void *buf, size_t n)
{
    size_t avail = fifo_available(f);
    if (avail == 0)
        return 0;
    if (n > avail)
        n = avail;
    for (size_t i = 0; i < n; ++i)
        ((char *)buf)[i] = f->buf[(f->rpos + i) % f->size];
    f->rpos += n;
    if (f->rpos >= f->size) {
        f->rpos %= f->size;
        f->wpos %= f->size;
    }
    return (ssize_t)n;
}

static ssize_t fifo_write(struct fifo *f, const void *buf, size_t n)
{
    size_t space = fifo_space(f);
    if (space == 0)
        return 0;
    if (n > space)
        n = space;
    for (size_t i = 0; i < n; ++i)
        f->buf[(f->wpos + i) % f->size] = ((const char *)buf)[i];
    f->wpos += n;
    if (f->wpos >= f->size) {
        f->rpos %= f->size;
        f->wpos %= f->size;
    }
    return (ssize_t)n;
}

ssize_t posix_read(int fd, void *buf, size_t n)
{
    if (fd < 0 || fd >= MAX_FDS || fds[fd].type == FD_NONE)
        return -1;
    if (!(fds[fd].perm & 1))
        return -1;
    if (fds[fd].type == FD_FILE)
        return read(fds[fd].u.file, buf, n);
    return fifo_read(fds[fd].u.fifo, buf, n);
}

ssize_t posix_write(int fd, const void *buf, size_t n)
{
    if (fd < 0 || fd >= MAX_FDS || fds[fd].type == FD_NONE)
        return -1;
    if (!(fds[fd].perm & 2))
        return -1;
    if (fds[fd].type == FD_FILE)
        return write(fds[fd].u.file, buf, n);
    return fifo_write(fds[fd].u.fifo, buf, n);
}

int posix_close(int fd)
{
    if (fd < 0 || fd >= MAX_FDS || fds[fd].type == FD_NONE)
        return -1;
    if (fds[fd].type == FD_FILE) {
        close(fds[fd].u.file);
    } else if (fds[fd].type == FD_FIFO) {
        if (--fds[fd].u.fifo->refs == 0) {
            free(fds[fd].u.fifo->buf);
            free((char *)fds[fd].u.fifo->name);
            memset(fds[fd].u.fifo, 0, sizeof(struct fifo));
        }
    }
    fds[fd].type = FD_NONE;
    return 0;
}

