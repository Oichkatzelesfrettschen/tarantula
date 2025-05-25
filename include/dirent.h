#ifndef DIRENT_H
#define DIRENT_H
#include <stddef.h>

#define MAXNAMLEN 255

struct dirent {
    char d_name[MAXNAMLEN + 1];
};

typedef struct DIR {
    size_t pos;
    size_t count;
    const char **names;
} DIR;

DIR *memfs_opendir(const char **names, size_t count);
struct dirent *memfs_readdir(DIR *d);
int memfs_closedir(DIR *d);

#endif /* DIRENT_H */
