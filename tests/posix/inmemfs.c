#include "../../include/dirent.h"
#include <stdlib.h>
#include <string.h>

DIR *memfs_opendir(const char **names, size_t count)
{
    DIR *d = malloc(sizeof(DIR));
    if (!d)
        return NULL;
    d->pos = 0;
    d->count = count;
    d->names = names;
    return d;
}

struct dirent *memfs_readdir(DIR *d)
{
    static struct dirent de;
    if (d->pos >= d->count)
        return NULL;
    strncpy(de.d_name, d->names[d->pos], MAXNAMLEN);
    de.d_name[MAXNAMLEN] = '\0';
    d->pos++;
    return &de;
}

int memfs_closedir(DIR *d)
{
    free(d);
    return 0;
}
