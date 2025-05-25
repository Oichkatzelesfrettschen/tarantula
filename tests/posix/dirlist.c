#include "../../include/dirent.h"
#include <stdio.h>

static const char *root_entries[] = {
    "foo.txt",
    "bar",
    "baz",
};

int main(void)
{
    DIR *d = memfs_opendir(root_entries, sizeof(root_entries)/sizeof(root_entries[0]));
    if (!d)
        return 1;
    struct dirent *de;
    while ((de = memfs_readdir(d)) != NULL)
        printf("%s\n", de->d_name);
    memfs_closedir(d);
    return 0;
}
