project('tarantula', 'c', default_options : ['c_std=c23'])

bison = find_program('bison', required : false)
if not bison.found()
  warning('bison not found; some tools may not build')
endif

libipc = static_library('ipc', 'src-lib/libipc/ipc.c',
                        include_directories : include_directories('src-headers'))

kern_srcs = [
  'src-kernel/proc_hooks.c',
  'src-kernel/sched_hooks.c',
  'src-kernel/vm_hooks.c',
  'src-kernel/vfs_hooks.c',
]
libkern = static_library('kern_stubs', kern_srcs,
                         include_directories : include_directories('src-headers'),
                         dependencies : libipc)

fs_srcs = files(
  'src-uland/fs-server/fs_open.c',
  'src-uland/fs-server/vfs_bio.c',
  'src-uland/fs-server/vfs_cache.c',
  'src-uland/fs-server/vfs_cluster.c',
  'src-uland/fs-server/vfs_conf.c',
  'src-uland/fs-server/vfs_init.c',
  'src-uland/fs-server/vfs_lookup.c',
  'src-uland/fs-server/vfs_subr.c',
  'src-uland/fs-server/vfs_syscalls.c',
  'src-uland/fs-server/vfs_vnops.c'
)
executable('fs_server', fs_srcs,
           include_directories : include_directories('src-headers',
                                                    'src-headers/machine',
                                                    'sys',
                                                    'sys/sys',
                                                    'sys/i386/include'),
           c_args : ['-DKERNEL'],
           link_with : libipc)

