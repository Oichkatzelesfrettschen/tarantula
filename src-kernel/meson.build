project('kern_stubs', 'c', default_options : ['c_std=c23'])

srcs = ['sched_hooks.c', 'vm_hooks.c', 'vfs_hooks.c']
libkern = static_library('kern_stubs', srcs,
                         include_directories : include_directories('../include'))

clangtidy = find_program('clang-tidy', required : false)
if clangtidy.found()
  foreach f : srcs
    run_target('tidy-' + f,
               command : [clangtidy, f, '--', '-I../include'])
  endforeach
  run_target('tidy', command : ['true'])
endif
