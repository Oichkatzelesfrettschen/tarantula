project('kern_stubs', 'c', default_options : ['c_std=c23'])
add_project_arguments('-Wall', '-Werror', language : 'c')

srcs = ['proc_hooks.c', 'sched_hooks.c', 'vm_hooks.c', 'vfs_hooks.c']
srcs += ['ipc.c']
libkern = static_library('kern_stubs', srcs,
                         include_directories : include_directories('../src-headers'))

clangtidy = find_program('clang-tidy', required : false)
if clangtidy.found()
  foreach f : srcs
    run_target('tidy-' + f,
               command : [clangtidy, f, '--', '-I../src-headers'])
  endforeach
  run_target('tidy', command : ['true'])
endif
