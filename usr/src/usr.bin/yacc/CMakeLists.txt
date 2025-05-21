cmake_minimum_required(VERSION 3.10)
project(yacc C)
add_executable(yacc
    closure.c error.c lalr.c lr0.c main.c mkpar.c
    output.c reader.c skeleton.c symtab.c verbose.c warshall.c)
install(TARGETS yacc DESTINATION bin)
