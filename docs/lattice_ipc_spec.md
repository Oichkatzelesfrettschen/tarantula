# Lattice IPC Specification

This document sketches a lattice-based capability system inspired by historical UNIX designs and modern research.

## Capability Tokens
- Each IPC channel is identified by a 128-bit token represented as an octonion.
- Tokens encode permissions and form a partially ordered set.  Channels may only be composed when their tokens satisfy the lattice relation `a \<= b`.

## Directed Acyclic Graph
- Processes connect through channels that form edges of a DAG.
- The kernel rejects any operation that would introduce a cycle in the wait-for graph.

## POSIX Mapping
- `open()` and `connect()` map to `lattice_connect()` which returns a channel handle.
- `read()` and `write()` become `lattice_recv()` and `lattice_send()`.
- `fork()` and `execve()` allocate fresh tokens for the child.

## Fast Path
- Active channels live in L1 cache friendly queues.
- Overflow falls back to shared L2 structures and finally to pageable buffers in L3.

This high level specification will evolve as the implementation grows.
