#!/usr/bin/env python3
import os
import re
import argparse

# Default locations within this repository
# By default we scan the traditional tree along with the modern kernel and
# userland directories.
DEFAULT_BASE = ['usr/src', 'src-kernel', 'src-uland']
DEFAULT_MASTER = 'usr/src/sys/kern/syscalls.master'

INCLUDE_QUOTE_RE = re.compile(r'#include\s+"([^"]+)"')
INCLUDE_ANGLE_RE = re.compile(r'#include\s+<([^>]+)>')
SYSCALL_REGEX = re.compile(r'^\s*(\d+)\s+STD\s+\{\s*(?:int|void)\s+(\w+)\([^)]*\)\s*\}\s*(\w+)?')

FUNC_DEF_RE = re.compile(r'^\s*(?:[\w\*]+\s+)+'
                         r'([A-Za-z_][A-Za-z0-9_]*)\s*\([^;]*\)\s*\{')
FUNC_CALL_RE = re.compile(r'\b([A-Za-z_][A-Za-z0-9_]*)\s*\(')


EXTENSIONS = ('.c', '.h', '.s')


def gather_source_files(bases):
    """Return a list of source files under the given base directories."""
    source_files = []
    for base in bases:
        for root, _, files in os.walk(base):
            for f in files:
                if f.endswith(EXTENSIONS):
                    source_files.append(os.path.join(root, f))
    return source_files


def build_index(files, bases):
    """Map relative paths and basenames to full paths."""
    index = {}
    for path in files:
        # record by basename
        base = os.path.basename(path)
        index.setdefault(base, path)
        # record by path relative to each base
        for b in bases:
            if path.startswith(b + os.sep):
                rel = os.path.relpath(path, b)
                index.setdefault(rel, path)
    return index


def map_includes(files, index):
    edges = set()
    for path in files:
        try:
            with open(path, 'r', errors='ignore') as fh:
                for line in fh:
                    m = INCLUDE_QUOTE_RE.search(line)
                    if m:
                        inc = m.group(1)
                        local = os.path.normpath(os.path.join(os.path.dirname(path), inc))
                        target = index.get(local) or index.get(inc) or index.get(os.path.basename(inc))
                        if target:
                            edges.add((path, target))
                    m = INCLUDE_ANGLE_RE.search(line)
                    if m:
                        inc = m.group(1)
                        target = index.get(inc) or index.get(os.path.basename(inc))
                        if target:
                            edges.add((path, target))
        except OSError:
            continue
    return edges


def parse_syscalls(master_path, func_defs):
    edges = set()
    if not os.path.exists(master_path):
        return edges
    syscalls = []
    with open(master_path, 'r', errors='ignore') as fh:
        for line in fh:
            m = SYSCALL_REGEX.match(line)
            if m:
                num, func, alias = m.groups()
                name = alias or func
                syscalls.append((name, func))
    for name, func in syscalls:
        impl = func_defs.get(func)
        if impl:
            edges.add((f'syscall:{name}', impl))
    return edges


def extract_function_defs(files):
    defs = {}
    for path in files:
        if not path.endswith('.c'):
            continue
        try:
            with open(path, 'r', errors='ignore') as fh:
                for line in fh:
                    m = FUNC_DEF_RE.match(line)
                    if m:
                        name = m.group(1)
                        defs.setdefault(name, path)
        except OSError:
            continue
    return defs


def map_function_calls(files, func_defs):
    edges = set()
    for path in files:
        if not path.endswith('.c'):
            continue
        try:
            with open(path, 'r', errors='ignore') as fh:
                for line in fh:
                    for m in FUNC_CALL_RE.finditer(line):
                        name = m.group(1)
                        target = func_defs.get(name)
                        if target and target != path:
                            edges.add((path, target))
        except OSError:
            continue
    return edges




def main():
    parser = argparse.ArgumentParser(
        description=(
            'Generate a dependency graph. By default the script scans '
            'usr/src, src-kernel, and src-uland.'
        )
    )
    parser.add_argument(
        '--base',
        action='append',
        default=list(DEFAULT_BASE),
        help=(
            'Base directories to scan (may be repeated; defaults to '
            'usr/src, src-kernel, and src-uland)'
        ),
    )
    parser.add_argument('--master', default=DEFAULT_MASTER,
                        help='Path to syscalls.master')
    parser.add_argument('--include-calls', action='store_true',
                        help='Include simple function call edges')
    args = parser.parse_args()

    files = gather_source_files(args.base)
    index = build_index(files, args.base)
    func_defs = extract_function_defs(files)

    edges = set()
    edges.update(map_includes(files, index))
    edges.update(parse_syscalls(args.master, func_defs))
    if args.include_calls:
        edges.update(map_function_calls(files, func_defs))

    out_path = 'dependency_graph.dot'
    with open(out_path, 'w') as out:
        out.write('digraph G {\n')
        for src, dst in sorted(edges):
            out.write(f'  "{src}" -> "{dst}";\n')
        out.write('}\n')
    print(f'DOT file written to {out_path}')


if __name__ == '__main__':
    main()
