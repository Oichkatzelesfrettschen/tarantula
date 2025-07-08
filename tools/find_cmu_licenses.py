#!/usr/bin/env python3
"""Locate files containing the Carnegie Mellon license header."""
import os
import sys
from typing import List

KEYWORDS = ["Carnegie-Mellon University", "Carnegie Mellon University"]


def scan_file(path: str) -> bool:
    """Return True if the file begins with any CMU license marker."""
    try:
        with open(path, 'r', errors='ignore') as f:
            head = ''.join(f.readlines()[:80])
    except (UnicodeDecodeError, OSError):
        return False
    return any(kw in head for kw in KEYWORDS)


def collect_files(base: str) -> List[str]:
    matches = []
    for root, dirs, files in os.walk(base):
        for name in files:
            full = os.path.join(root, name)
            if scan_file(full):
                matches.append(full)
    return matches


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else '.'
    files = collect_files(base)
    for f in sorted(files):
        print(f)


if __name__ == "__main__":
    main()
