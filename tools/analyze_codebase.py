import os
import sys
from collections import defaultdict

EXTENSIONS = ['.c', '.h', '.s', '.y', '.l', '.sh', '.f']


def collect_counts(base_dir):
    counts = defaultdict(int)
    for root, dirs, files in os.walk(base_dir):
        for f in files:
            _, ext = os.path.splitext(f)
            if ext in EXTENSIONS:
                counts[ext] += 1
    return counts


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else '.'
    counts = collect_counts(base)
    for ext in sorted(EXTENSIONS):
        print(f"{ext}: {counts[ext]}")


if __name__ == "__main__":
    main()
