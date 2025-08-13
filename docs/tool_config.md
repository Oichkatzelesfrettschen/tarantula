# Tool Installation and Configuration

This document enumerates analysis and instrumentation utilities, their canonical installation vectors, and any notable configuration requirements.

| Tool | Installation Method | Configuration Notes | Example Command |
|------|---------------------|---------------------|-----------------|
| lizard | `pip install lizard` | Default cyclomatic complexity threshold of 15; adjust with `-C <n>` | `lizard sys/kern/subr_prf.c` |
| cloc | `sudo apt-get install cloc` | Counts blank, comment and code lines; supports `--include-lang` to filter | `cloc sys/kern` |
| cscope | `sudo apt-get install cscope` | Generate database with `cscope -b`; use `cscope -d` for read-only queries | `cscope -q -b -i cscope.files` |
| diffoscope | `pip install diffoscope` | Provides deep difference reports; requires external helpers for archives | `diffoscope README.md README.md` |
| dtrace | source build | Clone [dtrace4linux](https://github.com/dtrace4linux/linux) and run `make; sudo make install` | `dtrace -l` |
| valgrind | `sudo apt-get install valgrind` | Use `--tool=<tool>` to select memcheck, cachegrind, etc. | `valgrind --version` |
| cppcheck | `sudo apt-get install cppcheck` | Enable additional analyses via `--enable=warning,style` | `cppcheck --enable=warning,style sys/kern/subr_prf.c` |
| sloccount | `sudo apt-get install sloccount` | Uses COCOMO model for effort estimates | `sloccount sys/kern` |
| flawfinder | `sudo apt-get install flawfinder` | Reports potential security flaws ranked 0–5 | `flawfinder sys/kern/subr_prf.c` |
| gdb | `sudo apt-get install gdb` | Use `.gdbinit` for session defaults; integrate with `bear` for symbols | `gdb --version` |
| pylint | `pip install pylint` | Configure via `pyproject.toml` or `.pylintrc` | `pylint tools/analyze_codebase.py` |
| flake8 | `pip install flake8` | Extend via plugins in `setup.cfg` or `tox.ini` | `flake8 tools/analyze_codebase.py` |
| mypy | `pip install mypy` | Type checking honors `mypy.ini` | `mypy tools/analyze_codebase.py` |
| semgrep | `pip install semgrep` | Autoconfig with `--config=auto` or supply rule sets | `semgrep --config=auto tools/analyze_codebase.py` |
| eslint | `npm install -g eslint` | Requires `eslint.config.js` in v9; older `.eslintrc.*` need migration | `eslint sample.js` |
| jshint | `npm install -g jshint` | Supports `.jshintrc` for per-project rules | `jshint sample.js` |
| jscpd | `npm install -g jscpd` | Duplicate detector; tweak thresholds with `--min-lines` | `jscpd sample.js` |
| nyc | `npm install -g nyc` | JavaScript coverage harness; configure via `.nycrc` | `nyc node sample.js` |
