# Tool Execution Reports

This log captures representative executions of the analysis tools across a subset of the source tree. Each section quotes the invocation and a condensed excerpt of its output.

## lizard
```
lizard sys/kern/subr_prf.c
```
Outputs cyclomatic complexity per function, e.g. `kprintf` with CCN 46.

## cloc
```
cloc sys/kern
```
Counts 20,876 lines of code across 55 C files.

## cppcheck
```
cppcheck --enable=warning,style sys/kern/subr_prf.c
```
Flags portability and style issues such as implicit `int` returns and redundant `continue` statements.

## sloccount
```
sloccount sys/kern
```
Estimates 19,603 physical SLOC and projects 4.55 person‑years of effort.

## flawfinder
```
flawfinder sys/kern/subr_prf.c
```
Highlights format string risks around `printf`/`sprintf` at lines 305–518.

## semgrep
```
semgrep --config=auto tools/analyze_codebase.py
```
Scan completed with no findings.

## pylint
```
pylint tools/analyze_codebase.py
```
Reports missing docstrings and unused variables; score 7.37/10.

## flake8
```
flake8 tools/analyze_codebase.py
```
No style violations detected.

## mypy
```
mypy tools/analyze_codebase.py
```
Successful static type analysis with no errors.

## cscope
```
find sys/kern -name "*.c" > cscope.files
cscope -q -b -i cscope.files
```
Generated `cscope.out` cross‑reference database.

## diffoscope
```
diffoscope README.md README.md
```
Tool unavailable in runtime; installation provides library only.

## valgrind
```
valgrind --version
```
Reports version 3.22.0.

## gdb
```
gdb --version
```
GNU gdb 15.0.50.20240403‑git.

## eslint
```
eslint /tmp/sample.js
```
Fails without `eslint.config.js` per v9 migration guide.

## jshint
```
jshint /tmp/sample.js
```
Run completes with no warnings.

## jscpd
```
jscpd /tmp/sample.js
```
Detects no duplicate fragments (0.178 ms).

## nyc
```
nyc node /tmp/sample.js
```
Generates a coverage table with zero statements.

