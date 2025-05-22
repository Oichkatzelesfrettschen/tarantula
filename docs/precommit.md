# Using pre-commit

This repository provides a `.pre-commit-config.yaml` with hooks for
`clang-format` and `clang-tidy`. Running `setup.sh` installs the
`pre-commit` tool along with `clang-tidy`. Activate the hooks to
automatically format code and run static analysis before each commit:

```sh
pip install pre-commit
pre-commit install
```

The hooks rely on the configuration files `.clang-format` and
`.clang-tidy` at the repository root.  A helper script
`tools/run_clang_tidy.sh` selects the appropriate language standard
(C23 or C++17) when invoking `clang-tidy`.
