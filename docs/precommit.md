# Using pre-commit

This repository provides a `.pre-commit-config.yaml` with hooks for
`clang-format`, `clang-tidy` and `shellcheck`. Running `setup.sh` installs the
`pre-commit` tool via both `apt` and `pip` and automatically sets up
the git hooks. After executing the script no manual steps are needed,
but you can re-install the hooks any time:

```sh
pre-commit install --install-hooks
```

The hooks rely on the configuration files `.clang-format` and
`.clang-tidy` at the repository root.  A helper script
`tools/run_clang_tidy.sh` selects the appropriate language standard
(C2x for C or C++17) when invoking `clang-tidy`.

Shell scripts (`*.sh`) are linted with `
A `.gitignore` file at the repository root prevents common build artifacts
from being committed. Patterns include `*/obj/`, `*.o`, `*.a`, `*.log` and the
`compile/` directory.
