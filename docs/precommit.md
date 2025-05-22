# Using pre-commit

This repository provides a `.pre-commit-config.yaml` with hooks for
`clang-format` and `clang-tidy`. Running `setup.sh` installs the
`pre-commit` tool via both `apt` and `pip` and automatically sets up
the git hooks. After executing the script no manual steps are needed,
but you can re-install the hooks any time:

```sh
pre-commit install --install-hooks
```

The hooks rely on the configuration files `.clang-format` and
`.clang-tidy` at the repository root.  A helper script
`tools/run_clang_tidy.sh` selects the appropriate language standard
(C23 or C++17) when invoking `clang-tidy`.

Each `src-uland` makefile defines a helper `tidy` target that runs
`clang-tidy` on that component's sources:

```sh
cd src-uland/libvm
make tidy
```

The command above uses the same options as the pre-commit hook.
