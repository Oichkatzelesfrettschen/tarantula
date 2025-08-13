# Using pre-commit

This repository provides a `.pre-commit-config.yaml` with hooks for
`clang-format`, `clang-tidy`, `shellcheck` and `codespell`. After cloning the
repository install `pre-commit` and related utilities as described in
[`docs/setup_guide.md`](setup_guide.md), then run `pre-commit install
--install-hooks` to set up the local git hooks. You can re-install the hooks at
any time:

```sh
pre-commit install --install-hooks
```

The hooks rely on the configuration files `.clang-format` and
`.clang-tidy` at the repository root.  A helper script
`tools/run_clang_tidy.sh` selects the appropriate language standard
(C2x for C or C++17) when invoking `clang-tidy`.

Shell scripts (`*.sh`) are linted with `shellcheck`.
Use `tools/generate_compiledb.sh` to create a `compile_commands.json` file for
`clang-tidy`.
A `.gitignore` file at the repository root prevents common build artifacts from
being committed. Patterns include `*/obj/`, `*.o`, `*.a`, `*.log` and the
`compile/` directory.
