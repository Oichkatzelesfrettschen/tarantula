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

The installation fetches hook repositories from GitHub. When offline,
mirror those repositories into `offline_packages/` so pre-commit can
provision them locally.

## Offline hook mirroring

To work offline, clone each hook repository listed in
`.pre-commit-config.yaml` into `offline_packages/`:

```sh
mkdir -p offline_packages
cd offline_packages
# Clone each hook repository from .pre-commit-config.yaml
git clone https://github.com/pre-commit/mirrors-clang-format
git clone https://github.com/pocc/pre-commit-hooks
# Add others as needed
cd ..
```

Then update `.pre-commit-config.yaml` to reference local paths:

```yaml
repos:
  - repo: offline_packages/mirrors-clang-format
    rev: <version>
    # ...
```

Alternatively, use `pre-commit install-hooks --config .pre-commit-config.yaml`
with network access once, then package `~/.cache/pre-commit/` for offline
deployment.

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
