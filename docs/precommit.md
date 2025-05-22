# Using pre-commit

This repository provides a `.pre-commit-config.yaml` with hooks for
`clang-format` and `clang-tidy`. Install the pre-commit tool and
activate the hooks to automatically format code and run static analysis
before each commit:

```sh
pip install pre-commit
pre-commit install
```

The hooks rely on the configuration files `.clang-format` and
`.clang-tidy` at the repository root.
