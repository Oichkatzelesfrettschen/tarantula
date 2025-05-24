# GitHub CI Workflows

This document describes recommended workflows for integrating CodeQL security scanning and Reviewdog-based linting. Sample workflow files can be found in `.github/workflows/codeql-analysis.yml` and `.github/workflows/reviewdog.yml`.
For local linting before pushing, enable the `pre-commit` hooks described in
[precommit.md](precommit.md).

## CodeQL with Bundled Query Packs

Use the `codeql-bundle-action` to assemble a specific set of query packs once and reuse that bundle across repositories or workflow runs. This approach keeps scans deterministic and avoids repeated downloads of the same query packs.

A minimal setup looks like this:

```yaml
name: codeql-multilang

on:
  push:
    branches: [main, release/**]
  pull_request:
    branches: [main, release/**]

permissions:
  contents: read
  security-events: write

env:
  BUNDLE_ARTIFACT: codeql-custom-bundle.tgz

jobs:
  build-bundle:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4
    - name: Build CodeQL bundle
      uses: advanced-security/codeql-bundle-action@v2
      with:
        packs: |
          codeql/javascript-queries@latest
          codeql/cpp-queries@latest
        output: ${{ env.BUNDLE_ARTIFACT }}
    - uses: actions/upload-artifact@v4
      with:
        name: ${{ env.BUNDLE_ARTIFACT }}
        path: ${{ env.BUNDLE_ARTIFACT }}
        retention-days: 5

  codeql-scan:
    needs: build-bundle
    runs-on: ubuntu-latest
    strategy:
      fail-fast: false
      matrix:
        include:
          - lang: "c-cpp"
          - lang: "python"
          - lang: "go"
          - lang: "javascript-typescript"
    steps:
    - uses: actions/checkout@v4
    - uses: actions/download-artifact@v4
      with:
        name: ${{ env.BUNDLE_ARTIFACT }}
    - name: Initialise CodeQL
      uses: github/codeql-action/init@v3
      with:
        languages: ${{ matrix.lang }}
        tools: ${{ env.BUNDLE_ARTIFACT }}
    - name: Autobuild
      uses: github/codeql-action/autobuild@v3
    - name: Perform CodeQL Analysis
      uses: github/codeql-action/analyze@v3
      with:
        category: "/language:${{ matrix.lang }}"
        output: sarif
```

## Reviewdog Annotations

Reviewdog can turn any linter output into GitHub pull request checks. The following example matrix runs several linters in parallel and reports results inline:

```yaml
name: lint-and-annotate

on:
  pull_request:
    types: [opened, synchronize, reopened]
  push:
    branches: [main]

permissions:
  contents: read
  pull-requests: write

jobs:
  lint:
    runs-on: ubuntu-latest
    strategy:
      fail-fast: false
      matrix:
        linter:
          - { id: "shellcheck", cmd: "shellcheck -f gcc $(git ls-files '*.sh')" }
          - { id: "black",       cmd: "black --check --diff ." }
          - { id: "golangci",    cmd: "golangci-lint run --out-format=checkstyle" }
    steps:
    - uses: actions/checkout@v4
    - uses: actions/setup-go@v5
    - uses: actions/setup-python@v5
    - name: Install linter runtime deps
      run: |
        sudo apt-get update -y
        sudo apt-get install -y shellcheck
    - name: Run ${{ matrix.linter.id }} & feed Reviewdog
      uses: reviewdog/reviewdog@v0.20.3
      uses: reviewdog/reviewdog@master
      with:
        name: ${{ matrix.linter.id }}
        reporter: github-pr-check
        filter_mode: diff_context
        fail_level: error
        run: ${{ matrix.linter.cmd }}
        level: warning
```

These snippets should be placed in `.github/workflows/` to enable deterministic security analysis and helpful inline lint feedback on pull requests.

## Kernel Test Job

The `build.yml` workflow also compiles and runs `tests/test_kern`. This job
builds the microkernel stubs and the test program using `bmake` and GCC, then
executes the binary. The test output and resulting executable are uploaded as
artifacts for later inspection.

A simplified example of the steps is:

```yaml
test-kern:
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v3
    - name: Install GCC and bmake
      run: |
        sudo apt-get update
        sudo apt-get install -y build-essential gcc-multilib aptitude
        sudo aptitude -y install bmake
    - name: Build test binary
      run: |
        bmake -C src-kernel CC=gcc
        bmake -C tests CC=gcc
    - name: Run test_kern
      run: ./tests/test_kern > test_kern.log
    - uses: actions/upload-artifact@v3
      with:
        name: test_kern_results
        path: |
          tests/test_kern
          test_kern.log
```

This provides a lightweight regression test ensuring the kernel stubs and
supporting libraries remain functional.
