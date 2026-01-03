# Formal Verification

This directory stores TLA+ specifications and Z3 models used to verify critical invariants of the microkernel and exokernel design.

## TLA+ Specifications

### I-CAP-1.tla - Capability Revocation Safety
Demonstrates capability revocation. Shows that once a capability is revoked it no longer appears in the active set. The invariant corresponds to the intended behavior of `cap_revoke()` in the user-space resource managers described in `exokernel_plan.md`.

**Status:** ✓ Complete - Proven

### I-IPC-1.tla - IPC Message Ordering
Proves FIFO ordering guarantees for mailbox-based IPC. Verifies that messages sent in order s₁ → s₂ are received in order r₁ → r₂. Includes proofs for:
- FIFO ordering preservation
- No message loss
- No spurious messages

**Status:** ✓ Complete - Ready for model checking

### I-MEM-1.tla - Memory Safety
Proves memory safety properties:
- I-MEM-1: No use-after-free violations
- I-MEM-2: No double-free violations  
- I-MEM-3: No use-before-allocation

Includes allocation bound checking and temporal safety properties.

**Status:** ✓ Complete - Ready for model checking

### I-SCHED-1.tla - Scheduling Fairness
Proves scheduling fairness properties:
- I-SCHED-1: Bounded starvation for runnable threads
- I-SCHED-2: Eventual execution guarantee
- I-SCHED-3: Progress property (liveness)

Includes deadlock freedom verification.

**Status:** ✓ Complete - Ready for model checking

## Z3 SMT Models

### buffer_overflow_check.smt2
Verifies integer overflow safety in buffer allocation:
- Multiplication overflow detection
- Maximum size enforcement
- Realistic scenario testing

**Usage:** `z3 buffer_overflow_check.smt2`

### pointer_safety.smt2
Verifies pointer arithmetic safety:
- Bounds checking
- Overflow detection  
- Alignment verification

**Usage:** `z3 pointer_safety.smt2`

### capability_ordering.smt2
Extends I-CAP-1 with hierarchical capabilities:
- Parent-child derivation
- Transitive revocation
- Acyclic property

**Usage:** `z3 capability_ordering.smt2`

## Running Model Checking

### TLA+ Models

Install TLA+ Toolbox or command-line tools:

```bash
# Download TLA+ tools
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Run model checker
java -jar tla2tools.jar -config I-IPC-1.cfg I-IPC-1.tla
```

### Z3 Models

Install Z3 solver:

```bash
# Via pip
pip3 install z3-solver

# Via apt (Ubuntu/Debian)
sudo apt install z3

# Run verification
z3 buffer_overflow_check.smt2
z3 pointer_safety.smt2
z3 capability_ordering.smt2
```

## Integration with Development

These formal models are minimal and independent of the code but mirror the operations provided by the implementation. Maintaining the proofs helps ensure that refactoring the kernel keeps fundamental safety guarantees intact.

### CI Integration

Add to `.github/workflows/formal-verification.yml`:

```yaml
name: Formal Verification
on: [push, pull_request]
jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Install Z3
        run: sudo apt install z3
      - name: Run Z3 proofs
        run: |
          z3 docs/formal/*.smt2
      - name: Install TLA+
        run: wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
      - name: Model check TLA+ specs
        run: |
          for spec in docs/formal/*.tla; do
            java -jar tla2tools.jar $spec
          done
```

## Future Work

Additional specifications needed:
- Deadlock detection for IPC protocols
- Virtual memory consistency
- Filesystem transaction safety
- Network protocol correctness

