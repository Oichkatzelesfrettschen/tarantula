# Formal Verification

This directory stores TLA+ specifications used to verify critical invariants of the exokernel design.

The included `I-CAP-1.tla` model demonstrates capability revocation. It shows that once a capability is revoked it no longer appears in the active set. The invariant corresponds to the intended behavior of `cap_revoke()` in the user-space resource managers described in `exokernel_plan.md`.

These formal models are minimal and independent of the code but mirror the operations provided by the implementation. Maintaining the proofs helps ensure that refactoring the kernel keeps fundamental safety guarantees intact.

