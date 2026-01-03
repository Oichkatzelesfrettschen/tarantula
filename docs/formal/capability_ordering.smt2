; Z3 Model for Capability Ordering and Revocation
; Extends I-CAP-1 with hierarchical capabilities

; Define capability types
(declare-datatypes ((Capability 0)) (
  ((mk-cap (id Int) (parent Int) (level Int)))
))

; Declare capability variables
(declare-const c1 Capability)
(declare-const c2 Capability)
(declare-const c3 Capability)

; Active and revoked sets
(declare-fun active (Capability) Bool)
(declare-fun revoked (Capability) Bool)
(declare-fun derives (Capability Capability) Bool)

; I-CAP-1: Revoked capabilities not active
(assert (forall ((c Capability))
  (=> (revoked c) (not (active c)))
))

; I-CAP-2: Revoking parent revokes derived capabilities
(assert (forall ((parent Capability) (child Capability))
  (=> (and (derives child parent) (revoked parent))
      (revoked child))
))

; Derivation is transitive
(assert (forall ((c1 Capability) (c2 Capability) (c3 Capability))
  (=> (and (derives c1 c2) (derives c2 c3))
      (derives c1 c3))
))

; No capability derives from itself (acyclic)
(assert (forall ((c Capability))
  (not (derives c c))
))

; Test: Can we have active derived cap when parent is revoked?
(assert (active c1))
(assert (derives c1 c2))
(assert (revoked c2))

(check-sat)  ; Should be UNSAT (violates I-CAP-2)

; Additional test scenarios
(push)
(echo "Testing three-level hierarchy...")
(assert (derives c1 c2))
(assert (derives c2 c3))
(assert (revoked c3))
(assert (active c1))
(check-sat)  ; Should be UNSAT (transitive revocation)
(pop)

(push)
(echo "Testing independent capabilities...")
(assert (not (derives c1 c2)))
(assert (revoked c2))
(assert (active c1))
(check-sat)  ; Should be SAT (independent caps OK)
(pop)
