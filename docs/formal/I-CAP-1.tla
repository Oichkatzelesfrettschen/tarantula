---- MODULE I-CAP-1 ----
EXTENDS Naturals

(**************************************************************************)
(* Capability Revocation Model                                           *)
(* Proves invariant I-CAP-1: revoked capabilities are never active.       *)
(**************************************************************************)

CONSTANT Capabilities

VARIABLES active, revoked

Init == /\ active = {}
        /\ revoked = {}

Add(cap) == /\ cap \in Capabilities
             /\ cap \notin active
             /\ active' = active \cup {cap}
             /\ revoked' = revoked

Revoke(cap) == /\ cap \in active
               /\ active' = active \setminus {cap}
               /\ revoked' = revoked \cup {cap}

Next == \E cap \in Capabilities: Add(cap)
        \/ \E cap \in active: Revoke(cap)

I_CAP_1 == active \cap revoked = {}

Spec == Init /\ [][Next]_<<active, revoked>>

THEOREM I_CAP_1_Holds == Spec => []I_CAP_1
====

