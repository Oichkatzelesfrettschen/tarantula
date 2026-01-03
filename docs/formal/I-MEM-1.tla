---- MODULE I_MEM_1 ----
EXTENDS Naturals, FiniteSets

(**************************************************************************)
(* Memory Safety Model                                                   *)
(* Proves invariant I-MEM-1: No use-after-free                          *)
(* Proves invariant I-MEM-2: No double-free                             *)
(**************************************************************************)

CONSTANTS
    Pointers,      \* Set of all possible pointer values
    MaxAllocs      \* Maximum number of allocations

VARIABLES
    allocated,     \* Set of currently allocated pointers
    freed,         \* Set of freed pointers (never reallocated)
    operations     \* Sequence of operations for checking

TypeInvariant ==
    /\ allocated \subseteq Pointers
    /\ freed \subseteq Pointers
    /\ operations \in Seq({"alloc", "free", "use"} \X Pointers)

Init ==
    /\ allocated = {}
    /\ freed = {}
    /\ operations = <<>>

Alloc(ptr) ==
    /\ ptr \in Pointers
    /\ ptr \notin allocated
    /\ ptr \notin freed
    /\ Cardinality(allocated) < MaxAllocs
    /\ allocated' = allocated \union {ptr}
    /\ freed' = freed
    /\ operations' = Append(operations, <<"alloc", ptr>>)

Free(ptr) ==
    /\ ptr \in allocated
    /\ ptr \notin freed
    /\ allocated' = allocated \ {ptr}
    /\ freed' = freed \union {ptr}
    /\ operations' = Append(operations, <<"free", ptr>>)

Use(ptr) ==
    /\ ptr \in allocated
    /\ allocated' = allocated
    /\ freed' = freed
    /\ operations' = Append(operations, <<"use", ptr>>)

Next ==
    \/ \E ptr \in Pointers: Alloc(ptr)
    \/ \E ptr \in allocated: Free(ptr)
    \/ \E ptr \in allocated: Use(ptr)

(**************************************************************************)
(* I-MEM-1: Use-After-Free Safety                                       *)
(* A pointer cannot be used after it has been freed                     *)
(**************************************************************************)

I_MEM_1_UseAfterFreeSafety ==
    \A i \in DOMAIN operations:
        LET op == operations[i]
            op_type == op[1]
            ptr == op[2]
        IN  (op_type = "use") => (ptr \notin freed)

(**************************************************************************)
(* I-MEM-2: Double-Free Prevention                                      *)
(* A pointer can only be freed once                                     *)
(**************************************************************************)

I_MEM_2_DoubleFreePrevention ==
    \A ptr \in freed:
        Cardinality({i \in DOMAIN operations: 
            operations[i][1] = "free" /\ operations[i][2] = ptr}) = 1

(**************************************************************************)
(* I-MEM-3: Use-Before-Alloc Prevention                                *)
(* A pointer cannot be used before it is allocated                      *)
(**************************************************************************)

I_MEM_3_UseBeforeAlloc ==
    \A i \in DOMAIN operations:
        LET op == operations[i]
            op_type == op[1]
            ptr == op[2]
        IN  (op_type = "use") =>
            \E j \in DOMAIN operations:
                /\ j < i
                /\ operations[j][1] = "alloc"
                /\ operations[j][2] = ptr
                /\ ~\E k \in DOMAIN operations:
                    /\ j < k /\ k < i
                    /\ operations[k][1] = "free"
                    /\ operations[k][2] = ptr

(**************************************************************************)
(* Memory Leak Detection: All allocated memory eventually freed         *)
(**************************************************************************)

EventuallyAllFreed ==
    <>(\A ptr \in Pointers: ptr \notin allocated)

(**************************************************************************)
(* Allocation Bounded: Never exceed maximum allocations                 *)
(**************************************************************************)

AllocationBounded ==
    Cardinality(allocated) <= MaxAllocs

Spec == Init /\ [][Next]_<<allocated, freed, operations>>

THEOREM I_MEM_1_Holds == Spec => [](I_MEM_1_UseAfterFreeSafety)
THEOREM I_MEM_2_Holds == Spec => [](I_MEM_2_DoubleFreePrevention)
THEOREM I_MEM_3_Holds == Spec => [](I_MEM_3_UseBeforeAlloc)
THEOREM AllocationBounded_Holds == Spec => [](AllocationBounded)

====
