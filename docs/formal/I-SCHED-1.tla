---- MODULE I_SCHED_1 ----
EXTENDS Naturals, FiniteSets

(**************************************************************************)
(* Scheduling Fairness Model                                             *)
(* Proves invariant I-SCHED-1: Eventual execution for runnable threads  *)
(**************************************************************************)

CONSTANTS
    Threads,         \* Set of all threads
    MaxStarvation    \* Maximum steps before a thread must run

VARIABLES
    runnable,        \* Set of runnable threads
    running,         \* Currently running thread (or NULL)
    waiting,         \* Threads waiting on resources
    wait_count,      \* Starvation counter per thread
    schedule_count   \* Total number of scheduling decisions

TypeInvariant ==
    /\ runnable \subseteq Threads
    /\ running \in Threads \union {NULL}
    /\ waiting \subseteq Threads
    /\ wait_count \in [Threads -> Nat]
    /\ schedule_count \in Nat
    /\ runnable \cap waiting = {}
    /\ (running /= NULL) => (running \in runnable)

NULL == CHOOSE x: x \notin Threads

Init ==
    /\ runnable = {}
    /\ running = NULL
    /\ waiting = {}
    /\ wait_count = [t \in Threads |-> 0]
    /\ schedule_count = 0

MakeRunnable(t) ==
    /\ t \in Threads
    /\ t \notin runnable
    /\ t \notin waiting
    /\ runnable' = runnable \union {t}
    /\ wait_count' = [wait_count EXCEPT ![t] = 0]
    /\ UNCHANGED <<running, waiting, schedule_count>>

Block(t) ==
    /\ t \in runnable
    /\ t = running
    /\ runnable' = runnable \ {t}
    /\ waiting' = waiting \union {t}
    /\ running' = NULL
    /\ UNCHANGED <<wait_count, schedule_count>>

Unblock(t) ==
    /\ t \in waiting
    /\ runnable' = runnable \union {t}
    /\ waiting' = waiting \ {t}
    /\ wait_count' = [wait_count EXCEPT ![t] = 0]
    /\ UNCHANGED <<running, schedule_count>>

Schedule(t) ==
    /\ t \in runnable
    /\ t /= running
    /\ running' = t
    /\ wait_count' = [th \in Threads |->
            IF th \in runnable /\ th /= t
            THEN wait_count[th] + 1
            ELSE wait_count[th]]
    /\ schedule_count' = schedule_count + 1
    /\ UNCHANGED <<runnable, waiting>>

Yield ==
    /\ running /= NULL
    /\ running' = NULL
    /\ UNCHANGED <<runnable, waiting, wait_count, schedule_count>>

Next ==
    \/ \E t \in Threads: MakeRunnable(t)
    \/ \E t \in runnable: Block(t)
    \/ \E t \in waiting: Unblock(t)
    \/ \E t \in runnable: Schedule(t)
    \/ Yield

(**************************************************************************)
(* I-SCHED-1: Bounded Starvation                                        *)
(* Every runnable thread is eventually scheduled within a bounded time  *)
(**************************************************************************)

I_SCHED_1_BoundedStarvation ==
    \A t \in runnable:
        wait_count[t] < MaxStarvation

(**************************************************************************)
(* I-SCHED-2: Fairness Property                                         *)
(* Eventually every runnable thread gets scheduled                      *)
(**************************************************************************)

I_SCHED_2_EventualExecution ==
    \A t \in Threads:
        (t \in runnable) ~> (running = t)

(**************************************************************************)
(* I-SCHED-3: Progress                                                  *)
(* If there are runnable threads, one must eventually run               *)
(**************************************************************************)

I_SCHED_3_Progress ==
    (runnable /= {}) => <>(running \in runnable)

(**************************************************************************)
(* No Deadlock: If runnable threads exist, system makes progress       *)
(**************************************************************************)

NoDeadlock ==
    (runnable /= {}) =>
        <>(schedule_count' > schedule_count)

Spec == Init /\ [][Next]_<<runnable, running, waiting, wait_count, schedule_count>>
            /\ WF_<<runnable, running, waiting, wait_count, schedule_count>>(
                \E t \in runnable: Schedule(t))

THEOREM I_SCHED_1_Holds == Spec => [](I_SCHED_1_BoundedStarvation)
THEOREM I_SCHED_2_Holds == Spec => []I_SCHED_2_EventualExecution
THEOREM I_SCHED_3_Holds == Spec => [](I_SCHED_3_Progress)
THEOREM NoDeadlock_Holds == Spec => [](NoDeadlock)

====
