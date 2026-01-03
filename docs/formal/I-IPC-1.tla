---- MODULE I_IPC_1 ----
EXTENDS Naturals, Sequences

(**************************************************************************)
(* IPC Message Ordering Model                                            *)
(* Proves invariant I-IPC-1: FIFO ordering for mailbox messages.         *)
(* Messages sent in order s₁ → s₂ are received in order r₁ → r₂        *)
(**************************************************************************)

CONSTANTS 
    Messages,      \* Set of all possible messages
    Mailboxes,     \* Set of all mailboxes
    MaxQueue       \* Maximum queue depth

VARIABLES 
    queues,        \* mailbox -> sequence of messages
    sent,          \* sequence of (mailbox, message, timestamp) tuples
    received,      \* sequence of (mailbox, message, timestamp) tuples
    clock          \* Logical clock for ordering

TypeInvariant ==
    /\ \A mb \in Mailboxes: queues[mb] \in Seq(Messages)
    /\ sent \in Seq(Mailboxes \X Messages \X Nat)
    /\ received \in Seq(Mailboxes \X Messages \X Nat)
    /\ clock \in Nat

Init ==
    /\ queues = [mb \in Mailboxes |-> <<>>]
    /\ sent = <<>>
    /\ received = <<>>
    /\ clock = 0

Send(mb, msg) ==
    /\ Len(queues[mb]) < MaxQueue
    /\ queues' = [queues EXCEPT ![mb] = Append(queues[mb], msg)]
    /\ sent' = Append(sent, <<mb, msg, clock>>)
    /\ received' = received
    /\ clock' = clock + 1

Receive(mb) ==
    /\ Len(queues[mb]) > 0
    /\ LET msg == Head(queues[mb])
       IN /\ queues' = [queues EXCEPT ![mb] = Tail(queues[mb])]
          /\ received' = Append(received, <<mb, msg, clock>>)
    /\ sent' = sent
    /\ clock' = clock + 1

Next ==
    \/ \E mb \in Mailboxes, msg \in Messages: Send(mb, msg)
    \/ \E mb \in Mailboxes: Receive(mb)

(**************************************************************************)
(* FIFO Ordering Invariant: Messages are received in send order         *)
(**************************************************************************)

I_IPC_1_FIFOOrdering ==
    \A i, j \in DOMAIN sent:
        LET si == sent[i]
            sj == sent[j]
            mb_i == si[1]
            mb_j == sj[1]
            msg_i == si[2]
            msg_j == sj[2]
            time_i == si[3]
            time_j == sj[3]
        IN  (mb_i = mb_j /\ i < j) =>
            \A ri, rj \in DOMAIN received:
                LET ri_entry == received[ri]
                    rj_entry == received[rj]
                IN  (ri_entry[1] = mb_i /\ ri_entry[2] = msg_i /\
                     rj_entry[1] = mb_j /\ rj_entry[2] = msg_j)
                    => ri < rj

(**************************************************************************)
(* No Message Loss: Every sent message is eventually received           *)
(**************************************************************************)

NoMessageLoss ==
    \A i \in DOMAIN sent:
        LET s == sent[i]
            mb == s[1]
            msg == s[2]
        IN \E j \in DOMAIN received:
               LET r == received[j]
               IN r[1] = mb /\ r[2] = msg

(**************************************************************************)
(* No Spurious Messages: Only sent messages can be received             *)
(**************************************************************************)

NoSpuriousMessages ==
    \A i \in DOMAIN received:
        LET r == received[i]
            mb == r[1]
            msg == r[2]
        IN \E j \in DOMAIN sent:
               LET s == sent[j]
               IN s[1] = mb /\ s[2] = msg

Spec == Init /\ [][Next]_<<queues, sent, received, clock>>

THEOREM I_IPC_1_Holds == Spec => [](I_IPC_1_FIFOOrdering)
THEOREM NoMessageLoss_Holds == Spec => <>(NoMessageLoss)
THEOREM NoSpuriousMessages_Holds == Spec => [](NoSpuriousMessages)

====
