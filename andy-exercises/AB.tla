--------------------------------- MODULE AB ---------------------------------
(*
AB.tla from Leslie Lamport's TLA+ Course, Lecture 9, Part 2

https://www.youtube.com/watch?v=EIDpC_iEVJ8
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 2: The Protocol (HD)"
*)

EXTENDS Integers, Sequences

CONSTANT Data

(***************************************************************************)
(* We first define Remove(i, seq) to be the sequence obtained by removing  *)
(* element number i from sequence seq.                                     *)
(***************************************************************************)
Remove(i, seq) ==
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j]
                                      ELSE seq[j+1]]

VARIABLES AVar, BVar,   \* The same as in module ABSpec
          AtoB,  \* The sequence of data messages in transit from sender to receiver.
          BtoA   \* The sequence of ack messages in transit from receiver to sender.
                 \* Messages are sent by appending them to the end of the sequence.
                 \* and received by removing them from the head of the sequence.

vars == << AVar, BVar, AtoB, BtoA >>

TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          /\ AtoB \in Seq(Data \X {0,1})
          /\ BtoA \in Seq({0,1})

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

(***************************************************************************)
(* The action of the sender sending a data message by appending AVar to    *)
(* the end of the message queue AtoB.  It will keep sending the same       *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BtoA, BVar>>

(***************************************************************************)
(* The action of the sender receiving an ack message.  If that ack is for  *)
(* the value it is sending, then it chooses another message to send and    *)
(* sets AVar to that message.  If the ack is for the previous value it     *)
(* sent, it ignores the message.  In either case, it removes the message   *)
(* from BtoA.                                                              *)
(***************************************************************************)
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

(***************************************************************************)
(* LoseMsg is the action that removes an arbitrary message from queue AtoB *)
(* or BtoA.                                                                *)
(***************************************************************************)
(*
LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB):
                         AtoB' = Remove(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA):
                         BtoA' = Remove(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED << AVar, BVar >>
*)

(* I prefer to have separate definitions for the losing of each kind
of message.  It makes counterexamples a bit easier to read with the
separate names. *)

LoseMsgAtoB == /\ \E i \in 1..Len(AtoB):
                       AtoB' = Remove(i, AtoB)
               /\ UNCHANGED << AVar, BVar, BtoA >>

LoseMsgBtoA == /\ \E i \in 1..Len(BtoA):
                       BtoA' = Remove(i, BtoA)
               /\ UNCHANGED << AVar, BVar, AtoB >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsgAtoB \/ LoseMsgBtoA

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec

THEOREM Spec => ABS!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with fairness conditions added.                        *)
(***************************************************************************)
FairSpec == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                      WF_vars(ASnd) /\ WF_vars(BSnd)
=============================================================================
\* Modification History
\* Last modified Wed Dec 27 13:29:51 PST 2017 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
