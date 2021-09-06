--------------------------------- MODULE ABQ ---------------------------------
(*
Derived from:
AB.tla from Leslie Lamport's TLA+ Course, Lecture 9, Part 2

https://www.youtube.com/watch?v=EIDpC_iEVJ8
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 2: The Protocol (HD)"

This is a first attempt to adapt AB.tla to implement my ABQSpec
variation of ABSpec.

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

VARIABLES AWait, AVar, AAcked, BVar, BRcvd,   \* The same as in module ABSpec
          AtoB,  \* The sequence of data messages in transit from sender to receiver.
          BtoA   \* The sequence of ack messages in transit from receiver to sender.
                 \* Messages are sent by appending them to the end of the sequence.
                 \* and received by removing them from the head of the sequence.

vars == << AWait, AVar, AAcked, BVar, BRcvd, AtoB, BtoA >>

TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          /\ AtoB \in Seq(Data \X {0,1})
          /\ BtoA \in Seq({0,1})

Init == /\ AWait = << >>
        /\ AVar \in Data \X {1}
        /\ AAcked = << >>
        /\ BVar = AVar
        /\ BRcvd = << >>
        /\ AtoB = << >>
        /\ BtoA = << >>

AWrite(d) ==
    /\ d \in Data
    /\ AWait' = Append(AWait, d)
    /\ UNCHANGED <<AVar, AAcked, BVar, BRcvd, AtoB, BtoA>>

(***************************************************************************)
(* The action of the sender sending a data message by appending AVar to    *)
(* the end of the message queue AtoB.  It will keep sending the same       *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AWait, AVar, AAcked, BtoA, BVar, BRcvd>>

(***************************************************************************)
(* The action of the sender receiving an ack message.  If that ack is for  *)
(* the value it is sending, then it chooses another message to send and    *)
(* sets AVar to that message.  If the ack is for the previous value it     *)
(* sent, it ignores the message.  In either case, it removes the message   *)
(* from BtoA.                                                              *)
(***************************************************************************)
ARcv ==
    /\ BtoA /= << >>
    /\ AWait /= << >>
    /\ IF Head(BtoA) = AVar[2]
         THEN /\ AVar' = <<Head(AWait), 1 - AVar[2]>>
              /\ AWait' = Tail(AWait)
              /\ AAcked' = Append(AAcked, AVar[1])
         ELSE /\ AVar' = AVar
              /\ AWait' = AWait
              /\ AAcked' = AAcked
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<AtoB, BVar, BRcvd>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd ==
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AWait, AVar, AAcked, AtoB, BVar, BRcvd>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv ==
    /\ AtoB /= << >>
    /\ IF Head(AtoB)[2] # BVar[2]
         THEN /\ BVar' = Head(AtoB)
              /\ BRcvd' = Append(BRcvd, BVar[1])
         ELSE /\ BVar' = BVar
              /\ BRcvd' = BRcvd
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AWait, AVar, AAcked, BtoA>>

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
               /\ UNCHANGED << AWait, AVar, AAcked, BVar, BRcvd, BtoA >>

LoseMsgBtoA == /\ \E i \in 1..Len(BtoA):
                       BtoA' = Remove(i, BtoA)
               /\ UNCHANGED << AWait, AVar, AAcked, BVar, BRcvd, AtoB >>

Next ==
    \/ \E d \in Data: AWrite(d)
    \/ ASnd
    \/ ARcv
    \/ BSnd
    \/ BRcv
    \/ LoseMsgAtoB
    \/ LoseMsgBtoA

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABQSpec

ABS_Spec == ABS!Spec
ABS_FairSpec == ABS!FairSpec

Inv ==
    /\ ABS!Inv
    /\ ABS!PrefixInv

THEOREM Spec => ABS!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with fairness conditions added.                        *)
(***************************************************************************)
FairSpecSS == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))

FairSpecWW == Spec  /\  WF_vars(ARcv) /\ WF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))

FairSpecWS == Spec  /\  WF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))

FairSpecSW == Spec  /\  SF_vars(ARcv) /\ WF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))
=============================================================================
\* Modification History
\* Last modified Wed Dec 27 13:29:51 PST 2017 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
