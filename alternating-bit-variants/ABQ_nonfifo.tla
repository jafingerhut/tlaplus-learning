----------------------------- MODULE ABQ_nonfifo -----------------------------
(*
Derived from:
AB.tla from Leslie Lamport's TLA+ Course, Lecture 9, Part 2

https://www.youtube.com/watch?v=EIDpC_iEVJ8
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 2: The Protocol (HD)"

This is a first attempt to adapt AB.tla to implement my ABQSpec
variation of ABSpec.

This is most closely related to ABQ.tla.  Like the change I made from
AB.tla to AB_nonfifo.tla to model links that can deliver messages in a
different order than they were transmitted, this ABQ_nonfifo.tla is
like ABQ.tla, except links can deliver messages in a different order
than they were transmitted.

*)

EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AWait, AVar, AAcked, BVar, BRcvd,   \* The same as in module ABSpec
          AtoB,  \* The set of data messages in transit from sender to receiver.
          BtoA   \* The set of ack messages in transit from receiver to sender.
                 \* Messages are sent by adding them to the set
                 \* and received by removing them from the set.

vars == << AWait, AVar, AAcked, BVar, BRcvd, AtoB, BtoA >>

TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          /\ AWait \in Seq(Data)
          /\ AAcked \in Seq(Data)
          /\ BRcvd \in Seq(Data)
          /\ AtoB \in SUBSET(Data \X {0,1})
          /\ BtoA \in SUBSET({0,1})

Init == /\ AWait = << >>
        /\ AVar \in Data \X {1}
        /\ AAcked = << >>
        /\ BVar = AVar
        /\ BRcvd = << >>
        /\ AtoB = {}
        /\ BtoA = {}

AWrite(d) ==
    /\ d \in Data
    /\ AWait' = Append(AWait, d)
    /\ UNCHANGED <<AVar, AAcked, BVar, BRcvd, AtoB, BtoA>>

(***************************************************************************)
(* The action of the sender sending a data message adding AVar to          *)
(* the set of messages AtoB.  It will keep sending the same                *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd ==
    /\ AtoB' = AtoB \union {AVar}
    /\ UNCHANGED <<AWait, AVar, AAcked, BtoA, BVar, BRcvd>>

(***************************************************************************)
(* The action of the sender receiving an ack message.  If that ack is for  *)
(* the value it is sending, then it chooses another message to send and    *)
(* sets AVar to that message.  If the ack is for the previous value it     *)
(* sent, it ignores the message.  In either case, it removes the message   *)
(* from BtoA.                                                              *)
(***************************************************************************)
ARcv ==
    /\ BtoA /= {}
    /\ AWait /= << >>
    /\ \E ack_msg \in BtoA:
           /\ IF ack_msg = AVar[2]
                THEN /\ AVar' = <<Head(AWait), 1 - AVar[2]>>
                     /\ AWait' = Tail(AWait)
                     /\ AAcked' = Append(AAcked, AVar[1])
                ELSE /\ AVar' = AVar
                     /\ AWait' = AWait
                     /\ AAcked' = AAcked
           /\ BtoA' = BtoA \ {ack_msg}
    /\ UNCHANGED <<AtoB, BVar, BRcvd>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd ==
    /\ BtoA' = BtoA \union {BVar[2]}
    /\ UNCHANGED <<AWait, AVar, AAcked, AtoB, BVar, BRcvd>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv ==
    /\ AtoB /= {}
    /\ \E data_msg \in AtoB:
           /\ IF data_msg[2] /= BVar[2]
                THEN /\ BVar' = data_msg
                     /\ BRcvd' = Append(BRcvd, BVar[1])
                ELSE /\ BVar' = BVar
                     /\ BRcvd' = BRcvd
           /\ AtoB' = AtoB \ {data_msg}
    /\ UNCHANGED <<AWait, AVar, AAcked, BtoA>>

(***************************************************************************)
(* LoseMsg is the action that removes an arbitrary message from queue AtoB *)
(* or BtoA.                                                                *)
(***************************************************************************)
LoseMsgAtoB == /\ \E data_msg \in AtoB:
                       AtoB' = AtoB \ {data_msg}
               /\ UNCHANGED << AWait, AVar, AAcked, BVar, BRcvd, BtoA >>

LoseMsgBtoA == /\ \E ack_msg \in BtoA:
                       BtoA' = BtoA \ {ack_msg}
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
