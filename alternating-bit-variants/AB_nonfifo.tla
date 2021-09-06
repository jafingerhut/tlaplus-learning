----------------------------- MODULE AB_nonfifo -----------------------------
(*
Derived from:
AB.tla from Leslie Lamport's TLA+ Course, Lecture 9, Part 2

https://www.youtube.com/watch?v=EIDpC_iEVJ8
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 2: The Protocol (HD)"

I have modified it so that the links between A and B can reorder
messages, and also perhaps drop them.  FIFO links are a reasonable
restriction in some physical implementations, but not when there can
be multiple network devices such as switches or routers between the
endpoints, and this network can have routing changes due to link
failures where the new path chosen has a lower latency than the
previously selected path.

*)

EXTENDS Integers

CONSTANT Data

VARIABLES AVar, BVar,   \* The same as in module ABSpec
          AtoB,  \* The set of data messages in transit from sender to receiver.
          BtoA   \* The set of ack messages in transit from receiver to sender.
                 \* Messages are sent by adding them to the set
                 \* and received by removing them from the set.

vars == << AVar, BVar, AtoB, BtoA >>

TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          /\ AtoB \in SUBSET(Data \X {0,1})
          /\ BtoA \in SUBSET({0,1})

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = {}
        /\ BtoA = {}

(***************************************************************************)
(* The action of the sender sending a data message adding AVar to          *)
(* the set of messages AtoB.  It will keep sending the same                *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd == /\ AtoB' = AtoB \union {AVar}
        /\ UNCHANGED <<AVar, BtoA, BVar>>

(***************************************************************************)
(* The action of the sender receiving an ack message.  If that ack is for  *)
(* the value it is sending, then it chooses another message to send and    *)
(* sets AVar to that message.  If the ack is for the previous value it     *)
(* sent, it ignores the message.  In either case, it removes the message   *)
(* from BtoA.                                                              *)
(***************************************************************************)
ARcv == /\ BtoA # {}
        /\ \E ack_msg \in BtoA:
               /\ IF ack_msg = AVar[2]
                      THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
                      ELSE AVar' = AVar
               /\ BtoA' = BtoA \ {ack_msg}
        /\ UNCHANGED <<AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd == /\ BtoA' = BtoA \union {BVar[2]}
        /\ UNCHANGED <<AVar, BVar, AtoB>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv == /\ AtoB # {}
        /\ \E data_msg \in AtoB:
               /\ IF data_msg[2] # BVar[2]
                    THEN BVar' = data_msg
                    ELSE BVar' = BVar
               /\ AtoB' = AtoB \ {data_msg}
        /\ UNCHANGED <<AVar, BtoA>>

(***************************************************************************)
(* LoseMsg is the action that removes an arbitrary message from queue AtoB *)
(* or BtoA.                                                                *)
(***************************************************************************)
LoseMsgAtoB == /\ \E data_msg \in AtoB:
                       AtoB' = AtoB \ {data_msg}
               /\ UNCHANGED << AVar, BVar, BtoA >>

LoseMsgBtoA == /\ \E ack_msg \in BtoA:
                       BtoA' = BtoA \ {ack_msg}
               /\ UNCHANGED << AVar, BVar, AtoB >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsgAtoB \/ LoseMsgBtoA

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec

ABS_Spec == ABS!Spec
ABS_FairSpec == ABS!FairSpec

Inv ==
    /\ ABS!Inv

THEOREM Spec => ABS!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with fairness conditions added.                        *)
(***************************************************************************)
FairSpecSS == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd)

FairSpecWW == Spec  /\  WF_vars(ARcv) /\ WF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd)

FairSpecWS == Spec  /\  WF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd)

FairSpecSW == Spec  /\  SF_vars(ARcv) /\ WF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd)
=============================================================================
\* Modification History
\* Last modified Wed Dec 27 13:29:51 PST 2017 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
