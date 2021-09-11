----------------------------- MODULE AB_nonfifo -----------------------------
(*
Derived from:
AB.tla from Leslie Lamport's TLA+ Course, Lecture 9, Part 2

https://www.youtube.com/watch?v=EIDpC_iEVJ8
"Lamport TLA+ Course Lecture 9: The Alternating Bit Protocol Part 2: The Protocol (HD)"

This is a simple one-line change from AB_fifo.tla in this directory,
changing only the EXTENDS of ChannelFIFO to ChannelNonFIFO.

*)

EXTENDS Integers, Sequences, ChannelNonFIFO

CONSTANT Data

CONSTANT NullMsg

ASSUME ~(NullMsg \in Data)

VARIABLES AMsgs, BMsgs,  \* The same as in module RTSpec
          AWait, AVar, BVar,
          AtoB,  \* The channel of data messages in transit from sender to receiver.
          BtoA   \* The channel of ack messages in transit from receiver to sender.

vars == <<AMsgs, BMsgs, AWait, AVar, BVar, AtoB, BtoA>>

TypeOK == /\ AMsgs \in Seq(Data)
          /\ BMsgs \in Seq(Data)
          /\ AVar \in (Data \union {NullMsg}) \X {0,1}
          /\ BVar \in {0,1}
          /\ AWait \in Seq(Data)
          /\ AtoB \in ChannelType(Data \X {0,1})
          /\ BtoA \in ChannelType({0,1})

Init == /\ AMsgs = << >>
        /\ BMsgs = << >>
        /\ AWait = << >>
        /\ AVar = << NullMsg, 1 >>
        /\ BVar = 0
        /\ AtoB = EmptyChannel
        /\ BtoA = EmptyChannel

AWrite(d) ==
    /\ d \in Data
    /\ AWait' = Append(AWait, d)
    /\ AMsgs' = Append(AMsgs, d)
    /\ UNCHANGED <<BMsgs, AVar, BVar, AtoB, BtoA>>

(***************************************************************************)
(* The action of the sender "loading" a value from the beginning of the    *)
(* queue AWait into AVar, so it becomes ready to transmit to the receiver. *)
(***************************************************************************)
Aload ==
    /\ AVar[1] = NullMsg
    /\ AWait /= << >>
    /\ AVar' = <<Head(AWait), AVar[2]>>
    /\ AWait' = Tail(AWait)
    /\ UNCHANGED <<AMsgs, BMsgs, BVar, AtoB, BtoA>>

(***************************************************************************)
(* The action of the sender sending a data message by adding AVar to       *)
(* the channel AtoB.  It will keep sending the same                        *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd ==
    /\ AVar[1] /= NullMsg
    /\ AtoB' = ChannelAfterSendMsg(AtoB, AVar)
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, BtoA, BVar>>

(***************************************************************************)
(* The action of the sender receiving an ack message.  If that ack is for  *)
(* the value it is sending, then it replaces the remembered message with   *)
(* NullMsg, as it was in the initial state, which leaves A ready to take   *)
(* an Aload step whenever AWait is non-empty.  If the ack is for the       *)
(* previous value it sent, it ignores the message.  In either case, it     *)
(* removes the message from BtoA.                                          *)
(***************************************************************************)
ARcv ==
    /\ BtoA /= EmptyChannel
    /\ \E ack_msg \in SetOfReceivableMessages(BtoA):
           /\ IF ack_msg = AVar[2]
                THEN /\ AVar' = <<NullMsg, 1 - AVar[2]>>
                ELSE /\ AVar' = AVar
           /\ BtoA' = ChannelAfterReceiveMsg(BtoA, ack_msg)
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd ==
    /\ BtoA' = ChannelAfterSendMsg(BtoA, BVar)
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv ==
    /\ AtoB /= EmptyChannel
    /\ \E data_msg \in SetOfReceivableMessages(AtoB):
           /\ IF data_msg[2] /= BVar
                THEN /\ BVar' = data_msg[2]
                     /\ BMsgs' = Append(BMsgs, data_msg[1])
                ELSE /\ BVar' = BVar
                     /\ BMsgs' = BMsgs
           /\ AtoB' = ChannelAfterReceiveMsg(AtoB, data_msg)
    /\ UNCHANGED <<AMsgs, AWait, AVar, BtoA>>

(***************************************************************************)
(* LoseMsgAtoB is the action that removes an arbitrary message from the    *)
(* channel AtoB.  Similarly for LoseMsgBtoA.                               *)
(***************************************************************************)
LoseMsgAtoB == /\ ChannelLoseMsg(AtoB)
               /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, BVar, BtoA>>

LoseMsgBtoA == /\ ChannelLoseMsg(BtoA)
               /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, BVar, AtoB>>

Next ==
    \/ \E d \in Data: AWrite(d)
    \/ Aload
    \/ ASnd
    \/ ARcv
    \/ BSnd
    \/ BRcv
    \/ LoseMsgAtoB
    \/ LoseMsgBtoA

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
RTS == INSTANCE RTSpec

RTS_Spec == RTS!Spec
RTS_FairSpec == RTS!FairSpec

Inv == RTS!Inv

THEOREM Spec => RTS!Spec
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

FairSpecWeaker == Spec  /\ \A d \in Data: WF_vars(AWrite(d))

FairSpecWS == Spec  /\  WF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))

FairSpecSW == Spec  /\  SF_vars(ARcv) /\ WF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))
=============================================================================
