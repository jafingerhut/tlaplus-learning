------------------------------- MODULE SRA_fifo ------------------------------
(*

My first attempt at writing a spec for the behavior of a Selective
Repeat ARQ transport protocol, using sequence numbers that can contain
multiple bits, but are finite and do wrap around.

    https://en.wikipedia.org/wiki/Selective_Repeat_ARQ

It is nearly identical to GBN_fifo.tla in this directory, because I
want to either prove it implements RTSpec, or violates it, depending
on various details, e.g. FIFO links vs. non-FIFO links, safety
vs. liveness properties, etc.

This specification of selective repeat ARQ uses only cumulative
acknowledgement messages.  There are other variants of selective
repeat ARQ where the receiver can send acknowledgement messages that
acknowledge only a specific sequence number, or a range of sequence
numbers, and/or include the ability to send negative acknowledgement
messages.  This specification does not include those features.

*)

EXTENDS Integers, Sequences, ChannelFIFO

CONSTANT Data

CONSTANT NSeq   \* The number of different sequence numbers used by the protocol
CONSTANT W      \* The maximum number of different sequence numbers the sender can send before it must wait for an ackwnoledgement
CONSTANT V      \* The maximum number of different sequence numbers the receiver accepts.  Normally this is described as equal to W, but I wanted to make it an independent parameter that might be smaller than W.

ASSUME NSeq \in Nat  /\  NSeq > 1
ASSUME W \in Nat  /\  W > 0  /\  W =< NSeq
ASSUME V \in Nat  /\  V > 0  /\  V =< W

VARIABLES AMsgs, BMsgs,  \* The same as in module RTSpec
          AWait, AVar, BVar,
          AtoB,  \* The channel of data messages in transit from sender to receiver.
          BtoA   \* The channel of ack messages in transit from receiver to sender.

vars == <<AMsgs, BMsgs, AWait, AVar, BVar, AtoB, BtoA>>

SeqNum == 0..(NSeq-1)

PlusMod(a, b) == (a + b) % NSeq
MinusMod(a, b) == (a - b) % NSeq

TypeOK == /\ AMsgs \in Seq(Data)
          /\ BMsgs \in Seq(Data)
          /\ AWait \in Seq(Data)
          /\ AVar \in [buf: [SeqNum -> Data],
                       win_begin: SeqNum,
                       num_msgs: 0..W,
                       next_to_send: SeqNum]
          /\ BVar \in [buf: [SeqNum -> Data],
                       valid: [SeqNum -> {0,1}],
		       nmsgs_ready: 0..V,
	               exp_seqnum: SeqNum]
          /\ AtoB \in ChannelType(Data \X SeqNum)
          /\ BtoA \in ChannelType(SeqNum)

\* If AVar.num_msgs is 0, then there are no messages ready to send from A
\* in AVar.buf.

\* If AVar.num_msgs is greater than 0, then there are exactly that
\* many messages ready to send from A in AVar.buf, and they are stored
\* in buf at indices AVar.win_begin up to
\* PlusMod(Avar.win_begin, AVar.num_msgs - 1).

IndexInBuf(idx2, avar) ==
    /\ idx2 \in SeqNum
    /\ MinusMod(idx2, avar.win_begin) < avar.num_msgs

Init == /\ AMsgs = << >>
        /\ BMsgs = << >>
        /\ AWait = << >>
        /\ \E d \in Data:
	       /\ AVar = [buf |-> [x \in SeqNum |-> d],
                          win_begin |-> 0, num_msgs |-> 0, next_to_send |-> 0]
               /\ BVar = [buf |-> [x \in SeqNum |-> d],
	                  valid |-> [x \in SeqNum |-> 0],
	                  nmsgs_ready |-> 0,
	                  exp_seqnum |-> 0]
        /\ AtoB = EmptyChannel
        /\ BtoA = EmptyChannel

AWrite(d) ==
    /\ d \in Data
    /\ AWait' = Append(AWait, d)
    /\ AMsgs' = Append(AMsgs, d)
    /\ UNCHANGED <<BMsgs, AVar, BVar, AtoB, BtoA>>

(***************************************************************************)
(* The action of the sender "loading" a value from the beginning of the    *)
(* queue AWait into AVar's send window, so it becomes ready to transmit to *)
(* the receiver.                                                           *)
(***************************************************************************)
Aload ==
    /\ AVar.num_msgs < W
    /\ AWait /= << >>
    /\ LET idx == PlusMod(AVar.win_begin, AVar.num_msgs)
       IN  /\ AVar' = [AVar EXCEPT
                        !.buf = [AVar.buf EXCEPT ![idx] = Head(AWait)],
                        !.num_msgs = AVar.num_msgs + 1]
    /\ AWait' = Tail(AWait)
    /\ UNCHANGED <<AMsgs, BMsgs, BVar, AtoB, BtoA>>

(***************************************************************************)
(* The action of the sender sending a data message by adding it to         *)
(* the channel AtoB.  It will keep sending the same                        *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd ==
    /\ AVar.num_msgs > 0
    /\ LET idx == AVar.next_to_send
           idxplus1 == PlusMod(idx, 1)
           next_idx == IF IndexInBuf(idxplus1, AVar)
                         THEN idxplus1
                         ELSE AVar.win_begin  \* wrap around back to win begin
       IN  /\ AtoB' = ChannelAfterSendMsg(AtoB, <<AVar.buf[idx], idx>>)
           /\ AVar' = [AVar EXCEPT !.next_to_send = next_idx]
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, BtoA, BVar>>

AVarInvariant ==
    IF AVar.num_msgs > 0
      THEN IndexInBuf(AVar.next_to_send, AVar)
      ELSE AVar.next_to_send = AVar.win_begin

\* The action of the sender receiving an ack message with sequence
\* number X.
\*
\* The convention used here is that the receiver sending an ack with a
\* sequence number X means that the receiver has received X-1 (modulo
\* NSeq), and expects to receive a message with sequence number X now.
\*
\* If (X-1) is in the sender's buffer of messages awaiting
\* acknowledgements, then the sender's win_begin is advanced to X,
\* num_msgs is reduced by the number of messages remaining in the
\* buffer after win_begin is advanced, and next_to_send is changed to
\* lie within the buffer if the change in win_begin would leave it
\* outside of the buffer.
\*
\* If (X-1) is outside of the sender's buffer, then the sender leaves
\* its state unchanged.  Most likely this is a repeated
\* acknowledgement for some message that was already acknowledged
\* earlier.
\*
\* The ack message is always removed from BtoA.

ARcv ==
    /\ BtoA /= EmptyChannel
    /\ \E ack_msg \in SetOfReceivableMessages(BtoA):
           /\ IF IndexInBuf(MinusMod(ack_msg, 1), AVar)
                THEN LET delta == MinusMod(ack_msg, AVar.win_begin)
                         tmp == [AVar EXCEPT
                                       !.win_begin = PlusMod(AVar.win_begin, delta),
                                       !.num_msgs = AVar.num_msgs - delta]
                     IN  IF IndexInBuf(AVar.next_to_send, tmp)
                           THEN AVar' = tmp
                           ELSE AVar' = [tmp EXCEPT !.next_to_send = tmp.win_begin]
                ELSE AVar' = AVar
           /\ BtoA' = ChannelAfterReceiveMsg(BtoA, ack_msg)
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd ==
    /\ BtoA' = ChannelAfterSendMsg(BtoA, BVar.exp_seqnum)
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv ==
    /\ AtoB /= EmptyChannel
    /\ \E data_msg \in SetOfReceivableMessages(AtoB):
           /\ LET msg_data == data_msg[1]
                  msg_seqnum == data_msg[2]
                  delta == MinusMod(msg_seqnum, BVar.exp_seqnum)
                  Btmp1 == [BVar EXCEPT !.buf = [BVar.buf EXCEPT ![msg_seqnum] = msg_data],
		                        !.valid = [BVar.valid EXCEPT ![msg_seqnum] = 1]]
                  nmsgs_ready == Maximum({c \in 0..V: (\A x \in 0..(c-1): Btmp1.valid[PlusMod(BVar.exp_seqnum, x)] = 1)})
                  msgs_ready == [x \in 1..nmsgs_ready |-> Btmp1.buf[PlusMod(BVar.exp_seqnum, x-1)]]
		  Btmp2 == [Btmp1 EXCEPT !.nmsgs_ready = nmsgs_ready,
		                         !.valid = [s \in SeqNum |-> IF MinusMod(s, BVar.exp_seqnum) < nmsgs_ready
		                                                       THEN 0
		                                                       ELSE Btmp1.valid[s]]]
              IN  IF delta >= 0 /\ delta < V
                    THEN /\ BVar' = [Btmp2 EXCEPT !.exp_seqnum = PlusMod(BVar.exp_seqnum, nmsgs_ready)]
                         /\ BMsgs' = BMsgs \o msgs_ready
                    ELSE UNCHANGED <<BVar, BMsgs>>
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

Inv ==
    /\ RTS!Inv
    /\ AVarInvariant

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
