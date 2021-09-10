--------------------------------- MODULE GBN ---------------------------------
(*

My first attempt at writing a spec for the behavior of a Go-Back-N
transport protocol, using sequence numbers that can contain multiple
bits, but are finite and do wrap around.

    https://en.wikipedia.org/wiki/Go-Back-N_ARQ

It has parts in common with AB.tla from this directory, because I want
to either prove it implements RTSpec, or violates it, depending on
various details, e.g. FIFO links vs. non-FIFO links, safety
vs. liveness properties, etc.

*)

EXTENDS Integers, Sequences

CONSTANT Data

\* CONSTANT NullMsg

CONSTANT NSeq   \* The number of different sequence numbers used by the protocol
CONSTANT W      \* The maximum number of different sequence numbers the sender can send before it must wait for an ackwnoledgement

\* ASSUME ~(NullMsg \in Data)

ASSUME NSeq \in Nat  /\  NSeq > 1
ASSUME W \in Nat  /\  W > 0  /\  W =< NSeq

(***************************************************************************)
(* We first define Remove(i, seq) to be the sequence obtained by removing  *)
(* element number i from sequence seq.                                     *)
(***************************************************************************)
Remove(i, seq) ==
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j]
                                      ELSE seq[j+1]]

VARIABLES AMsgs, BMsgs,  \* The same as in module RTSpec
          AWait, AVar, BVar,
          AtoB,  \* The sequence of data messages in transit from sender to receiver.
          BtoA   \* The sequence of ack messages in transit from receiver to sender.
                 \* Messages are sent by appending them to the end of the sequence.
                 \* and received by removing them from the head of the sequence.

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
          /\ BVar \in [exp_seqnum: SeqNum]
          /\ AtoB \in Seq(Data \X SeqNum)
          /\ BtoA \in Seq(SeqNum)

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
	       AVar = [buf |-> [x \in SeqNum |-> d],
                       win_begin |-> 0, num_msgs |-> 0, next_to_send |-> 0]
        /\ BVar = [exp_seqnum |-> 0]
        /\ AtoB = << >>
        /\ BtoA = << >>

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
(* The action of the sender sending a data message by appending AVar to    *)
(* the end of the message queue AtoB.  It will keep sending the same       *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd ==
    /\ AVar.num_msgs > 0
    /\ LET idx == AVar.next_to_send
           idxplus1 == PlusMod(idx, 1)
           next_idx == IF IndexInBuf(idxplus1, AVar)
                         THEN idxplus1
                         ELSE AVar.win_begin  \* wrap around back to win begin
       IN  /\ AtoB' = Append(AtoB, <<AVar.buf[idx], idx>>)
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
    /\ BtoA /= << >>
    /\ BtoA' = Tail(BtoA)
    /\ LET ack_msg == Head(BtoA)
       IN  IF IndexInBuf(MinusMod(ack_msg, 1), AVar)
             THEN LET delta == MinusMod(ack_msg, AVar.win_begin)
                      tmp == [AVar EXCEPT
                                    !.win_begin = PlusMod(AVar.win_begin, delta),
                                    !.num_msgs = AVar.num_msgs - delta]
                  IN  IF IndexInBuf(AVar.next_to_send, tmp)
                        THEN AVar' = tmp
                        ELSE AVar' = [tmp EXCEPT !.next_to_send = tmp.win_begin]
             ELSE AVar' = AVar
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd ==
    /\ BtoA' = Append(BtoA, BVar.exp_seqnum)
    /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, AtoB, BVar>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It sets BVar to   *)
(* that message if it's not for the data item it has already received.     *)
(***************************************************************************)
BRcv ==
    /\ AtoB /= << >>
    /\ LET msg_data == Head(AtoB)[1]
           msg_seqnum == Head(AtoB)[2]
       IN  IF msg_seqnum = BVar.exp_seqnum
             THEN /\ BVar' = [BVar EXCEPT !.exp_seqnum = PlusMod(msg_seqnum, 1)]
                  /\ BMsgs' = Append(BMsgs, msg_data)
             ELSE /\ BVar' = BVar
                  /\ BMsgs' = BMsgs
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AMsgs, AWait, AVar, BtoA>>

(***************************************************************************)
(* LoseMsgAtoB is the action that removes an arbitrary message from queue  *)
(* AtoB.  LoseMsgBtoA does the same for queue BtoA.                        *)
(***************************************************************************)
LoseMsgAtoB == /\ \E i \in 1..Len(AtoB):
                       AtoB' = Remove(i, AtoB)
               /\ UNCHANGED <<AMsgs, BMsgs, AWait, AVar, BVar, BtoA>>

LoseMsgBtoA == /\ \E i \in 1..Len(BtoA):
                       BtoA' = Remove(i, BtoA)
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
