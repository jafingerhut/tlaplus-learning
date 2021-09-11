---------------------------- MODULE ChannelFIFO ----------------------------
(*

I often want to model messages sent between systems.

Two main variants are:

+ channels that always deliver messages in the same order that they
  were transmitted, i.e. a FIFO channel
+ channels that can reorder messages

This module, and the accompanying module ChannelNonFIFO, provide some
definitions such that if they are used in another module consistently,
will allow that module to change from FIFO channels to non-FIFO
channels, or vice versa, simply by changing one of these two EXTEND
statements:

+ EXTEND ChannelFIFO
+ EXTEND ChannelNonFIFO

Bags are somewhat more realistic, and can potentially capture more
kinds of ways that a protocol can have errors, because it is
physically possible for a sender to send multiple copies of the same
message at different times, and have each copy reordered with other
messages independently of each other.  When using only a set to
represent messages in flight, it is as if retransmissions have no
effect at all, because a set can only represent at most one copy of
each message in flight, not more than one.

*)

EXTENDS Integers, Sequences


(***************************************************************************)
(* We first define Remove(i, seq) to be the sequence obtained by removing  *)
(* element number i from sequence seq.                                     *)
(***************************************************************************)
Remove(i, seq) ==
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j]
                                      ELSE seq[j+1]]

EmptyChannel == << >>

\* MessageType must be a set of possible messages that can be sent on
\* the channel.  ChannelType(MessageType) returns a set of possible
\* values of the channel.

ChannelType(MessageType) == Seq(MessageType)

ChannelAfterSendMsg(C, M) == Append(C, M)

\* Only the one message at the head is allowed to be received.
SetOfReceivableMessages(C) == {Head(C)}

\* TODO: Is there a way to make the following definition give an
\* error, or be disabled, if M is not equal to Head(C)?
ChannelAfterReceiveMsg(C, M) == Tail(C)

ChannelLoseMsg(C) == \E i \in 1..Len(C): C' = Remove(i, C)

ChannelNumMsgs(C) == Len(C)
=============================================================================
