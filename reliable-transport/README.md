# Introduction

This directory and its contents were created as a follow on to the
directory `alternating-bit-variants`.  I decided to create a separate
directory because in the directory `alternating-bit-variants`, the
focus is on the alternating bit protocol, which according to its name
limits itself to using a sequence number with only 1 bit.  That
directory demonstrates that while this protocol is correct when the
links between sender and receiver are FIFO, it is not correct if the
links between them can deliver messages in a different order than they
were sent.

This directory intends to specify protocols that use larger sequence
numbers, in order to do their job in the face of networks/links
between the sender and receiver that can reorder messages.


# RTSpec - a proposed basic specification of reliable transport protocols

The definition of `ABSpec` from Lamport's video lectures has the idea
of an alternating bit built right into the most general specification.

`RTSpec` does not have use a bit to identify the sender changing the
data message at all.  It models the sequence of data messages produces
so far by the sender as a TLA+ sequence, and similarly the receiver
has a sequence of messages it has received so far.  The sender has
steps `AWrite(d)` that it can take to append a new data message to its
sequence of messages that it wants the receiver to get a copy of, and
step `B` causes the receiver to append the next message in the
sender's sequence to the receiver's sequence (if there is one
available that the receiver does not already have).

As a simple test that `RTSpec` does not have any glaringly obvious
bugs, `RTSpec_ql.tla` adds a constraint on the sender's sequence
length to avoid an explosion in the number of possible reachable
states, and a definition of `NotReallyInvariant` such that I know that
`~NotReallyInvariant` should be true for some reachable states.  I
created that condition simply to verify that TLC can found a
counterexample that leads to a state violating that condition, and the
steps leading there look reasonable.  It can, using this command:

```bash
tlc RTSpec_ql.tla
```

I will not copy it here, but when I first ran that command it produced
a counterexample with 11 states, and all of the steps and intermediate
values of spec variables looked correct.


# A version of the alternating bit protocol that implements RTSpec

Starting from the original `AB.tla` given in Lamport's video course, I
modified it to create `AB_fifo.tla`.  In `AB_fifo`, the sender keeps a
record of all messages it wants to send in variable `AMsgs`, and a
record of all messages the receiver receives (in correct alternating
bit sequence number order) in a variable `BMsgs`.

I also modified `AB_fifo` to use my module `ChannelFIFO`.  This has
several definitions that, if you use them for the channels of messages
between sender and receiver, can easily be switched to non-FIFO
channels by extending module `ChannelNonFIFO` instead.

This command shows that it implements `RTSpec`'s safety properties.

```bash
tlc AB_fifo_ql.tla -config AB_ql_safety_only.cfg
```

And this command shows that it satisfies `RTSpec`'s liveness
properties:

```bash
tlc AB_fifo_ql.tla -config AB_ql_fss_satisfies_fs.cfg
```

I am a little surprised that AB implements the liveness properties,
even using only WF on steps:

```bash
tlc AB_fifo_ql.tla -config AB_ql_fww_satisfies_fs.cfg
```

I am very surprised that the following run finds no errors when
checking liveness properties.

```bash
tlc AB_fifo_ql.tla -config AB_ql_fweaker_satisfies_fs.cfg
```

TODO: What is going on here?


# Alternating bit fails safety properties of RTSpec with non-FIFO links

This is not anything new.  We have seen it before in the
`alternating-bit-variants` directory.  I did this as a quick exercise
to confirm that this version of AB fails to satisfy RTSpec's safety
properties when links are not FIFO:

```bash
tlc -difftrace AB_nonfifo_ql.tla -config AB_ql_safety_only.cfg
```

I was slightly surprised to see that the counterexample found only
used one value from the set `Data`.  The RTSpec safety property was
violated because B reached a state where it had received 3 messages,
but A had only produced 2.


# A first attempt at implementing a spec for Go-Back-N reliable transport

`GBN_fifo.tla` contains a spec that is reasonably close to an
implementation of a Go-Back-N sender and receiver, with FIFO links
between them.

The command below checks that it implements the safety properties of
`RTSpec` when using 4 different sequence numbers (`NSeq`=4) and the
sender limits itself to send at most 2 messages later than the last
one that was acknowledged (the window size `W`=2).

```bash
tlc -difftrace GBN_fifo_ql.tla -config GBN_ql_NSeq-4-W-2-safety_only.cfg
```

Even with only 2 possible values in the set `Data` and constraints on
various queue lengths that are quite short, TLC explores 423,000
distinct states.

```bash
tlc -difftrace GBN_fifo_ql.tla -config GBN_ql_NSeq-4-W-3-safety_only.cfg
```

The run above also finds no errors, after exploring 2,539,128 distinct
states.

```bash
tlc -difftrace GBN_fifo_ql.tla -config GBN_ql_NSeq-4-W-4-safety_only.cfg
```

The run above finds a sequence of 19 states that violates the `RTSpec`
safety properties, where the receiver accepts 5 messages when the
sender only produced 4.  This is a well known issue when you try to
have a window size that allows the sender to have as many new messages
outstanding as there are sequence numbers.


# Go-Back-N fails safety properties of RTSpec with non-FIFO links

This command takes a fair amount of time (about 40 mins on my 2015 Mac
laptop) before it finds a counterexample, because the state space is
fairly large:

```bash
tlc -difftrace GBN_nonfifo_ql.tla -config GBN_ql_NSeq-4-W-2-safety_only.cfg
```

Below is the counterexample trace found when I ran the command above:

```
Error: Invariant Inv is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ BMsgs = <<>>
/\ AtoB = << >>
/\ BVar = [exp_seqnum |-> 0]
/\ AWait = <<>>
/\ AMsgs = <<>>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 0, num_msgs |-> 0, next_to_send |-> 0]
/\ BtoA = << >>

State 2: <AWrite line 73, col 5 to line 76, col 50 of module GBN_nonfifo>
/\ AWait = <<d1>>
/\ AMsgs = <<d1>>

State 3: <Aload line 84, col 5 to line 91, col 51 of module GBN_nonfifo>
/\ AWait = <<>>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 0, num_msgs |-> 1, next_to_send |-> 0]

State 4: <AWrite line 73, col 5 to line 76, col 50 of module GBN_nonfifo>
/\ AWait = <<d1>>
/\ AMsgs = <<d1, d1>>

State 5: <Aload line 84, col 5 to line 91, col 51 of module GBN_nonfifo>
/\ AWait = <<>>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 0, num_msgs |-> 2, next_to_send |-> 0]

State 6: <AWrite line 73, col 5 to line 76, col 50 of module GBN_nonfifo>
/\ AWait = <<d1>>
/\ AMsgs = <<d1, d1, d1>>

State 7: <ASnd line 99, col 5 to line 107, col 52 of module GBN_nonfifo>
/\ AtoB = (<<d1, 0>> :> 1)
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 0, num_msgs |-> 2, next_to_send |-> 1]

State 8: <ASnd line 99, col 5 to line 107, col 52 of module GBN_nonfifo>
/\ AtoB = (<<d1, 0>> :> 1 @@ <<d1, 1>> :> 1)
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 0, num_msgs |-> 2, next_to_send |-> 0]

State 9: <ASnd line 99, col 5 to line 107, col 52 of module GBN_nonfifo>
/\ AtoB = (<<d1, 0>> :> 2 @@ <<d1, 1>> :> 1)
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 0, num_msgs |-> 2, next_to_send |-> 1]

State 10: <BRcv line 163, col 5 to line 173, col 45 of module GBN_nonfifo>
/\ BMsgs = <<d1>>
/\ AtoB = (<<d1, 0>> :> 1 @@ <<d1, 1>> :> 1)
/\ BVar = [exp_seqnum |-> 1]

State 11: <BRcv line 163, col 5 to line 173, col 45 of module GBN_nonfifo>
/\ BMsgs = <<d1, d1>>
/\ AtoB = (<<d1, 0>> :> 1)
/\ BVar = [exp_seqnum |-> 2]

State 12: <BSnd line 155, col 5 to line 156, col 58 of module GBN_nonfifo>
/\ BtoA = (2 :> 1)

State 13: <ARcv line 136, col 5 to line 148, col 52 of module GBN_nonfifo>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 2, num_msgs |-> 0, next_to_send |-> 2]
/\ BtoA = << >>

State 14: <Aload line 84, col 5 to line 91, col 51 of module GBN_nonfifo>
/\ AWait = <<>>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 2, num_msgs |-> 1, next_to_send |-> 2]

State 15: <AWrite line 73, col 5 to line 76, col 50 of module GBN_nonfifo>
/\ AWait = <<d1>>
/\ AMsgs = <<d1, d1, d1, d1>>

State 16: <Aload line 84, col 5 to line 91, col 51 of module GBN_nonfifo>
/\ AWait = <<>>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 2, num_msgs |-> 2, next_to_send |-> 2]

State 17: <ASnd line 99, col 5 to line 107, col 52 of module GBN_nonfifo>
/\ AtoB = (<<d1, 0>> :> 1 @@ <<d1, 2>> :> 1)
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 2, num_msgs |-> 2, next_to_send |-> 3]

State 18: <ASnd line 99, col 5 to line 107, col 52 of module GBN_nonfifo>
/\ AtoB = (<<d1, 0>> :> 1 @@ <<d1, 2>> :> 1 @@ <<d1, 3>> :> 1)
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 2, num_msgs |-> 2, next_to_send |-> 2]

State 19: <BRcv line 163, col 5 to line 173, col 45 of module GBN_nonfifo>
/\ BMsgs = <<d1, d1, d1>>
/\ AtoB = (<<d1, 0>> :> 1 @@ <<d1, 3>> :> 1)
/\ BVar = [exp_seqnum |-> 3]

State 20: <BRcv line 163, col 5 to line 173, col 45 of module GBN_nonfifo>
/\ BMsgs = <<d1, d1, d1, d1>>
/\ AtoB = (<<d1, 0>> :> 1)
/\ BVar = [exp_seqnum |-> 0]

State 21: <BRcv line 163, col 5 to line 173, col 45 of module GBN_nonfifo>
/\ BMsgs = <<d1, d1, d1, d1, d1>>
/\ AtoB = << >>
/\ BVar = [exp_seqnum |-> 1]
/\ AWait = <<>>
/\ AMsgs = <<d1, d1, d1, d1>>
/\ AVar = [buf |-> (0 :> d1 @@ 1 :> d1 @@ 2 :> d1 @@ 3 :> d1), win_begin |-> 2, num_msgs |-> 2, next_to_send |-> 2]
/\ BtoA = << >>

769392 states generated, 114590 distinct states found, 32896 states left on queue.
The depth of the complete state graph search is 21.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 6 and the 95th percentile is 3).
Finished in 38min 10s at (2021-09-11 20:32:47)
```

The basic idea of this sequence is very straightforward:

+ The sender sends a window W's worth of messages with sequence
  numbers 0 through W-1.
+ The sender retransmits the first message with sequence number 0.
+ The receiver receives and acknowledges the messages with sequence
  numbers 0 through W-1.
+ The sender advances its window to [W, 2W-1] and sends W more
  messages.
+ The receiver receives [W, 2W-1] and acks them all.
+ Repeat the steps above until the receiver is back to expecting
  sequence number 0.
+ Now the old retransmitted message with sequence number 0 arrives at
  the receiver, and is treated as if it were a new message with
  sequence number 0 by the receiver.  The receiver has now accepted a
  total of NSeq+1 messages, even though the sender has only produces
  NSeq messages.

This sequence generalizes to any integer values NSeq and W satisfying
1 <= W < NSeq.


# A first attempt at implementing a spec for Selective Repeat ARQ reliable transport

`SRA_fifo.tla` contains a spec that is at least one variant of an
implementation of a Selective Repeat ARQ sender and receiver, with
FIFO links between them.

The command below checks that it implements the safety properties of
`RTSpec` when using 4 different sequence numbers (`NSeq`=4) and the
sender limits itself to send at most 2 messages later than the last
one that was acknowledged (the window size `W`=2), and the receiver
limits itself to accepting a window of 2 different sequence numbers,
including the current expected sequence number up through that plus 1.

```bash
tlc -difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-4-W-2-safety_only.cfg
```

Even with only 2 possible values in the set `Data` and constraints on
various queue lengths that are quite short, TLC explores 533,522
distinct states.

The following run with `NSeq`=4 and `W`=3 does find a violation of the
`RTSpec` specification.

```bash
tlc -difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-4-W-3-safety_only.cfg
```

The counterexample has 20 steps, and ends with the receiver accepting
5 messages when the sender only produced 4.  This is a well known
issue when you try to have a window size that allows the sender and
receiver to have over half of `NSeq` messages in their windows.

Description of the steps:

* Sender does AWrite step for 4 copies of data d1, 3 of them do Aload
  into the sender's retransmission buffer.
* Sender does ASnd 3 times.  AtoB contains d1 3 times, with seq #s 0, 1, 2.
* B does BRcv of first message with seq # 0
* A does ASnd, retransmitting d1 with seq # 0
* B does BRcv of second message with seq # 1, and 3rd message with seq #2
  * AtoB now contains only retransmitted d1 with seq # 0
* B does BSnd to send ack # 3, the seq # of the next message it is expecting
* A does ARcv to get ack #3, so its window start advances to 3
* Aload to get 4th copy of d1 to send.  ASnd to send 4th copy of d1 with seq #3
  * AtoB now contains retransmitted d1 with seq #0 and new one with seq #3
* B does BRcv and misinterprets seq # 0 as _after_ seq #3, and accepts
  and stores it in its resequencing buffer
* B does BRcv for message with seq #3, and now releases that one, and
  the one with seq #0, for a total of 5 copies of the message, when A
  has only sent 4 copies.

Just to double-check with slightly larger state space, try with
`NSeq`=6 and `W`=3, which we expect should correctly implement the
safety properties.  It finds no errors while generating 6,677,874
distinct states.

```bash
tlc -difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-6-W-3-safety_only.cfg
```

The following one with `NSeq`=6 and `W`=4 has `W` greater than half of
`NSeq`, so we expect it to find a counterexample violating the safety
properties, which it does.

```bash
tlc -difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-6-W-4-safety_only.cfg
```

As expected, this finds a violation of RTSpec.  It takes 28 steps, and
ends with B receiving 7 messages after A only produced 6.


# How to implement reliable transport in the face of non-FIFO channels?

I have not read the research papers [5] and [6] in the references
section, but I believe the basic idea is that they prove under various
assumptions that it is impossible to have all of the following
properties satisfied simultaneously by a reliable transport protocol:

(C1) One's goal is to have a reliable transport protocol that can
     guarantee, worst case, that all messages are delivered in order
     to the receiver, with liveness guarantees.

(C2) Channels between endpoints can reorder or drop messages.

(C3) Messages sent can have at most a fixed finite number of
     additional bits, e.g. for header fields like sequence numbers,
     over and above the contents of the data messages being
     transported.

(C4) Messages can be buffered in the network for an arbitrarily long
     time before they are delivered.


## Relaxing conditions C1 or C2

(C1) is the goal of reliable transport, so we do not want to consider
here violating that condition.

It is typically impractical to try to violate (C2), at least the part
about never dropping messages.  Guaranteeing FIFO order between two
nodes in a network that can have routers or switches between them,
using a routing protocol to route around failed links and/or nodes, is
also difficult.


## Relaxing condition C3

If one is willing to violate (C3), then it is straightforward to
simply use sequence numbers in messages that can grow as large as
desired, e.g. using some variable-length encoding of sequence numbers,
so that the sender never uses the same sequence number for more than
one message.  In this way, the receiver never has any possibility of
confusing one received message for a different one.

Alternately, one can use a fixed number of bits for sequence numbers,
but simply limit the number of messages that can be sent in a single
reliable transport session to whatever will fit into that fixed number
of bits.  For example, a 64-bit sequence number on packets enables
sessions with up to 2^64 messages before the session must end.  In
many cases, such a large but finite limit would be acceptable.


## Relaxing condition C4

I believe that relaxing condition (C4) is effectively what is done, or
least _assumed_, for all reliable transport protocol implementations
in wide use.

* TCP
* Infiniband RC mode

Here is a relevant quote from [1]:

    "Since packets can get lost, packets must sometimes be
    retransmitted end-to-end, and since packets can be delayed
    arbitrarily, a packet can be retransmitted while the earlier copy
    of the packet is lurking in the network; that earlier copy can
    then remain in the network until the packet numbering wraps
    around, and the packet can then cause an uncorrectable error.
    This scenario is perhaps highly unlikely, but it serves to show
    that end-to-end recovery at the network or transport layer cannot
    be guaranteed to work correctly if packets are sometimes lost,
    sometimes get out of order, and sometimes become arbitrarily
    delayed.

    There are three possible ways out of the dilemma described above:

    first, insist that the network layer use virtual circuits and
    maintain ordering even if the path for a session is changed;

    second, make the modulus for numbering packets so large that
    errors of the foregoing type are acceptably unlikely;

    and third, create a mechanism whereby packets are destroyed after
    a maximum lifetime in the network, using a modulus large enough
    that wraparound cannot occur in that time.

    It is shown in Problem 2.43 that the reuqired modulus, using
    selective repeat, must be twice the window size plus the maximum
    number of packets of a session that can be transmitted while a
    given packet is alive.  In Section 2.9 we discuss how the
    transport protocol TCP uses a combination of the last two
    approaches described above." [2]

Another from [3]:

    "The solution to these problems is to design timers and window
    sizes carefully.  It is important that the packet-numbering space
    be large enough so that the packet number cannot wrap around
    during the worst-case delay time.  Thus, if it is conceivable that
    a network could delay a packet by 15 sec, it must not be possible
    for a transmitter, at maximum speed, to transmit enough packets so
    that a packet number will wrap around within 15 sec.  If the
    recipient holds on to packets that arrive out of order ..., it is
    also important that the window be no larger than half the packet
    number.  On strictly sequential channels [i.e. FIFO channels],
    packet might be lost but never reordered.  If the recipient is
    guarnateed to disard any packet except the one with the next
    consecutive number, the window size can be as large as the packet
    number size minus 1." [4]

See also Homework problems 4 and 5 in Section 1.


# References

[1] Dimitri P. Bertsekas, Robert Gallager, "Data Networks, 2nd
    edition", 1992, ISBN-0-13-200916-1

[2] Section 2.8.2 "Packet Numbering, Window Flow Control, and Error
    Recovery" of [1], pp. 115-116.

[3] Radia Perlman, "Interconnections: bridges, routers, switches and
    internetworking protocols, 2nd edition", 1999, ISBN-0-201-63448-1

[4] Section 1.4 "Reliable Data Transfer Protocols" of [3], p. 16

[5] Nancy Lynch, Yishay Mansour, Alan Fekete, "The Data Link Layer:
    Two Impossibility Results", PODC '88: Proceedings of the seventh
    annual ACM Symposium on Principles of distributed computing,
    January 1988, https://dl.acm.org/doi/abs/10.1145/62546.62572

[6] Da-Wei Wang, Lenore D. Zuck, "Tight Bounds for the Sequence
    Transmission Problem", PODC '89: Proceedings of the eighth annual
    ACM Symposium on Principles of distributed computing, June 1989,
    https://doi.org/10.1145/72981.72986
