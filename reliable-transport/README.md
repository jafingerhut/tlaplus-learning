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
