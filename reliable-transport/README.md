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
modified it so that the sender keeps a record of all messages it wants
to send in variable `AMsgs`, and a record of all messages the receiver
receives (in correct alternating bit sequence number order) in a
variable `BMsgs`.  This command shows that it implements `RTSpec`'s
safety properties.

```bash
tlc AB_ql.tla -config AB_ql_safety_only.cfg
```

And this command shows that it satisfies `RTSpec`'s liveness
properties:

```bash
tlc AB_ql.tla -config AB_ql_fss_satisfies_fs.cfg
```

I am a little surprised that AB implements the liveness properties,
even using only WF on steps:

```bash
tlc AB_ql.tla -config AB_ql_fww_satisfies_fs.cfg
```

I am very surprised that the following run finds no errors when
checking liveness properties.

```bash
tlc AB_ql.tla -config AB_ql_fweaker_satisfies_fs.cfg
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

`GBN.tla` contains a spec that is reasonably close to an
implementation of a Go-Back-N sender and receiver, with FIFO links
between them.

The command below checks that it implements the safety properties of
`RTSpec` when using 4 different sequence numbers (`NSeq`=4) and the
sender limits itself to send at most 2 messages later than the last
one that was acknowledged (the window size `W`=2).

```bash
tlc -difftrace GBN_ql.tla -config GBN_ql_NSeq-4-W-2-safety_only.cfg
```

Even with only 2 possible values in the set `Data` and constraints on
various queue lengths that are quite short, TLC explores 423,000
distinct states.
