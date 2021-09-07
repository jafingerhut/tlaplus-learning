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

`RTSpec` does not have any use of a bit to identify the sender
changing the data message at all.  It models the sequence of data
messages produces so far by the sender as a TLA+ sequence, and
similarly the receiver has a sequence of messages it has received so
far.  The sender has steps `AWrite(d)` that it can take to append a
new data message to its sequence of messages that it wants the
receiver to get a copy of, and step `B` causes the receiver to append
the next message in the sender's sequence to the receiver's sequence
(if there is one available that the receiver does not already have).

It should be possible to show that `AB` or any of its variants
implements `RTSpec`, but I may not bother doing that, unless I have
difficulty proving that more general transport protocols are correct.

In the mean time, as a simple test that `RTSpec` does not have any
glaringly obvious bugs, `RTSpec_ql.tla` adds a constraint on the
sender's sequence length to avoid an explosion in the number of
possible reachable states, and a definition of `NotReallyInvariant`
such that I know that `~NotReallyInvariant` should be true for some
reachable states.  I created that condition simply to verify that TLC
can found a counterexample that leads to a state violating that
condition, and the steps leading there look reasonable.  It can, using
this command:

```bash
tlc RTSpec_ql.tla
```

I will not copy it here, but when I first ran that command it produced
a counterexample with 11 states, and all of the steps and intermediate
values of spec variables looked correct.
