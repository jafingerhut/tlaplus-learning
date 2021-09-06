# Introduction


# Basic AB properties

The `AB` spec with safety only, satisfies the `ABSpec` safety only
part of its spec.

```bash
tlc AB_ql3.tla -config AB_ql3_safety_only.cfg
```

The `AB` spec with strong fairness for both `ARcv` and `BRcv` steps,
satisfies `ABSpec` safety and liveness spec.

```bash
tlc AB_ql3.tla -config AB_ql3_fss_satisfies_fs.cfg
```

The `AB` spec with weak fairness for either or both of the `ARcv` and
`BRcv` steps, does not satisfy `ABSpec` safety and liveness spec.

```bash
tlc AB_ql3.tla -config AB_ql3_fww_satisfies_fs.cfg
tlc AB_ql3.tla -config AB_ql3_fsw_satisfies_fs.cfg
tlc AB_ql3.tla -config AB_ql3_fws_satisfies_fs.cfg
```


# Checking what properties that AB_trigacks satisfies

`AB_trigacks` is a modified version of `AB` where B does _not_
periodically send ack messages.  There is no longer a `Bsnd` step like
`AB` has.  Instead, B only sends an ack message during the `Brcv`
step.

My motivation for doing this is to more closely model some
implementations of reliable transport protocols, where the receiver
can be a bit simpler in its implementation, because it does not need
any kind of retransmission timeout mechanism to decide when to send
ack messages.  Instead it is purely "reactive" to messages received
from A.  For example, several P4 programmable devices are better at
being reactive devices, and it is extra effort to make them have
retransmission timers and retransmit messages.

Note that because the names of defined spec formulas, including the
ones with liveness properties, are the same in `AB` and `AB_trigacks`,
I can reuse the `.cfg` files from the previous section here.

Safety only part of `ABSpec` is satisfied:

```bash
tlc AB_trigacks_ql3.tla -config AB_ql3_safety_only.cfg
```

The `AB_trigacks` spec with strong fairness for both `ARcv` and `BRcv`
steps, satisfies `ABSpec` safety and liveness spec.

```bash
tlc AB_trigacks_ql3.tla -config AB_ql3_fss_satisfies_fs.cfg
```

Running the following, with only weak fairness for the `ARcv` and
`Brcv` steps, violates temporal properties, as expected.

```bash
tlc AB_trigacks_ql3.tla -config AB_ql3_fww_satisfies_fs.cfg
```

The counterexample found was an infinite repetition of the sequence of
steps `ASnd`, `LostMsgAtoB`.

The following run also violates temporal properties, with the same
counterexample as above.  Even though `ARcv` has strong fairness
guarantees, `ARcv` is never enabled by the counterexample sequence of
steps.

```bash
tlc AB_trigacks_ql3.tla -config AB_ql3_fsw_satisfies_fs.cfg
```

The following run also violates temporal properties:

```bash
tlc AB_trigacks_ql3.tla -config AB_ql3_fws_satisfies_fs.cfg
```

The counterexample found was an infinite repetition of this sequence
of steps:

* `ASnd`
* `BRcv`, which causes `B` to send an ack message
* `LoseMsgBtoA`

Step `ARcv` has only weak fairness, so the above sequence does not
violate that, since `ARcv` is not continuously enabled.


# AB_nonfifo does not satisfy safety properties of ABSpec

`AB_nonfifo` is a modified version of `AB` where messages can be
reordered after being sent by A, before being received by B, and
similarly in the opposite direction from B to A.

My motivation for doing this is to model situations where there are
potentially multiple network devices between A and B in a network, and
these devices can reorder messages.  For example, here are some
possible reasons for reordering of messages, depending upon how the
network is configured:

* [Equal-cost
  multi-path](https://en.wikipedia.org/wiki/Equal-cost_multi-path_routing)
  (ECMP) routing is used, and thus different messages intentionally
  can take different paths.
* [Link aggregation](https://en.wikipedia.org/wiki/Link_aggregation)
  groups (LAGs) are configured between devices in the network.
* A [routing protocol](https://en.wikipedia.org/wiki/Routing_protocol)
  is configured in the network.  When links fail, or when new links
  are brought up into service, the path used by packets after the
  routing protocol changes its routing tables could have lower latency
  after the update than the path in use before the update.

The last reason given above is the most fundamental.  While it is easy
to disable ECMP and avoid use of LAGs in a network, avoiding the use
of any kind of routing protocol leaves one with no way to react to
changes in the set of working devices and links in the network.

Note that because the names of defined spec formulas, including the
ones with liveness properties, are the same in `AB` and `AB_nonfifo`,
I can reuse the `.cfg` files from the previous section here.

When messages can be reordered between A and B in the network, TLC
easily finds a counterexample to the safety properties of `ABSpec`, as
it should.

```bash
tlc -difftrace AB_nonfifo_ql3.tla -config AB_ql3_safety_only.cfg
```

Here is a counterexample it found when I tried running that command:

```
State 1: <Initial predicate>
/\ AtoB = {}
/\ BVar = <<d1, 1>>
/\ AVar = <<d1, 1>>
/\ BtoA = {}

State 2: <ASnd line 46, col 9 to line 47, col 41 of module AB_nonfifo>
/\ AtoB = {<<d1, 1>>}

State 3: <BSnd line 68, col 9 to line 69, col 41 of module AB_nonfifo>
/\ BtoA = {1}

State 4: <ARcv line 56, col 9 to line 62, col 35 of module AB_nonfifo>
/\ AVar = <<d1, 0>>
/\ BtoA = {}

State 5: <ASnd line 46, col 9 to line 47, col 41 of module AB_nonfifo>
/\ AtoB = {<<d1, 0>>, <<d1, 1>>}

State 6: <BRcv line 75, col 9 to line 81, col 35 of module AB_nonfifo>
/\ AtoB = {<<d1, 1>>}
/\ BVar = <<d1, 0>>

State 7: <BRcv line 75, col 9 to line 81, col 35 of module AB_nonfifo>
/\ AtoB = {}
/\ BVar = <<d1, 1>>
/\ AVar = <<d1, 0>>
/\ BtoA = {}

368 states generated, 108 distinct states found, 28 states left on queue.
```

Note that the message `<<d1, 0>>` sent by A in state 5 is received by
B in state 6, before the message `<<d1, 1>>` that was sent earlier by
A in state 2.

If we ignore the values of `AtoB` and `BtoA`, and focus only on the
values of `AVar` and `BVar` in the sequence of states, we have:

```
State     AVar       BVar
-----  ---------  ---------
  1    <<d1, 1>>  <<d1, 1>>
  2    <<d1, 1>>  <<d1, 1>>
  3    <<d1, 1>>  <<d1, 1>>
  4    <<d1, 0>>  <<d1, 1>>
  5    <<d1, 0>>  <<d1, 1>>
  6    <<d1, 0>>  <<d1, 0>>
  7    <<d1, 0>>  <<d1, 1>>
```

If we remove the steps that are stuttering steps for `ABSpec`, that
leaves us with this sequence:

```
State     AVar       BVar    Steps in ABSpec that are allowed to be taken
-----  ---------  ---------  ----------------------------------------------
  1    <<d1, 1>>  <<d1, 1>>  only step A
  4    <<d1, 0>>  <<d1, 1>>  only step B
  6    <<d1, 0>>  <<d1, 0>>  only step A, which if taken would lead to AVar
                             changing, but BVar remaining the same
  7    <<d1, 0>>  <<d1, 1>>
```

Steps 1 to 4 and 4 to 6 are allowed by `ABSpec`, but step 6 to 7 is
not.


# AB_nonfifoBtoA does not satisfy safety properties of ABSpec

`AB_nonfifoBtoA` is a modified version of `AB_nonfifo` where messages
must be in FIFO order from A to B, but acknowledgements from B to A
can be reordered in the network.  I created it after `AB_nonfifo`,
simply to verify that even if only acknowledgement messages can be
reordered, `AB_nonfifoBtoA`, it still does not satisfy the desired
safety properties of `ABSpec`.

```bash
tlc -difftrace AB_nonfifoBtoA_ql3.tla -config AB_ql3_safety_only.cfg
```

Here is a counterexample it found when I tried running that command:

```
State 1: <Initial predicate>
/\ AtoB = <<>>
/\ BVar = <<d1, 1>>
/\ AVar = <<d1, 1>>
/\ BtoA = {}

State 2: <BSnd line 75, col 9 to line 76, col 41 of module AB_nonfifoBtoA>
/\ BtoA = {1}

State 3: <ARcv line 63, col 9 to line 69, col 35 of module AB_nonfifoBtoA>
/\ AVar = <<d1, 0>>
/\ BtoA = {}

State 4: <ASnd line 53, col 9 to line 54, col 41 of module AB_nonfifoBtoA>
/\ AtoB = <<<<d1, 0>>>>

State 5: <BSnd line 75, col 9 to line 76, col 41 of module AB_nonfifoBtoA>
/\ BtoA = {1}

State 6: <BRcv line 82, col 9 to line 87, col 35 of module AB_nonfifoBtoA>
/\ AtoB = <<>>
/\ BVar = <<d1, 0>>

State 7: <BSnd line 75, col 9 to line 76, col 41 of module AB_nonfifoBtoA>
/\ BtoA = {0, 1}

State 8: <ARcv line 63, col 9 to line 69, col 35 of module AB_nonfifoBtoA>
/\ AVar = <<d1, 1>>
/\ BtoA = {1}

State 9: <ARcv line 63, col 9 to line 69, col 35 of module AB_nonfifoBtoA>
/\ AtoB = <<>>
/\ BVar = <<d1, 0>>
/\ AVar = <<d1, 0>>
/\ BtoA = {}

1408 states generated, 301 distinct states found, 56 states left on queue.
```

Note that the acknowledgement message `0` sent by B in state 7 is
received by A in state 8, before the message `1` that was sent earlier
by B in state 5.

If we ignore the values of `AtoB` and `BtoA`, and focus only on the
values of `AVar` and `BVar` in the sequence of states, we have:

```
State     AVar       BVar
-----  ---------  ---------
  1    <<d1, 1>>  <<d1, 1>>
  2    <<d1, 1>>  <<d1, 1>>
  3    <<d1, 0>>  <<d1, 1>>
  4    <<d1, 0>>  <<d1, 1>>
  5    <<d1, 0>>  <<d1, 1>>
  6    <<d1, 0>>  <<d1, 0>>
  7    <<d1, 0>>  <<d1, 0>>
  8    <<d1, 1>>  <<d1, 0>>
  9    <<d1, 0>>  <<d1, 0>>
```

If we remove the steps that are stuttering steps for `ABSpec`, that
leaves us with this sequence:

```
State     AVar       BVar    Steps in ABSpec that are allowed to be taken
-----  ---------  ---------  ----------------------------------------------
  1    <<d1, 1>>  <<d1, 1>>  only step A
  3    <<d1, 0>>  <<d1, 1>>  only step B
  6    <<d1, 0>>  <<d1, 0>>  only step A
  8    <<d1, 1>>  <<d1, 0>>  only step B, which if taken would lead to BVar
                             changing, but AVar remaining the same
  9    <<d1, 0>>  <<d1, 0>>
```

All steps up to 6 to 8 are allowed by `ABSpec`, but step 8 to 9 is
not.


# ABQSpec variant of ABSpec

I do not know if this is useful or not yet.  ABQSpec is similar to
ABSpec, but it has variables to remember the history of messages sent
from A and acknowledged by B, and a history of messages received by B.
This is really a learning experiment at this point, and perhaps has
significant disadvantages as compared to how ABSpec is written, but my
hope is that I can create a variant of AB that extends ABQSpec, such
that ABQSpec detects problems with safety and/or liveness properties
of those new versions of AB.

To verify that `ABQSpec_qla`, which is just `ABQSpec` with some
constraints on the lengths of its sequence variables to avoid a
too-large number of states to explore, satisfies a couple of
invariants:

```bash
tlc ABQSpec_ql.tla -config ABQSpec_ql_safety_only.cfg
```


# ABQ variant of AB

It was not very difficult to modify spec AB to create spec ABQ that
satisfies all of the safety properties of ABQSpec.  See files
`ABQ.tla` and `ABQ_ql.tla`, which give no errors with this command:

```bash
tlc ABQ_ql.tla -config AB_ql3_safety_only.cfg
```

I expected this run with strong fairness of `ARcv` and `BRcv` steps to
satisfy the liveness properties of `ABQSpec`, but for some reason it
finds an error:

```bash
tlc -difftrace ABQ_ql.tla -config AB_ql3_fss_satisfies_fs.cfg
```

The counterexample trace of steps is:

```
State 1: <Initial predicate>
/\ BRcvd = <<>>
/\ AtoB = <<>>
/\ BVar = <<d1, 1>>
/\ AWait = <<>>
/\ AVar = <<d1, 1>>
/\ BtoA = <<>>
/\ AAcked = <<>>

State 2: <BSnd line 86, col 5 to line 87, col 59 of module ABQ>
/\ BtoA = <<1>>

State 3: <ASnd line 58, col 5 to line 59, col 59 of module ABQ>
/\ AtoB = <<<<d1, 1>>>>

State 4: <BRcv line 94, col 5 to line 101, col 46 of module ABQ>
/\ AtoB = <<>>

Back to state 1: <LoseMsgBtoA line 125, col 16 to line 127, col 72 of module ABQ>
```

I believe the problem is that I modified step `ARcv` to have these
preconditions:

```
ARcv ==
    /\ BtoA /= << >>
    /\ AWait /= << >>
    /\ ... next state conditions omitted ...
```

Because my definition of `FairSpecSS` in `ABQ.tla` when I ran the
`tlc` command above was this:

```
FairSpecSS == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd)
```

there was no requirement to ever take any `AWrite(d)` steps.  Since
none were taken in the counterexample trace above, step `ARcv` was
never enabled.

If I add a weak fairness requirement for taking `AWrite(d)` steps, as
shown below, then `ARcv` should become enabled.

```
FairSpecSS == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                        WF_vars(ASnd) /\ WF_vars(BSnd) /\
			\A d \in Data: WF_vars(AWrite(d))
```

After making that change, and also updating `vars` to include all of
the variables in `ABQ`, the following command gave no errors, and
found 37632 distinct states:

```bash
tlc -difftrace ABQ_ql.tla -config AB_ql3_fss_satisfies_fs.cfg
```


# ABQ_nonfifo does not satisfy safety properties of ABQSpec

This is really retreading old ground that was done in the section
above named [AB_nonfifo does not satisfy safety properties of
ABSpec](#ab_nonfifo-does-not-satisfy-safety-properties-of-abspec).
The only difference is that here we are using ABQSpec instead of
ABSpec, and ABQ_nonfifo instead of AB_nonfifo.  See that section for
motivation.

When messages can be reordered between A and B in the network, TLC
easily finds a counterexample to the safety properties of `ABSpec`, as
it should.

```bash
tlc -difftrace ABQ_nonfifo_ql.tla -config AB_ql3_safety_only.cfg
```

The counterexample found is nearly identical to the one in the earlier
section linked above.  The only difference is that there is one more
step, for `AWrite`, in order for A to be able to send a second
message.
