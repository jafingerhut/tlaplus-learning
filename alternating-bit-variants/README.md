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


# AB_nonfifo does not even satisfy safety properties of ABSpec

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
