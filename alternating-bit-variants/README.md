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
