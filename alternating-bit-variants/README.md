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

