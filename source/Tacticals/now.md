---
title: now - CTPE
---

## now

`now tactic` is simply notation for `tactic; easy` ([`easy` tactic](/ctpe/Automation/easy.html)).

### Syntax

```coq
now split.
```

### Examples

Before
```coq
=========================
1/1
True /\ 42 = 14 * 3
```

```coq
now split.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.now)
