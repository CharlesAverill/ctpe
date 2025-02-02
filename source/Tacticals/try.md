---
title: "try - CTPE"
---

## try

The `try` tactical executes a provided tactic, catching any errors and always succeeding.

### Syntax

```coq
(* Simple usage *)
try reflexivity.
```

### Examples

Before
```coq
n: nat
=========================
1/1
n + 0 = n
```

```coq
try reflexivity.
```

After
```coq
n: nat
=========================
1/1
n + 0 = n
```

Alternatively,

```coq
try apply add_0_r.
```

```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.try)
