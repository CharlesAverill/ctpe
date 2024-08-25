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
=========================
1/1
1 = 2
```

```coq
try reflexivity.
```

After
```coq
=========================
1/1
1 = 2
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.try)
