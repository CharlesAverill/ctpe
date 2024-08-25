---
title: "contradiction - CTPE"
---

## [contradiction](/ctpe/SpecificSolvers/contradiction.html)

`contradiction` solves goals in which there exist contradictory hypotheses.
These contradictions generally take the form of a `False` hypothesis or a pair of hypotheses that state `P` and `~ P` for some proposition.
This tactic will fail if no such contradictions exist.

### Syntax

```coq
(* Simple usage *)
contradiction.
```

### Examples

Before
```coq
H: False
-------------------------
1/1
False
```

```coq
contradiction.
```

After
```coq
Proof finished
```

Before
```coq
x, y: nat
H: x = y
H0: x <> y
-------------------------
1/1
x = x + y
```

```coq
contradiction.
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.contradiction)

<hr>
