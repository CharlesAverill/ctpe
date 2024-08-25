---
title: "discriminate - CTPE"
---

## [discriminate](/ctpe/SpecificSolvers/discriminate.html)

`discriminate` solves goals that are trivial inequalities (something of the form `x <> y`).
This tactic will fail if the goal is not an inequality or is non-trivial.

### Syntax

```coq
(* Simple usage *)
discriminate.
```

### Examples

Before
```coq
-------------------------
1/1
1 <> 2
```

```coq
discriminate.
```

After
```coq
Proof finished
```

Before
```coq
-------------------------
1/1
"hello" <> "world"
```

```coq
discriminate.
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.discriminate)

<hr>
