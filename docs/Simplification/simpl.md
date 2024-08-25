---
title: "simpl - CTPE"
---

## [simpl](/Simplification/simpl.html)

`simpl` evaluates terms that are constructed of constant values - not variables.
`simpl` can also partially evaluate partially-constant values.

### Syntax

```coq
(* Simplify the goal as much as possible *)
simpl.

(* Simplify a hypothesis *)
simpl in H.

(* Simplify in the entire proof state *)
simpl in *.

(* Only simplify a specific term in a specific hypothesis *)
simpl (2 + 2) in H.
```

### Examples

Before
```coq
-------------------------
1/1
2 + 2 = 1 + 3
```

```coq
simpl (2 + 2).
```

After
```coq
-------------------------
1/1
4 = 1 + 3
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#coq:tacn.simpl)

<hr>
