---
title: "reflexivity - CTPE"
---

## [reflexivity](/SpecificSolvers/reflexivity.html)

`reflexivity` solves goals which state that a term is equal to itself.
`reflexivity` has some simplification power, but not as much as [`simpl`](/Simplification/simpl.html).
This tactic will fail if it cannot solve the goal.

`reflexivity` makes an attempt to simplify the goal and then `apply eq_refl`, where `eq_refl` is the sole constructor of the `eq` Inductive Proposition, stating that `forall {A : Type} (a : A), eq a a`.

### Syntax

```coq
(* Simple usage *)
reflexivity.
```

### Examples

Before
```coq
n: nat
-------------------------
1/1
n = n
```

```coq
reflexivity.
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html?highlight=reflexivity#coq:tacn.reflexivity)

<hr>
