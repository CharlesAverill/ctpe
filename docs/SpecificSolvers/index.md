---
title: "Specific Solvers - CTPE"
---

# [Specific Solvers](/ctpe/SpecificSolvers/index.html)

Each tactic in this group exists to solve a very specific kind of goal.
They're fairly simple to learn about and use, because their goal targets are such small groups that there are hardly any degrees of freedom for automation to be required.
Essentially all Coq proofs include some of these (whether they're written by the programmer or called by more complex tactics).


## [reflexivity](/ctpe/SpecificSolvers/reflexivity.html)

`reflexivity` solves goals which state that a term is equal to itself.
`reflexivity` has some simplification power, but not as much as [`simpl`](/ctpe/Simplification/simpl.html).
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
=========================
1/1
n = n
```

```coq
reflexivity.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html?highlight=reflexivity#coq:tacn.reflexivity)

<hr>


## [assumption](/ctpe/SpecificSolvers/assumption.html)

`assumption` solves goals in which there exists an assumption that directly proves the goal (no simplification).
This tactic will fail if there does not exist such an assumption.

### Syntax

```coq
(* Simple usage *)
assumption.
```

### Examples

Before
```coq
P: Prop
H: P
=========================
1/1
P
```

```coq
assumption.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.assumption)

<hr>


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
=========================
1/1
1 <> 2
```

```coq
discriminate.
```

After
```coq
No more goals.
```

Before
```coq
=========================
1/1
"hello" <> "world"
```

```coq
discriminate.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.discriminate)

<hr>


## [exact](/ctpe/SpecificSolvers/exact.html)

`exact` allows users to solve goals by providing a proof object directly.
This tactic will fail if the provided proof object does not prove the goal.

### Syntax

```coq
(* Simple usage *)
exact I.
```

### Examples

Before
```coq
=========================
1/1
True
```

```coq
exact I.
```

After
```coq
No more goals.
```

Before
```coq
n: nat
=========================
1/1
n + 5 = n + 5
```

```coq
exact (eq_refl (n + 5)).
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.exact)

<hr>


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
=========================
1/1
False
```

```coq
contradiction.
```

After
```coq
No more goals.
```

Before
```coq
x, y: nat
H: x = y
H0: x <> y
=========================
1/1
x = x + y
```

```coq
contradiction.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.contradiction)

<hr>

<hr>
