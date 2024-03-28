---
title: Generalization - CTPE
---

# [Generalization](/ctpe/Generalization/index.html)
Summary

---
title: intros - CTPE
---

## [intros](/ctpe/Generalization/intros.html)
Typically the first tactic a Coq user ever utilizes.
`intros` looks for assumptions in your goal and moves them to the goal's assumption space.

More specifically, `intros` [specializes](/ctpe/glossary.html#specialize) a goal by looking for [type inhabitation](/ctpe/glossary.html#type_inhabitation) and proposition assumptions and moving them into the assumption space.
For example, if you write `forall (n : nat), n + 0 = n`, the `forall` is acting as an assumption that there is a value of type `nat` that we can call `n`.
Calling `intros` here will provide you an assumption `n` that there is a value of type `nat`.

`intros` will not introduce variables that are contained in opaque/wrapped definitions.

A simpler tactic, `intro`, acts similarly but can only introduce one assumption, and will introduce variables contained in opaque/wrapped definitions.

### Syntax

```coq
(* Simple usage - introduces all named assumptions *)
intros.

(* Give specific names to assumptions as you introduce *)
intros n m x.

(* Split a conjunction or existential assumption upon introducing *)
intros [A B].
```

### Examples

Before
```coq
-------------------------
forall (n : nat), n + 0 = n
```

```coq
intros x.
```

After
```coq
x: nat
-------------------------
1/1
x + 0 = x
```

Before
```coq
-------------------------
forall (A B C : Prop), A /\ B -> C -> A /\ C
```

```coq
intros A B C [ATrue BTrue].
```

After
```coq
A, B, C: Prop
ATrue: A
BTrue: B
-------------------------
1/1
C -> A /\ C
```

Before (assume `P := forall (n : nat), n = n`)
```coq
-------------------------
1/1
P
```

```coq
intros.
```

After
```coq
-------------------------
1/1
P
```

Alternatively,

```coq
intro.
```

After
```coq
n: nat
-------------------------
1/1
n = n
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.intros)

<hr>

---
title: clear - CTPE
---

## [clear](/ctpe/Generalization/clear.html)
`clear` erases assumptions from the assumption space.
Multiple assumptions may be erased in one tactic via a space-separated list of assumptions.
`clear` will fail if an assumption passed into it contains as subterms other variables that still exist in the goal state.

### Syntax

```coq
(* Simple usage *)
clear H.

(* Clear multiple assumptions *)
clear H Heq X Y n.
```

### Examples

Before
```coq
n: nat
H, Hr1, Hr2: n = 0
IHn: n = 1
-------------------------
1/1
False
```

```coq
clear Hr1 Hr2.
```

After
```coq
n: nat
H: n = 0
IHn: n = 1
-------------------------
1/1
False
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.tactic)

<hr>

<hr>
