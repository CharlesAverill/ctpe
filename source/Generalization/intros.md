---
title: "intros - CTPE"
---

## intros

Typically the first tactics a Coq user ever utilizes.
`intros` finds assumptions builtin to your goal (usually in the form of a `forall` quantifier) and moves them to the goal's context (a.k.a. hypothesis space, assumption space).
This is similar to the first step of many informal, paper proofs, when the prover states "let there be some number n, ..."

More specifically, `intros` [specializes](glossary.md#specialize) a goal by looking for [type inhabitation](glossary.md#type_inhabitation) and proposition assumptions and moving them into the assumption space.
For example, if you write `forall (n : nat), n + 0 = n`, the `forall` is acting as an assumption that there is a value of type `nat` that we can call `n`.
Calling `intros` here will provide you an assumption `n` that there is a value of type `nat`.

`intros` will not introduce variables that are contained in opaque/wrapped definitions - <b>unless</b> an explicit name is provided for them.

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
=========================
forall (n : nat), n + 0 = n
```

```coq
intros x.
```

After
```coq
x: nat
=========================
1/1
x + 0 = x
```

Before
```coq
=========================
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
=========================
1/1
C -> A /\ C
```

Before (assume `P := forall (n : nat), n = n`)
```coq
=========================
1/1
P
```

```coq
intros.
```

After
```coq
=========================
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
=========================
1/1
n = n
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.intros)
