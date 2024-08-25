---
title: split - CTPE
---

## [split](/ctpe/Simplification/split.html)

`split` is primarily used to break a single goal of the form `A /\ B` into two new goals `A` and `B`.

You will often notice that `split` seems to solve some of the subgoals that it generates.
This is because `split` is just shorthand for `constructor 1` (see the [`constructor` tactic](/ctpe/CaseAnalysis/constructor.html)).

Looking at the definition of `/\` (or `and`):
```coq
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B.
```
we can see that `and` has a single constructor called `conj` - so `constructor 1` simply reduces to `apply conj`, which would give us goals `A` and `B` due to the impliciations that it carries.

### Syntax

```coq
split.
```

### Examples

Before
```coq
=========================
1/1
True /\ False
```

```coq
split.
```

After
```coq
=========================
1/2
True
=========================
2/2
False
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.split)

<hr>
