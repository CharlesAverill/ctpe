---
title: "auto - CTPE"
---

## [auto](/ctpe/Automation/auto.html)

`auto` does a recursive search through a specified knowledge base in order to solve goals.
If `auto` cannot completely solve a goal, it succeeds with no changes to the goal.

The knowledge bases that `auto` uses are called [**Hint Databases**](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#hintdatabases).
Hint databases are provided by the standard library, and can also be created and added to by users.
Hint databases can contain a variety of hint types, including but not limited to:

- `Constructors`: `auto` will now try to apply each of the constructors for a given `Inductive` type
- `Unfold`: `auto` will now try to unfold a given definition - helpful when trivial simplification isn't enough
- `Resolve`: `auto` will now try to `simple apply` a given lemma 

The default hint database used by `auto` when no other database is specified is `core`.

### Syntax

```coq
(* Simple usage *)
auto.

(* Using a specific database *)
auto with bool.

(* Using a specific lemma *)
auto using example.
```

### Examples

Before
```coq
P: Prop
H: P
=========================
1/1
0 = 0 /\ True /\ P
```

```coq
auto.
```

After
```coq
No more goals.
```

Script
```coq
Create HintDb automation.
Lemma mul_1_r : forall n, n * 1 = n. 
Proof. induction n. auto. simpl. now rewrite IHn. Qed.
Hint Resolve mul_1_r : automation.

Lemma x : (forall n, n * 1 = n) /\ (true = true). 
Proof. auto with automation. Qed.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.auto)

["More Automation" - Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/Auto.html)

["A Streamlined Treatment of Automation" - Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/AltAuto.html)

["Theory and Practice of Automation in Coq Proofs" - Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/UseAuto.html)

[Hint Databases](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#hintdatabases)

<hr>
