---
title: "Automation - CTPE"
---

# [Automation](/ctpe/Automation/index.html)

This is basically a catch-all category for tactics that do a lot of things at once.
This category of tactics generally intends to solve a large category of simple goals to reduce the load of the proof writer.


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


## [trivial](/ctpe/Automation/trivial.html)

`trivial` is essentially a non-recursive [`auto`](/ctpe/Automation/auto.html).
`trivial` is best utilized when a lemma that exactly matches the goal already exists in the hint database.

### Syntax

```coq
(* Simple usage *)
trivial.

(* Using a specific database *)
trivial with bool.
```

### Examples

Script
```coq
Theorem trivial_example : forall {X : Type} (n : X), 
    n = n.
Proof.
    trivial.
Qed.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.trivial)

<hr>


## [easy](/ctpe/Automation/easy.html)

`easy` throws many common "closing tactics" at a goal to solve a large category of simple problems.
`easy` will attempt to use:

- [`trivial`](/ctpe/Automation/trivial.html)

- [`reflexivity`](/ctpe/SpecificSolvers/reflexivity.html)

- [`symmetry`](/ctpe/Rewriting/symmetry.html)

- [`contradiction`](/ctpe/SpecificSolvers/contradiction.html)

- [`inversion`](/ctpe/CaseAnalysis/inversion.html)

- [`intros`](/ctpe/Generalization/intros.html)

- [`split`](/ctpe/Simplification/split.html) (this begins a recursive call of `easy`)

- [`destruct`](/ctpe/CaseAnalysis/destruct.html) (on hypotheses with conjunctions)

`easy` is the base form of the [`now`](/ctpe/Tacticals/now.html) tactical.

### Syntax

```coq
easy.
```

### Examples

Before
```coq
P: Prop
H: P
=========================
1/1
True /\ 42 = 14 * 3 /\ P
```

```coq
easy.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.easy)

<hr>


## [idtac](/ctpe/Automation/idtac.html)

`idtac` leaves a goal completely unchanged. This tactic will never fail.

A term can be provided as an argument to print a message to the console.
String and integers are printed literally rather than via their type's pretty-printer.

`idtac` is sometimes useful when you have many goals selected and only want to operate on some of them.

### Syntax

```coq
(* Simple usage *)
idtac.

(* Print a message *)
idtac "Hello World!".
```

### Examples

Before
```coq
=========================
1/1
True
```

```coq
idtac.
```

After
```coq
=========================
1/1
True
```

Before
```coq
n: nat
=========================
1/1
n + 0 = n
```

```coq
(* Only apply reflexivity to the n = 0 case. Leave the n = S n' case unaffected *)
induction n; [reflexivity | idtac].
```

After
```coq
n : nat
IHn : n + 0 = n
=========================
1/1
S n + 0 = S n
```
### Resources

[Reference Documentation](https://coq.inria.fr/doc/v8.10/refman/proof-engine/ltac.html#coq:tacn.idtac)

<hr>


## [fail](/ctpe/Automation/fail.html)

`fail` always fails.

This is sometimes useful if you're building a complex tactic with try-catch behavior.

### Syntax

```coq
(* Simple usage *)
fail.
```

### Examples

Before
```coq
=========================
1/1
True
```

```coq
fail.
```

After
```coq
Error: Tactic failure.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.fail)

<hr>

<hr>
