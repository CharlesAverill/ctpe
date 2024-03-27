# Coq Tactics in Plain English

If you're like me, one of the biggest shortcomings of the Coq ecosystem is the abysmally-complicated [tactic reference documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html).
It is exhaustive (which is better than lacking), but I have a few specific issues with it:

1. Entries are far too verbose. I usually don't _need_ an exhaustive explanation of what a tactic does.
2. Documentation specifics become out-of-date due to the sheer number of tactics and how many ways they can interact with a goal state.
3. BNF grammar is not that easy to read. This one might be more controversial, but I would rather have **examples** of syntax than a homework problem.
4. There are not enough examples of tactics being used, and the examples that do exist are too often not representative of what a beginner might see.

For these reasons, I've decided to compile a reference document of every tactic that I've ever used, addressing the problems above via the following solutions.

1. Entries will be written at an undergraduate level, assuming a basic understanding of the Coq system. Sometimes, this will require reading the pages for other tactics before the one you really want to know about, but I think that's a fair compromise. Explanations will focus on what configurations of goal states the tactic is useful or not useful for.
2. Entries will start general and become more specific as one reads on. This will ensure minimal maintenance is necessary as tactics change over time.
3. Entries will include syntax *examples* rather than BNF grammars
4. Entries will contain multiple examples, including goal states before and after executing the tactics. Small MRE Coq scripts may be included.
5. As a fallback, links to other resources, at minimum the official documentation, will be included in each entry.

# Table of Contents

1. [Generalization](#generalization)
2. [Simplification](#simplification)

# Generalization

Summary

## intros

Typically the first tactic a Coq user ever utilizes.
`intros` looks for assumptions in your goal and moves them to the goal's assumption space.

More specifically, `intros` [specializes](glossary.md#specialize) a goal by looking for [type inhabitation](glossary.md#type_inhabitation) and proposition assumptions and moving them into the assumption space.
For example, if you write `forall (n : nat), n + 0 = n`, the `forall` is acting as an assumption that there is a value of type `nat` that we can call `n`.
Calling `intros` here will provide you an assumption `n` that there is a value of type `nat`.

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
A, B, C : Prop
ATrue : A
BTrue : B
-------------------------
1/1
C -> A /\ C
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.intros)

# Simplification

Summary

## simpl

A short summary of what the tactic does, starting the most generally and ending the most specifically.

### Syntax

```coq
(* Example 1 *)
tactic argument in H with x.

(* Example 2 *)
tactic -> t.
```

### Examples

Before
```coq
n: nat
-------------------------
1/2
False
-------------------------
2/2
True
```

```coq
tactic n.
```

After
```coq
n: nat
-------------------------
1/2
True
-------------------------
2/2
True
```

Script
```coq
Theorem test : 
    forall (n : nat), False /\ True.
Proof.
    tactic n. all: auto.
Qed.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.tactic)
