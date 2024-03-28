---
title: Coq Tactics in Plain English
---

---
title : Prologue - CTPE
---

# [Coq Tactics in Plain English](/ctpe/prologue.html)
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
3. [Evidence Analysis](#evidence-analysis)

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

---
title: Simplification - CTPE
---

# [Simplification](/ctpe/Simplification/index.html)
Summary

---
title: simpl - CTPE
---

## [simpl](/ctpe/Simplification/simpl.html)
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
1/2
4 = 1 + 3
```

### Resources

TODO : Below link should be updated with the `master` version once it makes its way into the tree

[Reference Documentation](https://coq.inria.fr/doc/V8.11.0/refman/proof-engine/tactics.html#coq:tacn.simpl)

---
title: Evidence Analysis - CTPE
---

# [Evidence Analysis](/ctpe/EvidenceAnalysis/index.html)
Summary

---
title: inversion - CTPE
---

## [inversion](/ctpe/EvidenceAnalysis/inversion.html)
`inversion` looks at a given piece of structural evidence and draws conclusions from it.
If there are multiple sets of conclusions, `inversion` will generate a new proof obligation for each one.

This tactic often generates many trivial equality assumptions that may clutter the assumption space. 
I recommend almost always following `inversion` with [`subst`](/) to immediately substitute away these equalities.

### Syntax

```coq
(* Standard usage *)
inversion H.
```

### Examples

Before
```coq
n: nat
H: n <= 1
-------------------------
1/1
n = 0 \/ n = 1
```

```coq
inversion H.
```

After (for first goal)
```coq
n: nat
H: n <= 1
H0: n = 1
-------------------------
1/2
1 = 0 \/ 1 = 1
```

After (for second goal)
```coq
n: nat
H: n <= 1
m: nat
H1: n <= 0
H0: m = 0
-------------------------
1/2
n = 0 \/ n = 1
```

Script
```coq
Theorem test : 
    forall n, n <= 1 -> n = 0 \/ n = 1.
Proof.
    intros. inversion H. 
    - right. reflexivity.
    - inversion H1. left. reflexivity.
Qed.

```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.inversion)
