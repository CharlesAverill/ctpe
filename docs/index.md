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

There are many other guides to Coq tactics, you should check them out too if I don't have what you need:

- [Coq Tactics Cheatsheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html)
- [More Basic Tactics - Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html)
- [Detailed examples of tactics](http://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual012.html)
- [Coq Tricks for Beginners with Too Many Examples](https://le.qun.ch/en/blog/coq/)
- [Coq Cheatsheet](https://julesjacobs.com/notes/coq-cheatsheet/coq-cheatsheet.pdf)
- [Coq cheat sheet](https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf)

<hr>

<hr>

# Table of Contents

1. [Generalization](#generalization)
2. [Simplification](#simplification)
3. [Case Analysis](#case-analysis)

<hr>

<hr>

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

<hr>

<hr>

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
1/1
4 = 1 + 3
```

### Resources

TODO : Below link should be updated with the `master` version once it makes its way into the tree

[Reference Documentation](https://coq.inria.fr/doc/V8.11.0/refman/proof-engine/tactics.html#coq:tacn.simpl)

<hr>

<hr>

---
title: Case Analysis - CTPE
---

# [Case Analysis](/ctpe/CaseAnalysis/index.html)
Summary

---
title: destruct - CTPE
---

## [destruct](/ctpe/CaseAnalysis/destruct.html)
`destruct` allows for case analysis on inductive terms or assumptions.
It can be used to split assumptions with conjunctions and disjunctions, as well as existential assumptions.
The arguments of `destruct` are [patterns](/ctpe/glossary.html#pattern).

### Syntax

```coq
(* Simple usage *)
destruct H.

(* Destruct a term and introduce a hypothesis E showing its equivalence to the form it took *)
destruct n eqn:E.

(* Providing names for newly-introduced terms *)
destruct H as [H0 [H1 H2]].

(* Providing only some names for newly-introduced terms *)
destruct H as [H0 [? H1]].

(* Destructing multiple terms/hypotheses *)
destruct x as [| x0 x1], H as [[H1 H0] H2].

(* Providing names for newly-introduced terms in different generated subgoals *)
destruct H as [H1 | H2].
```

### Examples

Before
```coq
n: nat
-------------------------
n = 0 \/ 1 <= n
```

```coq
destruct n as [| n'] eqn:E.
```

After (first goal generated)
```coq
n: nat
E: n = 0
-------------------------
1/2
0 = 0 \/ 1 <= 0
```

After (second goal generated)
```coq
n, n': nat
E: n = S n'
-------------------------
1/1
S n' = 0 \/ 1 <= S n'
```

Script
```coq
Theorem destruct_example1 : forall n : nat,
    n = 0 \/ 1 <= n.
Proof.
    intros. destruct n as [| n'] eqn:E.
    - left. reflexivity.
    - right. apply le_n_S, le_0_n.
Qed.
```

Script
```coq
Theorem destruct_example2 : forall (P Q R : Prop),
    ((P /\ Q) /\ R) -> P /\ (Q /\ R).
Proof.
    intros P Q R H.
    destruct H as [[PTrue QTrue] RTrue]. split.
    - apply PTrue.
    - split. 
        -- apply QTrue.
        -- apply RTrue.
Qed.
```

Script
```coq
Theorem destruct_example3 : 
    forall (P Q R : Prop),
    (P \/ Q) -> P \/ Q \/ R.
Proof.
    intros. destruct H as [PTrue | QTrue].
    - left. assumption.
    - right. left. assumption.
Qed. 
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.tactic)

<hr>

---
title: inversion - CTPE
---

## [inversion](/ctpe/CaseAnalysis/inversion.html)
`inversion` looks at a given piece of structural evidence and draws conclusions from it.
If there are multiple sets of conclusions, `inversion` will generate a new proof obligation for each one.
Informally, `inversion` is doing a more specific form of the case analysis provided by [`destruct`](destruct.html) - where `destruct` essentially says "I don't know what this term is, so I'll prove a property for all of the possible forms of it," `inversion` says "I know exactly what terms could construct this hypothesis because of its definition, so I'll only prove a property for those terms."

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

After (first goal generated)
```coq
n: nat
H: n <= 1
H0: n = 1
-------------------------
1/2
1 = 0 \/ 1 = 1
```

After (second goal generated)
```coq
n: nat
H: n <= 1
m: nat
H1: n <= 0
H0: m = 0
-------------------------
1/1
n = 0 \/ n = 1
```

Script
```coq
Theorem inversion_example1 : 
    forall n, n <= 1 -> n = 0 \/ n = 1.
Proof.
    intros. inversion H. 
    - right. reflexivity.
    - inversion H1. left. reflexivity.
Qed.
```

Script
```coq
Inductive color : Type :=
| Red | Blue | Green | Cyan | Magenta | Yellow.

Inductive makes_white : color -> color -> color -> Prop :=
| RBG : makes_white Red Blue Green
| CMY : makes_white Cyan Magenta Yellow.

Theorem inversion_example2 : 
    forall (c1 c2 c3 : color),
    makes_white c1 c2 c3 ->
    (c1 = Red /\ c2 = Blue /\ c3 = Green) \/
    (c1 = Cyan /\ c2 = Magenta /\ c3 = Yellow).
Proof.
    intros c1 c2 c3 Hmw. inversion Hmw. 
    - left. repeat split.
    - right. repeat split.
Qed.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.inversion)

<hr>

---
title: induction - CTPE
---

## [induction](/ctpe/CaseAnalysis/induction.html)
`induction` is an extension of `destruct` that allows for case analysis on inductive terms, gaining an inductive hypothesis for each recursive subterm generated by the term destruction.
The arguments of `induction` are [patterns](/ctpe/glossary.html#pattern).

If the goal still contains named impliciations, `induction` can be used before introducing them with [intros](/ctpe/Generalization/intros.html).
In this case, if the argument to `induction` is not the first impliciation in the chain, all implications before it will be introduced to the goal's assumption space.

`induction` can act similarly to `inversion` under specific circumstances.
If you induct over an object that already contains subterms, you can [remember](/ctpe/Rewriting/remember.html) the subterm(s) and induct on the root object. Then, by an easy `inversion` on the hypothesis generated by `remember`, all cases that don't match the required form generated by the case analysis will be automatically solved by the [principle of explosion](/ctpe/glossary.html#explosion).

Sometimes, the automatically-generated induction principles for a type are not sufficient to prove some properties about terms with that type. 
In this case, it is possible to write a custom induction principle for a type and then use it with the `induction` tactic.

### Syntax

```coq
(* Simple usage *)
induction n.

(* Induct over a term and introduce a hypothesis E showing its equivalence to the form it took *)
induction n eqn:E.

(* Providing names for newly-introduced terms *)
induction n as [| n' IHn' ].

(* Using a custom induction principle *)
induction z using peano_ind.
```

### Examples

Before
```coq
n: nat
-------------------------
n + 0 = n
```

```coq
induction n as [| n' IHn' ].
```

After (first goal generated)
```coq
-------------------------
1/2
0 + 0 = 0
```

After (second goal generated)
```coq
n': nat
IHn' : n' + 0 = n'
-------------------------
1/1
S n' + 0 = S n'
```

Script
```coq
Theorem induction_example1 : forall (n : nat),
    n + 0 = n.
Proof.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.
```

Script
```coq
Require Import ZArith.
Open Scope Z.
Theorem induction_example2 : forall (x y : Z),
    x + y = y + x.
Proof.
    induction x using Z.peano_ind.
    - intros. simpl. rewrite Z.add_0_r. reflexivity.
    - intros. rewrite Z.add_succ_l. rewrite IHx.
      rewrite Z.add_comm. rewrite <- Z.add_succ_l.
      rewrite Z.add_comm. reflexivity.
    - intros. rewrite Z.add_pred_l. rewrite IHx.
      rewrite Z.add_comm. rewrite <- Z.add_pred_l.
      rewrite Z.add_comm. reflexivity.
Qed. 
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html#coq:tacn.tactic)

<hr>

<hr>

<hr>
