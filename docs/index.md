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
3. BNF grammar is not that easy to read. This one might be more controversial, but I would rather have **examples** of syntax than a homework problem.
4. There are not enough examples of tactics being used, and the examples that do exist are too often not representative of what a beginner might see.

For these reasons, I've decided to compile a reference document of every tactic that I've ever used, addressing the problems above via the following solutions.

1. Entries will be written at an undergraduate level, assuming a basic understanding of the Coq system. Sometimes, this will require reading the pages for other tactics before the one you really want to know about, but I think that's a fair compromise. Explanations will focus on what configurations of goal states the tactic is useful or not useful for.
2. Entries will start general and become more specific as one reads on. This will ensure minimal maintenance is necessary as tactics change over time.
3. Entries will include syntax *examples* rather than BNF grammars
4. Entries will contain multiple examples, including goal states before and after executing the tactics. Small MRE Coq scripts may be included.
5. As a fallback, links to other resources, at minimum the official documentation, will be included in each entry.

This guide doesn't aim to replace the reference documentation, it aims to be a stepping stone into the reference documentation that reduces the apprehension of those new to Coq.

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
3. [Specific Solvers](#specific-solvers)
4. [Rewriting](#rewriting)
5. [Case Analysis](#case-analysis)
6. [Automation](#automation)
7. [Tacticals](#tacticals)

<hr>

<hr>

---
title: Generalization - CTPE
---

# [Generalization](/ctpe/Generalization/index.html)
This group of tactics is often found at the beginnings of proofs. 
Generalization and its counterpart Specialization (both are included here) are concepts used to fine-tune how strong of a theorem is needed to continue.
Theorems that are too strong (specific) aren't useful for many different kinds of goals.
Theorems that are too weak (general) are frequently unprovable (even if their specified counterparts are!) and those that are provable are frequently harder to prove!

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

---
title: Simplification - CTPE
---

# [Simplification](/ctpe/Simplification/index.html)
This group of tactic aims to reduce the complexity of terms in a goal. 
They will not solve a goal, only convert it into what is a structurally smaller (although maybe not lexically smaller!) form of the original goal.

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

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#coq:tacn.simpl)

<hr>

---
title: unfold - CTPE
---

## [unfold](/ctpe/Simplification/unfold.html)
`unfold` replaces definition identifiers with the definition's contents, simplifying along the way.

### Syntax

```coq
(* Simple example *)
unfold plus.

(* Unfolding a definition in a hypothesis *)
unfold X in H.

(* Unfolding a definition in all hypotheses and the goal *)
unfold X in *.
```

### Examples

Given
```coq
Fixpoint bitlist (n : nat) : list bool :=
    match n with
    | O =>    true  :: nil
    | S n' => false :: (bitlist n')
    end.
```

Before
```coq
n: nat
l: list bool
H: bitlist (S (S n)) = false :: false :: l
-------------------------
1/1
bitlist (S n) = false :: l
```

```coq
unfold bitlist in *.
```

After
```coq
n: nat
l: list bool
H: false
     :: false
        :: (fix bitlist (n : nat) : list bool :=
              match n with
              | 0 => true :: nil
              | S n' => false :: bitlist n'
              end) n =
    false :: false :: l
-------------------------
1/1
false
 :: (fix bitlist (n0 : nat) : list bool :=
       match n0 with
       | 0 => true :: nil
       | S n' => false :: bitlist n'
       end) n = false :: l
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#coq:tacn.unfold)

<hr>

<hr>

---
title: Specific Solvers - CTPE
---

# [Specific Solvers](/ctpe/SpecificSolvers/index.html)
Each tactic in this group exists to solve a very specific kind of goal.
They're fairly simple to learn about and use, because their goal targets are such small groups that there are hardly any degrees of freedom for automation to be required.
Essentially all Coq proofs include some of these (whether they're written by the programmer or called by more complex tactics).

---
title: reflexivity - CTPE
---

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

---
title: assumption - CTPE
---

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
-------------------------
1/1
P
```

```coq
assumption
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.assumption)

<hr>

---
title: discriminate - CTPE
---

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
-------------------------
1/1
1 <> 2
```

```coq
discriminate.
```

After
```coq
Proof finished
```

Before
```coq
-------------------------
1/1
"hello" <> "world"
```

```coq
discriminate.
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.discriminate)

<hr>

---
title: exact - CTPE
---

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
-------------------------
1/1
True
```

```coq
exact I.
```

After
```coq
Proof finished
```

Before
```coq
n: nat
-------------------------
1/1
n + 5 = n + 5
```

```coq
exact (eq_refl (n + 5)).
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.exact)

<hr>

---
title: contradiction - CTPE
---

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
-------------------------
1/1
False
```

```coq
contradiction.
```

After
```coq
Proof finished
```

Before
```coq
x, y: nat
H: x = y
H0: x <> y
-------------------------
1/1
x = x + y
```

```coq
contradiction.
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.contradiction)

<hr>

<hr>

---
title: Rewriting - CTPE
---

# [Rewriting](/ctpe/Rewriting/index.html)
This group of tactics is very frequently used in the middles of proofs.
Rewriting in all of its forms is an efficient way to bring together previously-independent parts of a goal.

---
title: rewrite - CTPE
---

## [rewrite](/ctpe/Rewriting/rewrite.html)
`rewrite` takes an equivalence proof as input, like `t1 = t2`, and replaces all occurances of `t1` with `t2`.
Replacement of `t2` with `t1` can be achieved with the variant `rewrite <-` (rewrite backwards).
Multiple rewrites can be chained with one tactic via a list of comma-separated equivalence proofs.
Each of the equivalence proofs in the chain may be rewritten backwards.
`rewrite` will fail if there are no `t1`'s (in this example) to replace.

### Syntax

```coq
(* Replace t1 with t2 in the goal *)
rewrite t1_eq_t2.

(* Rewrite in an assumption *)
rewrite Eq in H.

(* Rewrite in the goal and all assumptions *)
rewrite HEq in *.

(* Rewrite multiple values *)
rewrite t1_eq_t2, <- x_eq_y, ht_eq_ht.
```

### Examples

Before
```coq
x, y: nat
H: x = y
-------------------------
x + y = y + y
```

```coq
rewrite H.
```

After
```coq
x, y: nat
H: x = y
-------------------------
y + y = y + y
```

Alternatively,
```coq
rewrite <- H.
```


```coq
x, y: nat
H: x = y
-------------------------
x + x = x + x
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#coq:tacn.rewrite)

<hr>

---
title: rename - CTPE
---

## [rename](/ctpe/Rewriting/rename.html)
`rename` changes the name of an introduced variable or assumption.

### Syntax

```coq
(* Simple example *)
rename x into y.
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
rename n into x.
```

After
```coq
x: nat
-------------------------
1/1
x = x
```
### Resources

[Reference Documentation](https://coq.inria.fr/doc/V8.13.2/refman/proof-engine/tactics.html#coq:tacn.rename)

<hr>

---
title: remember - CTPE
---

## [remember](/ctpe/Rewriting/remember.html)
`remember` gives a name to complex terms.
Specifically, `remember t` (where `t` has type `T`) introduces an assumption that there exists a member of type `T`, gives it a name such as `t0`, and provides another assumption that `t = t0`.

### Syntax

```coq
(* Simple usage *)
remember (5 + x).

(* Provide a name for the remembered term *)
remember ("hello world") as s.
```

### Examples

Before
```coq
x, y: nat
H: x + y = x
-------------------------
1/1
y = 0
```

```coq
remember (x + y) as sum.
```

After
```coq
x, y, sum: nat
Heqsum: sum = x + y
H: sum = x
-------------------------
1/1
y = 0
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/V8.13.2/refman/proof-engine/tactics.html#coq:tacn.remember)

<hr>

<hr>

---
title: Case Analysis - CTPE
---

# [Case Analysis](/ctpe/CaseAnalysis/index.html)
Case analysis is a core aspect of constructivist logic.
Although for many kinds of problems it is a low-level tool, it is ubiquitous among the foundations of all problems formalized in the Coq system.
The core idea is: "if I want to prove a property P holds for a term t, I can do so by writing multiple sub-proofs stating that for each form that t can have, P holds."

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

[Reference Documentation](https://coq.inria.fr/doc/V8.13.2/refman/proof-engine/tactics.html#coq:tacn.destruct)

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

[Reference Documentation](https://coq.inria.fr/doc/V8.13.2/refman/proof-engine/tactics.html#coq:tacn.induction)

<hr>

<hr>

---
title: Automation - CTPE
---

# [Automation](/ctpe/Automation/index.html)
This is basically a catch-all category for tactics that do a lot of things at once.
This category of tactics generally intends to solve a large category of simple goals to reduce the load of the proof writer.

---
title: auto - CTPE
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
-------------------------
1/1
0 = 0
```

```coq
auto.
```

After
```coq
Proof finished
```

Script
```coq
Create HintDb automation.
Lemma add_0_r : forall n, n * 1 = n. 
Proof. induction n. auto. simpl. now rewrite IHn. Qed.
Hint Resolve add_0_r : automation.

Lemma x : (forall n, n * 1 = n) /\ (true = true). 
Proof. auto with automation. Qed.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.auto)

[Hint Databases](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#hintdatabases)

<hr>

---
title: trivial - CTPE
---

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

<hr>

---
title: Tacticals - CTPE
---

# [Tacticals](/ctpe/Tacticals/index.html)
This category refers to tactics that modify the behavior of other tactics.
Important phrasing note for this section: a tactical is only a tactical when it doesn't have all of its arguments. A tactical with all of its arguments is a tactic.
Tacticals are heavily utilized in automation because they broaden the capabilities of the tactic language significantly, making it much more expressive.

For an interesting perspective on automation - and good examples of building "one shot proofs" (proofs that only contain one tactic) - check out [this post by Adam Chlipala](http://adam.chlipala.net/cpdt/html/Large.html).

---
title: try - CTPE
---

## [try](/ctpe/Tacticals/try.html)
The `try` tactical executes a provided tactic, catching any errors and always succeeding.

### Syntax

```coq
(* Simple usage *)
try reflexivity.
```

### Examples

Before
```coq
-------------------------
1/1
1 = 2
```

```coq
try reflexivity.
```

After
```coq
-------------------------
1/1
1 = 2
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.try)

<hr>

---
title: ; - CTPE
---

## [;](/ctpe/Tacticals/semicolon.html)
The infix `;` tactical is the sequencing tactical.
It applies the right tactic to all of the goals generated by the left tactic.

The `;` tactical is binary, so it takes two tactics (we will say `A` and `B`) as input.
`A` is executed.
If `A` does not fail and does not solve the goal, then `B` is executed for every goal that results from applying `A`.
If `A` solves the goal, then `B` is never called and the entire tactic succeeds.
This is useful when `A` generates lots of very simple subgoals (like preconditions of a theorem application) that can all be handled with another automation tactic.

The `;` tactical is left-associative.
Consider the tactic `A; B; C.`
If `A` generates goals `A1` and `A2`, then `B` will be applied to each.
Let's say that this results in a state with goals `A1'`, `A2'`, and `B'`.
`C` will now be applied to each of these.
This may not always be desired, and so parentheses can be used to force right-associativity.
Consider the tactic `A; (B; C)`.
If `A` generates goals `A1` and `A2`, then `B; C` will be applied to each.
The difference may not be crystal-clear in an abstract example such as this one, so check out the script below. 
Keep in mind that the difference is in the resulting state tree from calling these tactics:

```
A; B; C
├── A1              /*  Call B  */
│   └── A1'         /*  Call C  */
│       └── A1''
└── A2              /*  Call B  */
    └── A2'         /*  Call C  */
        └── A2''

A;(B;C)             /*  Call A  */
├── A1              /* Call B;C */
│   └── A1''
└── A2              /* Call B;C */
    └── A2''
```

Also keep in mind that this behavior is extremely versatile, the above tree "shortening" use is only one example.

Compare this tactical with [Prolog's semicolon tactical](https://www.swi-prolog.org/pldoc/man?predicate=%3B/2) and revel at some neat similarities!
For example, in Coq, `A;B` will backtrack if `B` fails and `A` can succeed in a *different way*.
The primary example of a tactic being able to succeed in multiple ways is the [`constructor`](/ctpe/CaseAnalysis/constructor.html) tactic.

### Syntax

```coq
(* Simple usage *)
split; reflexivity.

(* Left-associative chain *)
split; simpl; reflxivity.

(* Right-associative chain *)
split; (split; auto).
```

### Examples

Before
```coq
P, Q: Prop
H: Q
-------------------------
1/1
P \/ Q
```

```coq
constructor; assumption.
```

After
```coq
Proof finished
```
Note the definition of `or`:
```coq
Inductive or (A B : Prop) : Prop :=
| or_introl : A -> A \/ B 
| or_intror : B -> A \/ B.
```

<hr>

---
title: Goal Selectors - CTPE
---

## [Goal Selectors](/ctpe/Tacticals/goalselectors.html)
Goal selectors are a category of tacticals that apply a tactic to a specific goal or goals.

There are a number of goal selectors:

- `all`: Applies the tactic to all goals in focus **in series**
- `!`: If only one goal is in focus, apply the tactic. If not, this tactic fails
- `par`: Applies the tactic to all goals in focus **in parallel**. The tactic provided must solve all goals or do nothing, otherwise this tactic fails
- `n-m`: Applies the tactic to goals with indices between `n` and `m`, inclusive

### Syntax

```coq
all: simpl.

par: simpl; reflexivity; auto.

!: discriminate.

2-3: auto.
```

### Examples

Before
```coq
-------------------------
1/2
True
-------------------------
2/2
True
```

```coq
all: exact I.
(* or *)
1-2: exact I.
```

After
```coq
Proof finished
```

Alternatively,

```coq
!: exact I.
```

```After
Error: Expected a single focused goal but 2 goals are focused.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/V8.18.0/refman/proof-engine/ltac.html#goal-selectors)

<hr>

---
title: repeat - CTPE
---

## [repeat](/ctpe/Tacticals/repeat.html)
The `repeat` tactical repeatedly executes a tactic until it either fails or causes no change in the goal.
If the tactic provided succeeds, it will be recursively applied to each generated subgoal.

### Syntax

```coq
(* Simple usage *)
repeat split.
```

### Examples

Before
```coq
P, Q, R, S: Prop
-------------------------
1/1
P /\ Q /\ R /\ S
```

```coq
repeat split.
```

After
```coq
P, Q, R, S: Prop
-------------------------
1/4
P
-------------------------
2/4
Q
-------------------------
3/4
R
-------------------------
4/4
S
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.repeat)

<hr>

---
title: || - CTPE
---

## [||](/ctpe/Tacticals/or.html)
The infix `||` tactical tries the first tactic and only tries the second if the first failed.
In other words, `||` executes the first tactic that makes progress on the goal.

### Syntax

```coq
(* Simple usage *)
reflexivity || assumption.
```

### Examples

Before
```coq
P: Prop
H: P
-------------------------
1/1
P
```

```coq
reflexivity || assumption.
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#first-tactic-to-make-progress)

<hr>

<!-- #include do.md -->

<hr>

<hr>
