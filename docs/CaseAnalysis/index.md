---
title: Case Analysis - CTPE
---

# [Case Analysis](/ctpe/CaseAnalysis/index.html)
Summary

---
title: destruct - CTPE
---

## [destruct](/ctpe/CaseAnalysis/destruct.html)
`destruct` allows for case analysis on terms, including assumptions.
It can be used to split assumptions with conjunctions, as well as existential assumptions.
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

<hr>
