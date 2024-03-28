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
