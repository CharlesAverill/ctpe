---
title: inversion - CTPE
---

## inversion

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
