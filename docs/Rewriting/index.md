---
title: Rewriting - CTPE
---

# [Rewriting](/ctpe/Rewriting/index.html)
Summary

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