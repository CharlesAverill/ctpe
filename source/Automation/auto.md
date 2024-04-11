---
title: auto - CTPE
---

## auto

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

(* Use a specific database *)
auto with bool.

(* Use a specific lemma *)
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

Lemma x : (forall n, n * 1 = n) /\ (true = true). auto with automation. Qed.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.auto)

[Hint Databases](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#hintdatabases)
