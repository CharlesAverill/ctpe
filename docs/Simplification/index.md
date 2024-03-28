# [Simplification](/ctpe/Simplification/index.html)
Summary

## [simpl](/ctpe/Simplification/simpl.html)
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
