---
title: "trivial - CTPE"
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
