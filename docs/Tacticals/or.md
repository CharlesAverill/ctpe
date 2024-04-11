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
