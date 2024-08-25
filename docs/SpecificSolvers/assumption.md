---
title: "assumption - CTPE"
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
=========================
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
