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
