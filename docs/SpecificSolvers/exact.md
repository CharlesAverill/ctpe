---
title: "exact - CTPE"
---

## [exact](/SpecificSolvers/exact.html)

`exact` allows users to solve goals by providing a proof object directly.
This tactic will fail if the provided proof object does not prove the goal.

### Syntax

```coq
(* Simple usage *)
exact I.
```

### Examples

Before
```coq
-------------------------
1/1
True
```

```coq
exact I.
```

After
```coq
Proof finished
```

Before
```coq
n: nat
-------------------------
1/1
n + 5 = n + 5
```

```coq
exact (eq_refl (n + 5)).
```

After
```coq
Proof finished
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/tactics.html?highlight=assumption#coq:tacn.exact)

<hr>
