---
title: "rename - CTPE"
---

## rename

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
