---
title: symmetry - CTPE
---

## [symmetry](/ctpe/Rewriting/symmetry.html)

`symmetry` is used to swap the left and right sides of an equality.

`symmetry` can be used on either the goal or a list of hypotheses.

### Syntax

```coq
(* Usage on goal *)
symmetry.

(* Usage on hypotheses *)
symmetry in H.
symmetry in H1, H2.
```

### Examples

Before
```coq
=========================
1/1
5 = 2 + 3
```

```coq
symmetry.
```

After
```coq
=========================
1/1
2 + 3 = 5
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/equality.html#coq:tacn.symmetry)

<hr>
