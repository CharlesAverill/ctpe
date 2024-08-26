---
title: do - CTPE
---

## [do](/ctpe/Tacticals/do.html)

The `do` tactical accepts a tactic `t` and a natural number `n`, applying `t` to the goal `n` times.
`do` fails if one of the applications of `t` fails before `n` applications have occurred.

In my opinion, `do` is a difficult tactic to justify. I find myself using it when using [`repeat`](/ctpe/Tacticals/repeat.html)
tends to be overzealous. For example, if I have a goal with 100 subterms, and I'd like to apply a tactic `t`
only to 30 of the subterms (assuming `t` works on individual subterms and not the whole goal), I'm more
likely to use `do 30 t` than `repeat t` to prevent the remaining 70 subterms from being affected.

### Syntax

```coq
do 3 (split; [reflexivity | idtac]).
```

### Examples

Before
```coq
=========================
1/1
1 = 1 /\ 2 = 2 /\ 3 = 3 /\ 4 = 4
```

```coq
do 3 (split; [reflexivity | idtac]).
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.do)

<hr>
