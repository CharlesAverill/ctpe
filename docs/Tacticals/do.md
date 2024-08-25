---
title: do - CTPE
---

## [do](/ctpe/Tacticals/do.html)

The `do` tactical accepts a tactic `t` and a natural number `n`, applying `t` to the goal `n` times.
`do` fails if one of the applications of `t` fails before `n` applications have occurred.

In my opinion, `do` is a difficult tactic to justify. I find myself using it when using [`repeat`](/ctpe/Tacticals/repeat.html)
tends to be overzealous. For example, if I have 100 goals and 30 of them can be solved the same way,
I'm more likely to use `do 30 <tactic>` than `repeat <tactic>` to prevent the remaining 70 goals from
being altered.

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
