---
title: "repeat - CTPE"
---

## repeat

The `repeat` tactical repeatedly executes a tactic until it either fails or causes no change in the goal.
If the tactic provided succeeds, it will be recursively applied to each generated subgoal.

### Syntax

```coq
(* Simple usage *)
repeat split.
```

### Examples

Before
```coq
P, Q, R, S: Prop
-------------------------
1/1
P /\ Q /\ R /\ S
```

```coq
repeat split.
```

After
```coq
P, Q, R, S: Prop
-------------------------
1/4
P
-------------------------
2/4
Q
-------------------------
3/4
R
-------------------------
4/4
S
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.repeat)
