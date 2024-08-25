---
title: "Goal Selectors - CTPE"
---

## Goal Selectors

Goal selectors are a category of tacticals that apply a tactic to a specific goal or goals.

There are a number of goal selectors:

- `all`: Applies the tactic to all goals in focus **in series**
- `!`: If only one goal is in focus, apply the tactic. If not, this tactic fails
- `par`: Applies the tactic to all goals in focus **in parallel**. The tactic provided must solve all goals or do nothing, otherwise this tactic fails
- `n-m`: Applies the tactic to goals with indices between `n` and `m`, inclusive

### Syntax

```coq
all: simpl.

par: simpl; reflexivity; auto.

!: discriminate.

2-3: auto.
```

### Examples

Before
```coq
-------------------------
1/2
True
-------------------------
2/2
True
```

```coq
all: exact I.
(* or *)
1-2: exact I.
```

After
```coq
Proof finished
```

Alternatively,

```coq
!: exact I.
```

```After
Error: Expected a single focused goal but 2 goals are focused.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/V8.18.0/refman/proof-engine/ltac.html#goal-selectors)
