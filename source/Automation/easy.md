---
title: easy - CTPE
---

## easy

`easy` throws many common "closing tactics" at a goal to solve a large category of simple problems.
`easy` will attempt to use:

- [`trivial`](/ctpe/Automation/trivial.html)

- [`reflexivity`](/ctpe/SpecificSolvers/reflexivity.html)

- [`symmetry`](/ctpe/Rewriting/symmetry.html)

- [`contradiction`](/ctpe/SpecificSolvers/contradiction.html)

- [`inversion`](/ctpe/CaseAnalysis/inversion.html)

- [`intros`](/ctpe/Generalization/intros.html)

- [`split`](/ctpe/Simplification/split.html) (this begins a recursive call of `easy`)

- [`destruct`](/ctpe/CaseAnalysis/destruct.html) (on hypotheses with conjunctions) 

### Syntax

```coq
easy.
```

### Examples

Before
```coq
P: Prop
H: P
=========================
1/1
True /\ 42 = 14 * 3 /\ P
```

```coq
easy.
```

After
```coq
No more goals.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proofs/automatic-tactics/auto.html#coq:tacn.easy)
