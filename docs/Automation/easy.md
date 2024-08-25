---
title: easy - CTPE
---

## [easy](/Automation/easy.html)

`easy` throws many common "closing tactics" at a goal to solve a large category of simple problems.
`easy` will attempt to use:

- [`trivial`](/Automation/trivial.html)

- [`reflexivity`](/SpecificSolvers/reflexivity.html)

- [`symmetry`](/Rewriting/symmetry.html)

- [`contradiction`](/SpecificSolvers/contradiction.html)

- [`inversion`](/CaseAnalysis/inversion.html)

- [`intros`](/Generalization/intros.html)

- [`split`](/Simplification/split.html) (this begins a recursive call of `easy`)

- [`destruct`](/CaseAnalysis/destruct.html) (on hypotheses with conjunctions) 

### Syntax

```coq
easy.
```

### Examples

Before
```coq
P: Prop
H: P
-------------------------
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

<hr>
