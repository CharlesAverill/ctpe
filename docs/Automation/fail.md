---
title: fail - CTPE
---

## [fail](/ctpe/Automation/fail.html)

`fail` always fails.

This is sometimes useful if you're building a complex tactic with try-catch behavior.

### Syntax

```coq
(* Simple usage *)
fail.
```

### Examples

Before
```coq
=========================
1/1
True
```

```coq
fail.
```

After
```coq
Error: Tactic failure.
```

### Resources

[Reference Documentation](https://coq.inria.fr/doc/master/refman/proof-engine/ltac.html#coq:tacn.fail)

<hr>
