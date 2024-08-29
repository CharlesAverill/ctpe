---
title: idtac - CTPE
---

## [idtac](/ctpe/Automation/idtac.html)

`idtac` leaves a goal completely unchanged. This tactic will never fail.

A term can be provided as an argument to print a message to the console.
String and integers are printed literally rather than via their type's pretty-printer.

`idtac` is sometimes useful when you have many goals selected and only want to operate on some of them.

### Syntax

```coq
(* Simple usage *)
idtac.

(* Print a message *)
idtac "Hello World!".
```

### Examples

Before
```coq
=========================
1/1
True
```

```coq
idtac.
```

After
```coq
=========================
1/1
True
```

Before
```coq
n: nat
=========================
1/1
n + 0 = n
```

```coq
(* Only apply reflexivity to the n = 0 case. Leave the n = S n' case unaffected *)
induction n; [reflexivity | idtac].
```

After
```coq
n : nat
IHn : n + 0 = n
=========================
1/1
S n + 0 = S n
```
### Resources

[Reference Documentation](https://coq.inria.fr/doc/v8.10/refman/proof-engine/ltac.html#coq:tacn.idtac)

<hr>
