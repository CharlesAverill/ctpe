---
title: "Glossary - CTPE"
---

# Specialize

To transform a theorem P into some theorem P' that applies to a similar but more specific set of inputs than P. 
For example, the commutativity of addition states that

```coq
forall (n m : nat), n + m = m + n.
```

This can be specialized into the following theorem, which says that addition is commutative if one of the arguments is 7:

```coq
forall (m : nat), 7 + m = m + 7.
```

Important property: if the original general theorem P is true, then a specialized form P' of that theorem is always true!

Synonyms: weaken
Antonyms: generalize, strengthen
