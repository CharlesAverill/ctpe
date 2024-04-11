---
title: unfold - CTPE
---

## unfold

`unfold` replaces definition identifiers with the definition's contents, simplifying along the way.

### Syntax

```coq
(* Simple example *)
unfold plus.

(* Unfolding a definition in a hypothesis *)
unfold X in H.

(* Unfolding a definition in all hypotheses and the goal *)
unfold X in *.
```

### Examples

Given
```coq
Fixpoint bitlist (n : nat) : list bool :=
    match n with
    | O =>    true  :: nil
    | S n' => false :: (bitlist n')
    end.
```

Before
```coq
n: nat
l: list bool
H: bitlist (S (S n)) = false :: false :: l
-------------------------
1/1
bitlist (S n) = false :: l
```

```coq
unfold bitlist in *.
```

After
```coq
n: nat
l: list bool
H: false
     :: false
        :: (fix bitlist (n : nat) : list bool :=
              match n with
              | 0 => true :: nil
              | S n' => false :: bitlist n'
              end) n =
    false :: false :: l
-------------------------
1/1
false
 :: (fix bitlist (n0 : nat) : list bool :=
       match n0 with
       | 0 => true :: nil
       | S n' => false :: bitlist n'
       end) n = false :: l
```

### Resources

TODO : Below link should be updated with the `master` version once it makes its way into the tree

[Reference Documentation](https://coq.inria.fr/doc/V8.11.0/refman/proof-engine/tactics.html#coq:tacn.unfold)
