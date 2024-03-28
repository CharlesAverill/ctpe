Inductive color : Type :=
| Red | Blue | Green | Cyan | Magenta | Yellow.

Inductive makes_white : color -> color -> color -> Prop :=
| RBG : makes_white Red Blue Green
| CMY : makes_white Cyan Magenta Yellow.

Theorem inversion_example2 : 
    forall (c1 c2 c3 : color),
    makes_white c1 c2 c3 ->
    (c1 = Red /\ c2 = Blue /\ c3 = Green) \/
    (c1 = Cyan /\ c2 = Magenta /\ c3 = Yellow).
Proof.
    intros c1 c2 c3 Hmw. inversion Hmw. 
    - left. repeat split.
    - right. repeat split.
Qed.
