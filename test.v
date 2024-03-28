Theorem remember_ex : forall (x y : nat),
    x + y = x -> y = 0.
Proof.
    intros. remember (x + y) as sum.
