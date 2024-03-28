Theorem test : forall n, n + 5 = n + 5.
intros. exact (eq_refl (n + 5)).
