Theorem test : 
    forall n, n <= 1 -> n = 0 \/ n = 1.
Proof.
    intros. inversion H. 
    - right. reflexivity.
    - inversion H1. left. reflexivity.
Qed.
