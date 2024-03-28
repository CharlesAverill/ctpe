Theorem destruct_example3 : 
    forall (P Q R : Prop),
    (P \/ Q) -> P \/ Q \/ R.
Proof.
    intros. destruct H as [PTrue | QTrue].
    - left. assumption.
    - right. left. assumption.
Qed. 
