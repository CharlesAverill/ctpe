Theorem destruct_example2 : forall (P Q R : Prop),
    ((P /\ Q) /\ R) -> P /\ (Q /\ R).
Proof.
    intros P Q R H.
    destruct H as [[PTrue QTrue] RTrue]. split.
    - apply PTrue.
    - split. 
        -- apply QTrue.
        -- apply RTrue.
Qed.
