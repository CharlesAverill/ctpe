Theorem induction_example1 : forall (n : nat),
    n + 0 = n.
Proof.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

Require Import ZArith.
Open Scope Z.
Theorem induction_example2 : forall (x y : Z),
    x + y = y + x.
Proof.
    induction x using Z.peano_ind.
    - intros. simpl. rewrite Z.add_0_r. reflexivity.
    - intros. rewrite Z.add_succ_l. rewrite IHx.
      rewrite Z.add_comm. rewrite <- Z.add_succ_l.
      rewrite Z.add_comm. reflexivity.
    - intros. rewrite Z.add_pred_l. rewrite IHx.
      rewrite Z.add_comm. rewrite <- Z.add_pred_l.
      rewrite Z.add_comm. reflexivity.
Qed. 
