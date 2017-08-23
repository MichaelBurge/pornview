Lemma succ_neq :
  forall (n : nat),
    n <> S n.
Proof.
  intros.
  intro.
  induction n.
  discriminate.
  destruct IHn.
  congruence.
Qed.

Lemma s_neq :
  forall (n : nat) (m : nat),
    n = S m -> n <> m.
Proof.
  intros.
  intro.
  rewrite H0 in H.
  apply succ_neq in H.
  apply H.
Qed.

Lemma s_neq_2 :
  forall (n : nat) (m : nat),
    S n = S m <-> n = m.
Proof.
  intros.
  split. intro.
  inversion H. tauto.
  
  intro. rewrite H.
  tauto.
Qed.

Lemma l_sub :
  forall (p : nat) (q : nat) (r : nat),
    p + q = p + r <-> q = r.
Proof.
  intros.
  split.
  intro.
  induction p.
  compute in H. apply H.

  inversion H. apply IHp in H1. apply H1.

  intro.
  rewrite H.
  tauto.
Qed.

Lemma succ_add :
  forall (p : nat),
    S p = p + 1.
Proof.
  intro.

  case_eq (p). intros. compute. auto.
  intros. rewrite <- H.
  assert (p = p + 0).
  apply plus_n_O.
  rewrite H0.
  rewrite plus_n_Sm. rewrite <- H0.
  tauto.  
Qed.
