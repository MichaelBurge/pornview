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
  split.
  intro.
  congruence.
  intro.
  rewrite H.
  auto.
Qed.
