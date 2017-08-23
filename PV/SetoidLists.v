Require Import PV.Types.
Require Import PV.Lists.
Require Import PV.Nat.

Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Arith.PeanoNat.

Section SetoidLists.

Variable a : Type.
Variable eqA : a -> a -> Prop.
Variable equiv : Equivalence eqA.
Variable dec : DecidableEqA a eqA.

Lemma NoDupA_head_1 :
  forall (xs : list a) (x : a),
    NoDupA eqA (x :: xs) -> NoDupA eqA xs.
Proof.
  intros.
  inversion H.
  apply H3.
Qed.
  
Lemma removeA_head_2 :
  forall (xs : list a) (x1 x2 : a),
    ~ eqA x1 x2 -> removeA dec x1 (x2::xs) = x2 :: (removeA dec x1 xs).
Proof.
  intros.
  unfold removeA.
  case (dec x1 x2).
  intro.
  contradiction.
  intro.
  auto.
Qed.

Lemma removeA_head_4 :
  forall (xs : list a) (x1 x2 : a),
    eqA x1 x2 -> removeA dec x1 (x2::xs) = removeA dec x1 xs.
Proof.
  intros.
  unfold removeA.
  case (dec x1 x2).
  intro.
  tauto.
  intro.
  contradiction.
Qed.

Lemma NoDupA_head_2 :
  forall (xs : list a) (x1 x2 : a),
    NoDupA eqA (x1 :: x2 :: xs) -> ~ eqA x1 x2.
Proof.
  intros.
  inversion H.
  intro.
  destruct H2.
  inversion H3.
  apply InA_cons_hd with (l := xs) in H4.
  apply H4.
Qed.

Lemma NoDupA_head_3 :
  forall (xs : list a) (x1 x2 : a),
    NoDupA eqA (x1 :: x2 :: xs) -> NoDupA eqA (x2 :: x1 :: xs).
Proof.
  intros.
  inversion H.
  inversion H3.

  specialize (NoDupA_head_2 xs x1 x2 H).
  intro.
  apply NoDupA_cons.
  intro.
  destruct H6.
  inversion H9.
  apply equiv in H10. contradiction.
  apply H10.

  apply NoDupA_cons.
  SearchAbout InA.
  rewrite InA_cons in H2.
  intro.
  destruct H2.
  right.
  apply H9.
  apply H7.
Qed.

Lemma removeA_head_5 :
  forall (xs : list a) (x1 x2 : a),
    NoDupA eqA (x2::xs) -> eqA x1 x2 ->
    removeA dec x1 (x2::xs) = xs.
Proof.
  intros.
  rewrite removeA_head_4.
  induction xs.
  compute. tauto.

  inversion H.
  assert (~ eqA x1 a0). apply NoDupA_head_2 with (xs := xs).
  apply NoDupA_cons.
  intro.
  destruct H3.
  apply InA_eqA with (x := x1). apply equiv. apply equiv. apply equiv in H0. apply H0.
  apply H5. apply H4.
  apply removeA_head_2 with (xs := xs) in H5.
  rewrite H5.
  assert (NoDupA eqA (x2 :: xs)). apply NoDupA_head_3 in H.
  inversion H.
  apply H9.
  specialize (IHxs H6).
  rewrite IHxs.
  tauto.
  auto.
Qed.

Lemma removeA_head_1 :
  forall (xs : list a) (x : a),
    ~ InA eqA x xs -> xs = removeA dec x (x::xs).
Proof.
  intros.
  induction xs.
  compute.
  case (dec x x).
  intro. auto.
  intro. destruct n.
  apply Equivalence.equiv_reflexive.
  apply equiv.

  
  assert (~ InA eqA x xs).
  intro. destruct H.
  apply InA_cons_tl with (y := a0) in H0. apply H0.
  specialize (IHxs H0).
  compute.
  unfold removeA in IHxs.
  case_eq (dec x x).
  intro.
  case (dec x a0).
  case (dec x x) in IHxs.
  intros.
  destruct H.
  apply InA_cons_hd. apply e1.

  contradiction.

  intros.
  rewrite IHxs in |- * at 1.
  case_eq (dec x x).
  intros.
  auto.  

  intros.
  contradiction.

  intros.
  destruct n.
  apply Equivalence.equiv_reflexive.
  apply equiv.
Qed.

Lemma removeA_in_1 :
  forall (xs : list a) (x : a) (y : a),
    InA eqA x (removeA dec y xs) -> InA eqA x xs.
Proof.
  intros.
  rewrite removeA_InA in H. destruct H.
  apply H.
  apply equiv.
Qed.

Lemma removeA_head_3 :
  forall (xs : list a) (x y: a),
    InA eqA x (removeA dec y xs) <-> (~ eqA x y /\ InA eqA x xs).
Proof.
  intros.
  (* -> *)
  split.
  intro.
  split.
  intro.
  rewrite H0 in H. apply removeA_InA in H. apply H.

  intros. apply Equivalence.equiv_reflexive.
  apply equiv. apply equiv.

  apply removeA_InA in H.
  destruct H.
  apply H.
  apply equiv.

  (* <- *)
  intros.
  destruct H.
  apply removeA_InA.
  apply equiv.
  split. apply H0.

  intro. destruct H.
  apply equiv. apply H1.
Qed.

Lemma list_remove_nodup_len_1 :
  forall (xs : list a) (x : a),
    NoDupA eqA xs -> InA eqA x xs ->
    Datatypes.length xs = S (Datatypes.length (removeA dec x xs)).
Proof.  
  intros.
  induction xs.
  (* Empty list *)
  apply InA_nil in H0. contradiction.
  (* Induction case *)
  rewrite list_succ_len_eq.
  rewrite s_neq_2.
  specialize (removeA_head_5 xs x a0 H).
  intros.  
  apply NoDupA_head_1 in H.

  apply InA_cons in H0.
  destruct H0.
  specialize (H1 H0).
  rewrite H1. auto.

  specialize (IHxs H H0).
  case (dec x a0).
  intro.
  specialize (H1 e). rewrite H1. auto.
  intro.
  rewrite removeA_head_2.
  rewrite list_succ_len_eq.
  apply IHxs.
  apply n.
Qed.

Lemma NoDupA_cons_2 :
  forall (x : a) (xs : list a),
    NoDupA eqA (x :: xs) -> ~InA eqA x xs.
Proof.
  intros.
  intro.
  inversion H0.
  inversion H.
  contradiction.

  inversion H.
  contradiction.
Qed.

Lemma list_length_removeA :
  forall (x : a) (xs : list a) (ys : list a),
    NoDupA eqA ys ->
    length (x :: xs) <> length ys -> ~ InA eqA x ys \/ length xs <> length (removeA dec x ys).
Proof.
  intro.
  intro.
  induction xs.
  intros.
  case (InA_dec (A := a) (eqA := eqA) dec x ys).
  intros.

  right.
  specialize (list_remove_nodup_len_1 ys x H i).
  intros.
  rewrite H1 in H0.
  
  rewrite list_succ_len_eq in H0.
  rewrite s_neq_2 in H0.
  apply H0.

  intros.
  left. apply n.
  
  (* Main Induction case *)
  intros.
  case (InA_dec (A := a) (eqA := eqA) dec x ys).
  intros.
  right.
  specialize (list_remove_nodup_len_1 ys x H i). intros.
  rewrite H1 in H0. rewrite list_succ_len_eq in H0.
  rewrite s_neq_2 in H0.
  apply H0.

  intros.
  left. apply n.
Qed.

Lemma list_diff_exists_A :
  forall (xs : list a) (ys : list a),
    NoDupA eqA xs -> NoDupA eqA ys ->
    Datatypes.length xs <> Datatypes.length ys ->
    exists (x : a),
      (InA eqA x xs /\ ~ InA eqA x ys) \/
      (~InA eqA x xs /\ InA eqA x ys).
Proof.
  intro.
  induction xs.
  induction ys.
  intros.
  compute in H0. contradiction.

  intros.
  exists a0.
  right.
  split.
  rewrite InA_nil. intro. contradiction.
  apply InA_cons. left. apply equiv.

  intros.
  assert (H' := H).
  rewrite <- app_nil_l with (A := a) in H at 1.
  apply NoDupA_split in H. compute in H.

  apply list_length_removeA in H1.
  destruct H1.
  exists a0.
  left. split.
  apply InA_cons_hd. apply equiv. apply H1.

  apply removeA_NoDupA with (x := a0) (eqA_dec := dec) in H0.
  specialize (IHxs (removeA dec a0 ys) H H0 H1).
  destruct IHxs.
  destruct H2.
  
  exists x.
  destruct H2.
  left.
  split.
  apply InA_cons_tl. apply H2.
  intro. destruct H3.
  apply removeA_InA.
  apply equiv. split.
  apply H4.
  intro.
  apply NoDupA_cons_2 in H'.
  apply equiv in H3.
  specialize (InA_eqA (l := xs) equiv H3). intros.
  specialize (H5 H2). contradiction.

  case (dec a0 x).
  intro.
  destruct H2.
  apply removeA_InA in H3.
  destruct H3.
  contradiction.
  apply equiv.

  intro.
  exists x.
  destruct H2.
  right.
  split.
  intro.
  apply InA_cons in H4.
  destruct H4.
  apply equiv in H4. contradiction.
  contradiction.
  
  apply removeA_InA in H3.
  destruct H3.
  auto. apply equiv. apply equiv. apply H0.
Qed.

End SetoidLists.