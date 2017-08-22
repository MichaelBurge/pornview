Require Import PV.Types.
Require Import PV.Nat.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Lemma remove_not_in :
  forall (a : Type) (xs : list a) (x : a),
  forall (dec : DecidableEq a),
    ~In x xs -> xs = remove dec x xs.
Proof.
  intros.
  induction xs.
  compute. auto.
  unfold remove.
  case (dec x a0).

  intro.
  rewrite e in H.
  destruct H.
  apply in_eq.

  intro.
  assert (~ In x xs).
  intro.
  destruct H.
  apply in_cons.
  apply H0.

  specialize (IHxs H0).
  rewrite IHxs in |- * at 1.
  unfold remove.
  auto.
Qed.

Lemma list_succ_len_eq :
  forall (a : Type) (xs : list a) (x : a),
    Datatypes.length (x :: xs) = S (Datatypes.length xs).
Proof.
  intros.
  apply Add_length with (a := x).
  apply Add_head.
Qed.

Lemma remove_head_2 :
  forall (a : Type) (xs : list a) (x1 x2 : a),
  forall (dec : DecidableEq a),
    x1 <> x2 -> remove dec x1 (x2::xs) = x2 :: (remove dec x1 xs).
Proof.
  intros.
  unfold remove.
  case (dec x1 x2).
  intro.
  contradiction.
  intro.
  auto.
Qed.

Lemma remove_head_4 :
  forall (a : Type) (xs : list a) (x1 x2 : a),
  forall (dec : DecidableEq a),
    x1 = x2 -> remove dec x1 (x2::xs) = remove dec x1 xs.
Proof.
  intros.
  rewrite H.
  unfold remove.
  case (dec x2 x2).
  intro.
  tauto.
  intro.
  rewrite H in H.
  contradiction.
Qed.

Lemma remove_head_1 :
  forall (a : Type) (xs : list a) (x : a),
  forall (dec : DecidableEq a),
    ~ In x xs -> xs = remove dec x (x::xs).
Proof.
  intro. intro.
  unfold remove.
  intros.
  case (dec x x).
  intro.
  rewrite <- remove_not_in with (x := x) (dec := dec).
  tauto.
  apply H.
  
  intro.
  contradiction.
Qed.

Lemma remove_in_1 :
  forall (a : Type) (xs : list a) (x : a) (y : a),
  forall (dec : DecidableEq a),
    In x (remove dec y xs) -> In x xs.
Proof.
  intros.
  induction xs.
  compute in H. contradiction.
  case (dec x a0).
  intro.
  rewrite e.
  apply in_eq.

  intro.
  apply in_cons.
  case (dec y a0).
  intro.
  rewrite e in H.
  apply in_cons with (a := a0) in H.
  apply in_inv in H.
  destruct H.
  symmetry in H.
  contradiction.

  rewrite remove_head_4 in H.
  rewrite e in IHxs.
  apply IHxs in H.
  apply H.
  tauto.

  intro.
  rewrite remove_head_2 in H.
  apply in_inv in H.
  destruct H.
  symmetry in H.
  contradiction.

  apply IHxs in H.
  apply H.
  apply n0.
Qed.

Lemma remove_head_3 :
  forall (a : Type) (xs : list a) (x y: a),
  forall (dec : DecidableEq a),
    In x (remove dec y xs) <-> (x <> y /\ In x xs).
Proof.
  intros.
  (* -> *)
  split.
  intro.
  split.
  intro.
  rewrite H0 in H. apply remove_In in H. apply H.

  intros.
  apply remove_in_1 in H.
  apply H.

  (* <- *)
  intros.
  destruct H.
  induction xs.
  compute in H0. contradiction.

  case (dec y a0).
  intro.
  rewrite <- e in H0.
  apply in_inv in H0.
  destruct H0.
  symmetry in H0. contradiction.
  apply IHxs in H0.
  rewrite <- e.
  rewrite remove_head_4.
  apply H0.
  auto.

  intros.
  rewrite remove_head_2.
  case (dec x a0).
  intro. rewrite e.
  apply in_eq.

  intro.
  apply in_cons.
  apply in_inv in H0.
  destruct H0.
  symmetry in H0. contradiction.
  apply IHxs in H0.
  apply H0.
  apply n.
Qed.

Lemma list_remove_add :
  forall (a : Type) (xs : list a) (x : a),
  forall (dec : DecidableEq a),
    NoDup xs -> In x xs ->
    Add x (remove dec x xs) xs.
Proof.
  intros.
  induction xs.
  apply in_nil in H0.
  contradiction.
  pose dec.
  specialize (d x a0).
  destruct d.
  rewrite <- e.
  rewrite <- remove_head_1 with (x := x) (dec := dec).
  apply Add_head.
  assert (~ In x xs /\ NoDup xs).
  rewrite <- NoDup_cons_iff.
  rewrite <- e in H.
  apply H.
  destruct H1.
  apply H1.

  specialize (in_inv H0).
  intros.
  destruct H1.
  symmetry in H1. contradiction.
  assert (NoDup xs). apply NoDup_cons_iff in H. destruct H.
  apply H2.
  specialize (IHxs H2 H1).
  rewrite remove_head_2.
  apply Add_cons.
  apply IHxs.
  apply n.
Qed.

Lemma list_remove_nodup_len_1 :
  forall (a : Type) (xs : list a) (x : a),
  forall (dec : DecidableEq a),
    NoDup xs -> In x xs ->
    Datatypes.length xs = S (Datatypes.length (remove dec x xs)).
Proof.
  intros.
  induction xs.
  (* Empty list *)
  apply in_nil in H0. contradiction.
  (* Induction case *)
  apply Add_length with (a := x).
  apply list_remove_add.
  apply H.
  apply H0.
Qed.

Lemma remove_not_in_1 :
  forall (a : Type) (xs : list a) (x : a) (y : a),
  forall (dec : DecidableEq a),
    ~ In x (remove dec y xs) -> (x = y \/ ~ In x xs).
Proof.
  intros.
  pose (dec x y).
  destruct s.
  left.
  tauto.

  right.
  intro.
  destruct H.
  
  induction xs.
  compute. tauto.

  simpl.
  case (dec y a0).
  intro.
  assert (In x xs).
  apply in_inv in H0.
  destruct H0.
  rewrite e in n.
  rewrite H in n.
  contradiction.

  apply H.
  specialize (IHxs H).
  apply IHxs.

  intro.
  case (dec x a0).
  intro.
  rewrite e.
  apply in_eq.

  intro.
  apply in_inv in H0.
  destruct H0.
  symmetry in H.
  contradiction.

  specialize (IHxs H).
  apply in_cons.
  apply IHxs.
Qed.
  
Lemma list_remove_nodup_len_2 :
  forall (a : Type) (xs : list a) (ys : list a) (x : a),
  forall (dec : DecidableEq a),
    Datatypes.length xs = Datatypes.length ys ->
    NoDup xs -> NoDup ys -> In x ys ->
    Datatypes.length xs = S (Datatypes.length (remove dec x ys)).
Proof.
  intros.
  rewrite <- list_remove_nodup_len_1. apply H. apply H1.
  apply H2.
Qed.

Lemma remove_not_in_3 :
  forall (a : Type) (xs : list a) (x y : a),
  forall (dec : DecidableEq a),
    In x (remove dec y xs) -> x <> y.
Proof.
  intros.
  case (dec x y).
  intro.
  rewrite e in H.
  apply remove_In in H.
  contradiction.
  
  intro.
  apply n.
Qed.


Lemma remove_not_in_2 :
  forall (a : Type) (xs : list a) (x : a) (y : a),
  forall (dec : DecidableEq a),
    In x (remove dec y xs) <-> (x <> y /\ In x xs).
Proof.
  intros.
  (* -> *)
  split.
  intro.
  induction xs.
  compute in H. contradiction.
  pose (in_dec dec x (a0 :: xs)).
  destruct s.
  pose (dec x y).
  destruct s.

  rewrite e in H.
  apply remove_In in H. contradiction.
  auto.

  apply remove_not_in with (dec := dec) in n.
  rewrite <- remove_not_in in H.
  rewrite n in H.
  apply remove_In in H. contradiction.

  rewrite remove_head_3 in H.
  destruct H.
  rewrite n in H0.
  
  apply remove_In in H0. contradiction.

  (* <- *)
  intros.
  destruct H.
  apply remove_head_3.
  auto.
Qed.
  


Lemma list_remove_preserves_nodup :
  forall (a : Type) (xs : list a) (x : a),
  forall (dec : DecidableEq a),
    NoDup xs -> NoDup (remove dec x xs).
Proof.
  intros.
  induction H.
  compute. apply NoDup_nil.
  case (dec x x0).
  Focus 2.
  intro.
  rewrite remove_head_2.
  apply NoDup_cons.

  intro.
  rewrite remove_head_3 in H1.
  destruct H1.
  contradiction.
  apply IHNoDup.
  apply n.

  intro.
  rewrite e.
  rewrite remove_head_4.
  rewrite e in IHNoDup.
  apply IHNoDup.
  tauto.
Qed.


Lemma list_length_remove :
  forall (elt : Type) (x : elt) (xs : list elt) (ys : list elt),
    forall (dec : DecidableEq elt),
      NoDup ys ->
      length (x :: xs) <> length ys -> ~ In x ys \/ length xs <> length (remove dec x ys).
Proof.
  admit.
Admitted.
  
Lemma list_diff_exists :
  forall (elt : Type) (xs : list elt) (ys : list elt),
    DecidableEq elt ->
    NoDup xs /\ NoDup ys ->
    Datatypes.length xs <> Datatypes.length ys ->
    exists (x : elt),
      (In x xs /\ ~ In x ys) \/
      (~In x xs /\ In x ys).
Proof.  
  (* Try #1 *)
  intro.
  intro.
  induction xs.
  intros.
  induction ys.
  (* Case 1: Two empty lists *)
  intros.
  contradiction.
  (* Case 2: An empty list and a nonempty list *)
  exists a.
  right.
  split.
  auto.
  apply in_eq.

  (* Case 3: Two nonempty lists (a::xs) and ys *)
  intros.
  destruct H.
  rewrite NoDup_cons_iff in H.
  destruct H.
  pose in_dec.
  specialize s with (A := elt) (a := a) (l := ys).
  assert (forall (a : elt) (l : list elt), {In a l} + {~ In a l}).
  apply s.
  apply X.
  
  specialize (X0 a ys).
  destruct X0.
  (* Case 3b: a is in both, so throw it out and apply induction hypothesis *)
  
  pose (Nat.eq_dec (Datatypes.length xs) (Datatypes.length ys)).
  destruct s0.
  pose (remove X a ys).
  pose (list_remove_nodup_len_2 elt xs ys a X e H2 H1).
  apply s_neq in e0.
  assert (NoDup xs /\ NoDup l). split.
  apply H2. apply list_remove_preserves_nodup. apply H1.
  specialize (IHxs l X H3 e0).
  destruct IHxs.
  exists x.
  destruct H4.
  destruct H4.

  left.
  split.
  
  apply in_cons. apply H4.
  pose (remove_not_in_1 elt ys x a X).
  specialize (o H5).
  destruct o.
  rewrite H6 in H4.
  contradiction.
  
  apply H6.
  destruct H4.
  right.
  split.
  pose (X a x).
  destruct s0.
  assert (~ In x l).
  unfold l.
  rewrite e1 in |- * at 1.
  apply remove_In.
  contradiction.
  apply not_in_cons.
  split.
  auto.
  apply H4.
  destruct H3.
  unfold l in H5.
  apply remove_in_1 with (dec := X) (y := a).
  apply H5.
  pose (remove X a ys).
  assert (NoDup l). apply list_remove_preserves_nodup. apply H1.
  assert (NoDup xs /\ NoDup l). auto.
  specialize (IHxs l X H4).
  pose (list_eq_dec X xs ys). apply i.
  
  (* Case: a is again in both, so exclude it *)
  rewrite list_succ_len_eq in H0.
  rewrite list_remove_nodup_len_1 with (xs := ys) (x := a) (dec := X) in H0.
  rewrite s_neq_2 in H0.
  assert (NoDup xs /\ NoDup (remove X a ys)). split.
  tauto. apply list_remove_preserves_nodup. apply H1.
  specialize (IHxs (remove X a ys) X H3 H0).
  destruct IHxs.
  exists x.
  destruct H4.
  destruct H4.
  left.
  split.
  apply in_cons. apply H4.
  assert (x = a \/ ~ In x ys).
  apply remove_not_in_1 with (dec := X).
  apply H5.
  destruct H6.
  rewrite H6 in H4. contradiction.
  apply H6.
  
  destruct H4.
  right.
  split.
  apply not_in_cons.
  split.
  pose remove_not_in_3.
  specialize (n0 elt ys x a X H5).
  apply n0.
  apply H4.
  pose remove_in_1.
  specialize (i0 elt ys x a X H5).
  apply i0.
  apply H1.
  apply i.

  (* Case *)
  exists a.
  left.
  split.
  apply in_eq.
  apply n.
Qed.
