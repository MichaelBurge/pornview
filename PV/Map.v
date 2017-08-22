Require Import PV.Types.
Require Import PV.Lists.
Require Import PV.SetoidList.

From Coq Require Import
     Sets.Ensembles
     NArith.BinNat
     ZArith.Int
     FSets.FMapFacts
     FSets.FSetFacts
     FSets.FSetInterface
     FSets.FMapAVL
     FSets.FSetAVL
     Structures.OrdersEx
     Structures.OrdersAlt
     Lists.List
     Strings.String
     Bool.Bool
     Numbers.Natural.Abstract.NProperties
     PArith.BinPos
     Structures.Equalities
     Arith.PeanoNat.

Module N_as_OT := Backport_OT N_as_OT.
Module M := FMapAVL.Make(N_as_OT).
Module MF := Coq.FSets.FMapFacts.Facts M.
Module MP := Coq.FSets.FMapFacts.Properties M.
Module S := FSetAVL.Make(N_as_OT).
Module SF := Coq.FSets.FSetFacts.Facts S.

Lemma decidable_eq_pair :
  forall (elt : Type) (dec : DecidableEq elt),
    DecidableEq (M.key * elt).
Proof.
  intros.
  intro.
  intro.
  destruct x.
  destruct y.
  specialize (dec e e0).
  destruct dec.
  specialize (M.E.eq_dec k k0). intro.
  destruct H.
  (* Equal *)
  left.
  rewrite e2. rewrite e1. auto.
  (* Key unequal *)
  right.
  intro.
  rewrite e1 in H.
  destruct n.
  assert (fst (k, e0) = fst (k0, e0)).
  rewrite H. auto.
  unfold fst in H0.
  apply H0.
  (* Element unequal *)
  right.
  intro.
  destruct n.
  assert (snd (k, e) = snd (k0, e0)).
  rewrite H. auto.
  unfold snd in H0.
  apply H0.
Qed.

Lemma in_map_iff_in_elements :
  forall (elt : Type) (m : M.t elt) (idx : N) (e : elt),
    (InA (@M.eq_key_elt elt) (idx, e) (M.elements m) <-> M.In idx m).
Proof.
  admit.
(*   admit. *)
(*   intros. *)
(*   split. *)
(*   (* -> *) *)
(*   intro. *)
(*   apply MP.F.elements_in_iff. *)
(*   exists e. *)
(*   apply In_InA. *)
(*   apply MP.eqke_equiv. *)
(*   apply H. *)

(*   (* <- *) *)
(*   intro. *)
(*   apply MP.F.elements_in_iff in H. *)
(*   destruct H.admit. *)
(* Admitted. *)
Admitted.
  
Lemma nodup_elements :
  forall (elt : Type) (m : M.t elt),
    NoDup (M.elements m).
Proof.
  admit.
Admitted.

Lemma cardinal_diff_exists :
  forall (elt : Type) (m : M.t elt) (m' : M.t elt),
    forall (dec : DecidableEq elt),
      M.cardinal m <> M.cardinal m' ->
      exists (idx : N),
        (M.In idx m /\ ~ M.In idx m') \/
        (~M.In idx m /\ M.In idx m').
Proof.
  intros.
  rewrite M.cardinal_1 in H.
  rewrite M.cardinal_1 in H.
  apply list_diff_exists_A with (eqA := @M.eq_key_elt elt) in H.
  destruct H.
  destruct H.
  
  destruct H.
  destruct x.
  exists k.
  left.
  split.
  apply MF.elements_in_iff.
  exists e.
  
  apply in_map_iff_in_elements.
  apply MP.F.elements_in_iff.
  exists e. apply H.
  intro.
  destruct H0.
  pose in_map_iff_in_elements.
  specialize (i elt m' k e).
  destruct i.
  apply H2.
  apply H1.
  destruct x.
  exists k.
  destruct H.
  rewrite in_map_iff_in_elements in H0, H.
  right.
  auto.
  split.
  apply nodup_elements.
  apply nodup_elements.
Qed.

Lemma cardinal_bijection :
  forall (elt : Type) (m : M.t elt) (m' : M.t elt),
    DecidableEq elt ->
    (forall (idx : N),
        (M.In idx m <-> M.In idx m')) ->
    M.cardinal m = M.cardinal m'.
Proof.
  intros.
  pose Nat.eq_dec.
  specialize s with (n := M.cardinal m) (m := M.cardinal m').
  destruct s.
  apply e.
  apply cardinal_diff_exists in n.
  destruct n.
  destruct H0.
  destruct H0.
  specialize H with (idx := x).
  destruct H.
  apply H in H0.
  contradiction.
  destruct H0.
  specialize H with (idx := x).
  apply H in H1.
  contradiction.
  apply X.
Qed.

Lemma monotone_In :
  forall (elt : Type) (m : M.t elt) (x : N) (y : N) (e : elt),
    M.In x m -> M.In x (M.add y e m).
Proof.
  intros.
  apply MF.add_in_iff.
  right.
  apply H.
Qed.
