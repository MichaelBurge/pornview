Require Import PV.Types.
Require Import PV.Lists.
Require Import PV.SetoidLists.
Require Import PV.Nat.

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

Section Map.

  Variable elt : Type.
  Variable eqA : elt -> elt -> Prop.
  Variable eqA_dec : DecidableEqA elt eqA.

(* Lemma decidable_eq_pair : *)
(*   DecidableEq (M.key * elt). *)
(* Proof. *)
(*   intro. *)
(*   intro. *)
(*   destruct x. *)
(*   destruct y. *)
(*   specialize (dec e e0). *)
(*   destruct dec. *)
(*   specialize (M.E.eq_dec k k0). intro. *)
(*   destruct H. *)
(*   (* Equal *) *)
(*   left. *)
(*   rewrite e2. rewrite e1. auto. *)
(*   (* Key unequal *) *)
(*   right. *)
(*   intro. *)
(*   rewrite e1 in H. *)
(*   destruct n. *)
(*   assert (fst (k, e0) = fst (k0, e0)). *)
(*   rewrite H. auto. *)
(*   unfold fst in H0. *)
(*   apply H0. *)
(*   (* Element unequal *) *)
(*   right. *)
(*   intro. *)
(*   destruct n. *)
(*   assert (snd (k, e) = snd (k0, e0)). *)
(*   rewrite H. auto. *)
(*   unfold snd in H0. *)
(*  (*  apply H0. *) *)
(* Qed. *)

(* Lemma decidable_eqke_pair : *)
(*   DecidableEqA (M.key * elt) (@M.eq_key_elt elt). *)
(* Proof. *)
(*   admit. *)
(*   (* intro. *) *)
(*   (* intro. *) *)
(*   (* destruct x. destruct y. *) *)
(*   (* case (N.eq_dec k k0). *) *)
(*   (* case (dec e e0). *) *)
(*   (* intros. *) *)
(*   (* rewrite e1. rewrite e2. *) *)
(*   (* left. *) *)
(*   (* compute. *) *)
(*   (* auto. *) *)

(*   (* intros. *) *)
(*   (* right. *) *)
(*   (* compute. *) *)
(*   (* intros. *) *)
(*   (* destruct H. *) *)
(*   (* contradiction. *) *)

(*   (* intros. *) *)
(*   (* right. *) *)
(*   (* compute. *) *)
(*   (* intro. *) *)
(*   (* destruct H. *) *)
(*   (* contradiction. *) *)
(* Admitted. *)

Lemma decidable_eqk_pair :
  DecidableEqA (M.key * elt) (@M.eq_key elt).
Proof.

  intro.
  intro.
  destruct x. destruct y.
  case (N.eq_dec k k0).
  intros.
  rewrite e1.
  left.
  compute.
  auto.

  intros.
  right.
  compute.
  intros.
  contradiction.
Qed.

Lemma InA_eqk_eq :
  forall (m : M.t elt) (idx : N) (e e' : elt),
    InA (@M.eq_key elt) (idx, e) (M.elements m) <->
    InA (@M.eq_key elt) (idx, e') (M.elements m).
Proof.
  intros.
  induction (M.elements m).
  split.
  compute.
  rewrite InA_nil. contradiction.
  rewrite InA_nil. contradiction.

  split.
  intro.
  rewrite InA_cons in H.
  destruct H.
  apply InA_cons_hd.
  compute in H.
  compute. tauto.
  rewrite InA_cons.
  apply IHl in H.
  right. apply H.

  intro.
  rewrite InA_cons in H.
  rewrite InA_cons.
  destruct H.
  compute in H.
  left.
  compute.
  tauto.

  right.
  apply IHl in H.
  tauto.
Qed.

Lemma cons_head :
  forall (a : Type) (xs1 xs2 : list a) (x1 x2 : a),
    (x1 :: xs1) = (x2 :: xs2) <-> x1 = x2.
Proof.
  admit.
Admitted.

Lemma eqb_findA_1 :
  forall (xs : list (prod N elt)) (k : N) (e : elt),
    findA (MP.F.eqb k) ((k, e) :: xs) <> None.
Proof.
  intros.
  unfold findA.
  unfold MP.F.eqb.
  case_eq (M.E.eq_dec k k).
  intros. discriminate.
  intros. contradiction.
Qed.

Lemma eqb_findA_2 :
  forall (xs : list (prod N elt)) (k1 k2 : N) (e : elt),
    MP.F.eqb k1 k2 = true \/
    findA (MP.F.eqb k1) ((k2, e) :: xs) = findA (MP.F.eqb k1) xs.
Proof.
  intros.
  unfold findA.
  case_eq (MP.F.eqb k1 k2).
  
  intros. left. tauto.
  intros.
  
  right. tauto.
Qed.
     
Lemma InA_eqk_implies_find :
  forall (m : M.t elt) (idx : N) (e : elt),
    InA (M.eq_key (elt:=elt)) (idx, e) (M.elements m) ->
    M.find idx m <> None.
Proof.
  intros.
  rewrite MP.F.elements_o.
  induction (M.elements m).
  compute in H.
  apply InA_nil in H.
  auto.

  apply InA_cons in H.
  destruct H.
  destruct a.
  unfold M.eq_key in H.
  unfold M.Raw.Proofs.PX.eqk in H.
  unfold fst in H.
  rewrite H.
  apply eqb_findA_1.
  
  apply IHl in H.
  intro.
  destruct H.
  destruct a.
  
  specialize (eqb_findA_2 l idx k e0).
  intro.
  destruct H.
  unfold findA in H0.
  rewrite H in H0.
  discriminate.
  rewrite <- H0.
  symmetry.
  apply H.
Qed.

Lemma In_map_iff_InA_elements_1 :
  forall (m : M.t elt) (idx : N) (e : elt),
    InA (@M.eq_key elt) (idx, e) (M.elements m) <-> M.In idx m.
Proof.
  intros.
  split.
  (* -> *)
  intros.

  apply MP.F.mem_in_iff.
  rewrite MP.F.mem_find_b.
  case_eq (M.find idx m).

  intros. auto.

  intros. apply InA_eqk_implies_find with (e := e) in H0. contradiction.
  apply H.
  
  (* <- *)
  intro.
  apply MP.F.elements_in_iff in H.
  destruct H.
  apply MP.InA_eqke_eqk with (k2 := idx) (e2 := e) in H.
  apply H.
  tauto.  
Qed.
  
Lemma NoDupA_eqk :
  forall (m : M.t elt),
    @NoDupA (M.key * elt) (@M.eq_key elt) (M.elements m).
Proof.
  apply M.elements_3w.
Qed.
  
Lemma cardinal_diff_exists :
  forall (m : M.t elt) (m' : M.t elt),
      M.cardinal m <> M.cardinal m' ->
      exists (idx : N),
        (M.In idx m /\ ~ M.In idx m') \/
        (~M.In idx m /\ M.In idx m').
Proof.
  intros.
  rewrite M.cardinal_1 in H.
  rewrite M.cardinal_1 in H.

  specialize (list_diff_exists_A (M.key * elt) (@M.eq_key elt) (@MP.eqk_equiv elt) (decidable_eqk_pair)).  
  intros.
  specialize (H0 (M.elements m) (M.elements m') (NoDupA_eqk m) (NoDupA_eqk m') H).
  destruct H0.
  destruct x.
  rewrite In_map_iff_InA_elements_1 in H0.
  rewrite In_map_iff_InA_elements_1 in H0.
  exists k.
  apply H0.
Qed.

Lemma cardinal_bijection :
  forall (m : M.t elt) (m' : M.t elt),
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
Qed.

Lemma monotone_In :
  forall (m : M.t elt) (x : N) (y : N) (e : elt),
    M.In x m -> M.In x (M.add y e m).
Proof.
  intros.
  apply MF.add_in_iff.
  right.
  apply H.
Qed.

Lemma Add_if_add :
  forall (m : M.t elt) (k : N) (e : elt),
    MP.Add k e m (M.add k e m).
Proof.
  intros.
  intro.
  tauto.
Qed.

  
Lemma cardinal_4 :
  forall (m : M.t elt) (k : N) (e : elt),
    (M.In k m /\ M.cardinal (M.add k e m) = M.cardinal m) \/
    (~ M.In k m /\ M.cardinal (M.add k e m) = S (M.cardinal m)).
Proof.
  intros.
  case (MF.In_dec m k).
  intro.
  left.
  split.
  apply i.
  apply cardinal_bijection.
  intro.
  split.
  intro.
  apply MP.F.add_in_iff in H.
  destruct H.
  rewrite H in i.
  apply i.
  apply H.

  intro.
  apply MP.F.add_in_iff.
  right.
  apply H.

  intro.
  right.
  split.
  apply n.
  apply MP.cardinal_2 with (e := e) (x := k).
  apply n.

  apply Add_if_add.
Qed.


Definition add_diff_cardinal (idx : N) (m : M.t elt) : nat :=
  match M.find idx m with
  | None => 1
  | Some  x => 0
  end.

(* Compare with cardinal_2 in Coq.FSets.FMapFacts *)
Lemma cardinal_3 :
  forall (m : M.t elt) (k : N) (e : elt),
    M.In k m -> M.cardinal (M.add k e m) = M.cardinal m.
Proof.
  intros.
  pose cardinal_4.
  specialize o with (m := m) (k := k) (e := e).
  destruct o.
  destruct H0.
  apply H1.
  destruct H0.
  contradiction.
Qed.


Lemma add_diff_cardinal_1 :
  forall (m : M.t elt) (idx : N),
    M.In idx m -> add_diff_cardinal idx m = 0.
Proof.
  intros.
  apply MP.F.in_find_iff in H.
  unfold add_diff_cardinal.
  case_eq (M.find idx m).
  intros. tauto.
  intros. contradiction.
Qed.

Lemma add_diff_cardinal_2 :
  forall (m : M.t elt) (k : N),
    ~ M.In k m -> add_diff_cardinal k m = 1.
Proof.
  intros.
  apply MP.F.not_find_in_iff in H.
  unfold add_diff_cardinal.
  rewrite H.
  tauto.
Qed.

Lemma add_inc_cardinal :
  forall (m : M.t elt) (k : N) (e : elt),
    M.cardinal (M.add k e m) = M.cardinal m + add_diff_cardinal k m.
Proof.
  intros.
  
  pose MF.In_dec.
  specialize s with elt m k.
  destruct s.
  (* Case 1: The index is already in the map *)
  assert (i2 := i).
  apply cardinal_3 with (e := e)in i.
  rewrite i.
  assert (M.cardinal m = M.cardinal m + 0). rewrite -> Nat.add_0_r. tauto.
  rewrite H in |- * at 1.
  apply l_sub. symmetry.
  apply add_diff_cardinal_1.
  apply i2.
  (* Case 2: The index is not in the map *)  
  rewrite MP.cardinal_2 with (x := k) (m := m) (e := e).
  rewrite succ_add.
  apply l_sub. symmetry.
  apply add_diff_cardinal_2.
  apply n.
  apply n.
  apply Add_if_add.
Qed.

Lemma Add_remove_1 :
  forall (m : M.t elt) (k : N) (e : elt),
    M.MapsTo k e m -> MP.Add k e (M.remove k m) m.
Proof.
  intros.

  intro.
  rewrite MP.F.elements_o.
  rewrite MP.F.add_o.
  rewrite MP.F.remove_o.
  rewrite MP.F.elements_o.
  case_eq (M.E.eq_dec k y).
  intros.

  SearchAbout M.MapsTo.
  apply M.find_1 in H.
  rewrite MP.F.elements_o in H.
  rewrite e0 in H.
  apply H.

  intros.
  tauto.
Qed.

Lemma cardinal_remove_1 :
  forall (m : M.t elt) (k : N),
    M.In k m -> S (M.cardinal (M.remove k m)) = M.cardinal m.
Proof.
  intros.
  symmetry.
  apply MP.F.elements_in_iff in H.
  destruct H.
  apply MP.cardinal_2 with (x := k) (e := x).
  intro.
  apply M.remove_1 in H0. contradiction.
  tauto.

  apply Add_remove_1.
  apply MP.F.elements_mapsto_iff.
  auto.
Qed.
  
End Map.