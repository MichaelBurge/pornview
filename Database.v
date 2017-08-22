Require Import Ascii.
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

(* Our custom modules *)
Load Nat.
Require Import Lists.

Record Image : Set :=
  mkImage
    {
      filename : string;
      timestamp : N
    }.

Definition ImageId := N.
Definition CategoryId := N.
Definition Index := S.t.

Record ImageDb : Type :=
  mkDb
    {
      images : M.t Image;
      indices : M.t Index;
      next_id : ImageId
    }.

(* Main datatype operations *)
Definition newDb := {|
  images := M.empty Image;
  indices := M.empty Index;
  next_id := N.zero
                   |}.
Definition create_image (db : ImageDb) (img : Image) :=
  {|
    images := M.add (next_id db) img (images db);
    indices := indices db;
    next_id := N.succ (next_id db)
  |}.

Fixpoint find_category_ids (db : ImageDb) (cat : CategoryId) : Index :=
  match M.find cat (indices db) with
  | None => S.empty
  | Some xs => xs
  end.

Compute find_category_ids newDb N.zero.

Fixpoint set_from_list (xs : list N) : Index := fold_right S.add S.empty xs.
Fixpoint list_from_set (xs : Index) : list N := S.fold cons xs nil.

Print option.

Fixpoint find_categories_ids (db : ImageDb) (categories : list CategoryId) : Index :=
  match categories with
  | nil => set_from_list (map fst (M.elements (images db)))
  | cons cat cats => S.inter (find_category_ids db cat) (find_categories_ids db cats)
  end.

Fixpoint find_imgs (db : ImageDb) (imgs : list ImageId) :=
  match imgs with
  | nil => nil
  | cons i is =>
    match M.find i (images db) with
    | None => find_imgs db is
    | Some img => cons img (find_imgs db is)
    end
  end.  

Fixpoint find_categories (db : ImageDb) (categories : list CategoryId) : list Image :=
  find_imgs db (list_from_set (find_categories_ids db categories)).

Fixpoint delete_image (db : ImageDb) (img : ImageId) : ImageDb :=
  {|
    images  := M.remove img (images db);
    indices := M.map (S.remove img) (indices db);
    next_id := next_id db
  |}.

Print M.add.

Fixpoint tag_image (db: ImageDb) (img : ImageId) (cat : CategoryId) : ImageDb :=
  let idxs :=
      match M.find cat (indices db) with
      | None => M.add cat (S.singleton img) (indices db)
      | Some idx => M.add cat (S.add img idx) (indices db)
      end
  in {|
    images  := images db;
    indices := idxs;
    next_id := next_id db
  |}.

Fixpoint untag_image (db : ImageDb) (img : ImageId) (cat : CategoryId) : ImageDb :=
  let idxs :=
      match M.find cat (indices db) with
      | None => indices db
      | Some idx => M.add cat (S.remove img idx) (indices db)
      end
  in {|
    images  := images db;
    indices := idxs;
    next_id := next_id db
  |}.
      

(* Useful helper functions *)
Definition num_images (db : ImageDb) := M.cardinal (images db).
Definition mem_image (db : ImageDb) (img : ImageId) := M.mem img (images db).

(* Invariants *)
Theorem count_empty_db : num_images newDb = 0.
Proof.
  compute.
  tauto.
Qed.

Extraction Language Haskell.
Extraction count_empty_db.

Definition InternallyConsistent (db : ImageDb) :=
  forall (some_id : ImageId),
    M.In some_id (images db) -> N.lt some_id (next_id db).

Lemma lt_zero : forall (n : N), N.lt n N.zero -> False.
Proof.
  induction n.
  compute. intro. discriminate.
  compute. intro. discriminate.
Qed.  
  
  
Theorem preserves_consistency_1 : (InternallyConsistent newDb).
Proof.
  intro.
  intro.
  rewrite MF.empty_in_iff in H.
  contradiction.
Qed.

Theorem preserves_consistency_2 :
  forall (db : ImageDb) (img : Image),
    InternallyConsistent db -> InternallyConsistent (create_image db img).
Proof.
  intros.
  intro.
  intro.
  simpl.
  apply N.lt_succ_r.
  simpl in H0.
  apply MF.add_in_iff in H0.
  destruct H0.
  apply N.le_lteq.
  right.
  symmetry. apply H0.
  apply H in H0.
  apply N.le_lteq.
  left.
  apply H0.
Qed.

Axiom preserves_consistency_3 :
  forall (db : ImageDb) (img : ImageId),
    InternallyConsistent db -> InternallyConsistent (delete_image db img).

Axiom preserves_consistency_4 :
  forall (db : ImageDb) (img : ImageId) (cat : CategoryId),
    InternallyConsistent db -> InternallyConsistent (tag_image db img cat).

Axiom preserves_consistency_5 :
  forall (db : ImageDb) (img : ImageId) (cat : CategoryId),
    InternallyConsistent db -> InternallyConsistent (untag_image db img cat).

Lemma next_id_nin :
  forall (db : ImageDb),
    InternallyConsistent db -> ~ (M.In (next_id db) (images db)).
Proof.
  intros.
  intro.
  apply H in H0.
  apply N.ltb_nlt in H0.
  apply H0.
  apply N.ltb_irrefl.
Qed.

Definition add_diff_cardinal (a : Type) (idx : N) (m : M.t a) : nat :=
  match M.find idx m with
  | None => 1
  | Some  x => 0
  end.

Lemma not_in_map_if_not_in_elements :
  forall (elt : Type) (idx : N) (m : M.t elt) (e : elt),
    ~ In (idx, e) (M.elements m) -> ~ M.In idx m.
Proof.
  admit.
Admitted.

Lemma prod_fst_snd :
  forall (a b : Type) (p : a*b) (k : a) (e : b),
    k = fst p /\ e = snd p ->
    (k,e) = p.
Proof.
  admit.
Admitted.
  
Lemma cardinal_4 :
  forall (elt : Type) (m : M.t elt) (x : ImageId) (e : elt),
    (M.In x m /\ M.cardinal (M.add x e m) = M.cardinal m) \/
    (~ M.In x m /\ M.cardinal (M.add x e m) = S (M.cardinal m)).
Proof.
  admit.
Admitted.

(* Compare with cardinal_2 in Coq.FSets.FMapFacts *)
Lemma cardinal_3 :
  forall (elt : Type) (m : M.t elt) (x : ImageId) (e : elt),
    M.In x m -> M.cardinal (M.add x e m) = M.cardinal m.
Proof.
  intros.
  pose cardinal_4.
  specialize o with (elt := elt) (m := m) (x := x) (e := e).
  destruct o.
  destruct H0.
  apply H1.
  destruct H0.
  contradiction.
Qed.  


Lemma add_diff_cardinal_1 :
  forall (a : Type) (m : M.t a) (idx : ImageId),
    M.In idx m -> add_diff_cardinal a idx m = 0.
Proof.
  admit.
Admitted.

Lemma add_diff_cardinal_2 :
  forall (a : Type) (m : M.t a) (idx : ImageId),
    ~ M.In idx m -> add_diff_cardinal a idx m = 1.
Proof.
  admit.
Admitted.
  
Lemma l_sub :
  forall (p : nat) (q : nat) (r : nat),
    p + q = p + r <-> q = r.
Proof.
  admit.
Admitted.

Lemma succ_add :
  forall (p : nat),
    S p = p + 1.
Proof.
  intro.
  induction p.
  compute. tauto.
  rewrite IHp in |- * at 1.
  apply Nat.add_succ_l.
Qed.
  
Lemma add_preserves_Add :
  forall (a : Type) (m : M.t a) (idx : N) (x : a),
    MP.Add idx x m (M.add idx x m).
Proof.
  admit.
Admitted.

Lemma add_inc_cardinal :
  forall (a : Type) (m : M.t a) (idx : N) (x : a),
    M.cardinal (M.add idx x m) = M.cardinal m + add_diff_cardinal a idx m.
Proof.
  intros.
  
  pose MF.In_dec.
  specialize s with a m idx.
  destruct s.
  (* Case 1: The index is already in the map *)
  assert (i2 := i).
  apply cardinal_3 with (e := x)in i.
  rewrite i.
  assert (M.cardinal m = M.cardinal m + 0). rewrite -> Nat.add_0_r. tauto.
  rewrite H in |- * at 1.
  apply l_sub. symmetry.
  apply add_diff_cardinal_1.
  apply i2.
  (* Case 2: The index is not in the map *)  
  rewrite MP.cardinal_2 with (x := idx) (m := m) (e := x).
  rewrite succ_add.
  apply l_sub. symmetry.
  apply add_diff_cardinal_2.
  apply n.
  apply n.
  apply add_preserves_Add.
Qed.

Lemma consistent_adds_cardinal :
  forall (db : ImageDb),
    InternallyConsistent db -> add_diff_cardinal Image (next_id db) (images db) = 1.
Proof.
  intros.
  unfold add_diff_cardinal.
  assert (M.find (next_id db) (images db) = None).
  apply MF.not_find_in_iff.
  apply next_id_nin.
  apply H.
  rewrite H0. tauto.
Qed.
  
Theorem size_increases :
  forall (db : ImageDb) (img : Image),
    InternallyConsistent db -> (num_images (create_image db img) = num_images db + 1).
Proof.
  intros.
  unfold create_image.
  unfold num_images.
  unfold images.
  rewrite add_inc_cardinal.
  rewrite l_sub.
  apply consistent_adds_cardinal.
  apply H.
Qed.
Axiom size_decreases : forall (db : ImageDb) (img : ImageId),
    (Is_true (mem_image db img) /\ N.succ (num_images (delete_image db img)) = num_images db) \/
    (~ Is_true (mem_image db img) /\ num_images (delete_image db img) = num_images db).
Axiom size_nochange : forall (db : ImageDb) (img : ImageId) (cat : CategoryId),
    num_images (tag_image db img cat) = num_images db /\
    num_images (untag_image db img cat) = num_images db.

Extraction Language Haskell.
Extraction create_image.
Extraction find_categories.
Extraction delete_image.
Extraction create_category.
Extraction tag_image.
Extraction untag_image.
Extraction delete_category.