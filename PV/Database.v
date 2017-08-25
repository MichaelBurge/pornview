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
     Strings.Ascii
     extraction.ExtrHaskellString
     extraction.ExtrHaskellNatInteger
     extraction.ExtrHaskellNatNum
     Arith.PeanoNat.

(* Our custom modules *)
Require Import Nat.
Require Import Lists.
Require Import Map.

Module Database.

Record Image : Set :=
  mkImage
    {
      id : N;
      filename : string;
      timestamp : N
    }.

Definition ImageId := N.
Definition CategoryId := N.
Definition Index := S.t.

Record ImageDb : Type :=
  mkImageDb
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
  let newImg := {|
        id := next_id db;
        filename := filename img;
        timestamp := timestamp img
      |}
  in {|
    images := M.add (next_id db) newImg (images db);
    indices := indices db;
    next_id := N.succ (next_id db)
  |}.

Fixpoint find_category_ids (db : ImageDb) (cat : CategoryId) : Index :=
  match M.find cat (indices db) with
  | None => S.empty
  | Some xs => xs
  end.

(* Compute find_category_ids newDb N.zero. *)

Fixpoint set_from_list (xs : list N) : Index := fold_right S.add S.empty xs.
Fixpoint list_from_set (xs : Index) : list N := S.fold cons xs nil.

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

Fixpoint find_img (db : ImageDb) (img : ImageId) : option Image := M.find img (images db).

Fixpoint find_categories (db : ImageDb) (categories : list CategoryId) : list Image :=
  find_imgs db (list_from_set (find_categories_ids db categories)).

Fixpoint delete_image (db : ImageDb) (img : ImageId) : ImageDb :=
  {|
    images  := M.remove img (images db);
    indices := M.map (S.remove img) (indices db);
    next_id := next_id db
  |}.

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

Theorem preserves_consistency_3 :
  forall (db : ImageDb) (img : ImageId),
    InternallyConsistent db -> InternallyConsistent (delete_image db img).
Proof.
  intros.
  intro.
  intro.
  destruct db.
  unfold delete_image in H0.
  unfold next_id in H0.
  unfold images in H0.

  unfold delete_image.
  unfold next_id.
  unfold InternallyConsistent in H.
  apply MP.F.remove_in_iff in H0.
  destruct H0.
  specialize (H some_id H1).
  unfold next_id in H.
  apply H.
Qed.
  
Theorem preserves_consistency_4 :
  forall (db : ImageDb) (img : ImageId) (cat : CategoryId),
    InternallyConsistent db -> InternallyConsistent (tag_image db img cat).
Proof.
  intros.
  destruct db.
  intro.
  intro.
  unfold tag_image.
  unfold next_id.

  unfold InternallyConsistent in H.
  specialize (H some_id H0).
  unfold next_id in H.
  apply H.
Qed.
  
Theorem preserves_consistency_5 :
  forall (db : ImageDb) (img : ImageId) (cat : CategoryId),
    InternallyConsistent db -> InternallyConsistent (untag_image db img cat).
Proof.
  intros.
  destruct db.
  intro. intro.
  unfold untag_image.
  unfold next_id.
  unfold untag_image in H0.
  unfold next_id in H0.
  unfold InternallyConsistent in H.
  specialize (H some_id H0).
  unfold next_id in H.
  apply H.
Qed.
  
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

Lemma num_images_1 :
  forall (db : ImageDb) (img : ImageId),
    num_images (delete_image db img) = M.cardinal (M.remove img (images db)).
Proof.
  intros.
  destruct db.
  unfold delete_image.
  unfold num_images.
  
  unfold images.
  tauto.
Qed.

Theorem size_decreases : forall (db : ImageDb) (img : ImageId),
    (Is_true (mem_image db img) /\ S (num_images (delete_image db img)) = num_images db) \/
    (~ Is_true (mem_image db img) /\ num_images (delete_image db img) = num_images db).
Proof.
  intros.
  case (MF.In_dec (images db) img).
  intros.
  left.
  unfold mem_image.
  split.
  apply MP.F.mem_in_iff in i.
  unfold Is_true. rewrite i. tauto.

  rewrite num_images_1.
  apply cardinal_remove_1. apply i.

  intros.
  right.
  split.
  unfold mem_image.
  unfold Is_true.
  case_eq (M.mem img (images db)).
  intro.
  rewrite <- MP.F.mem_in_iff in H. contradiction.

  intro.
  rewrite <- MP.F.not_mem_in_iff in H. tauto.

  rewrite num_images_1.
  apply cardinal_bijection.
  intros.
  split.
  intro.
  apply MF.remove_in_iff in H.
  destruct H.
  apply H0.

  intro.
  case (N.eq_dec img idx).
  intros.
  rewrite e in n. contradiction.
  intro.
  assert (img <> idx /\ M.In idx (images db)).
  auto.
  rewrite <- MP.F.remove_in_iff in H0.
  apply H0.
Qed.

Theorem size_nochange : forall (db : ImageDb) (img : ImageId) (cat : CategoryId),
    num_images (tag_image db img cat) = num_images db /\
    num_images (untag_image db img cat) = num_images db.
Proof.
  intros.
  split.
  destruct db.
  unfold num_images.
  unfold tag_image.
  unfold images. tauto.

  destruct db.
  unfold num_images.
  unfold untag_image.
  unfold images. tauto.
Qed.

End Database.

(* Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ] *)
(*                                        "(\f0 fS n -> if n Prelude.<= 0 then f0 () else fS ( n Prelude.- 1))". *)
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extraction Language Haskell.
Extraction "Database" Database.
(* Extraction create_image. *)
(* Extraction find_categories. *)
(* Extraction delete_image. *)
(* Extraction tag_image. *)
(* Extraction untag_image. *)
