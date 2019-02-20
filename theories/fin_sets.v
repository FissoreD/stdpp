(* Copyright (c) 2012-2019, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on finite sets. Most
importantly, it implements a fold and size function and some useful induction
principles on finite sets . *)
From stdpp Require Import relations.
From stdpp Require Export numbers sets.
Set Default Proof Using "Type*".

Instance set_size `{Elements A C} : Size C := length ∘ elements.
Definition set_fold `{Elements A C} {B}
  (f : A → B → B) (b : B) : C → B := foldr f b ∘ elements.

Instance set_filter
    `{Elements A C, Empty C, Singleton A C, Union C} : Filter A C := λ P _ X,
  list_to_set (filter P (elements X)).
Typeclasses Opaque set_filter.

Definition set_map `{Elements A C, Singleton B D, Empty D, Union D}
    (f : A → B) (X : C) : D :=
  list_to_set (f <$> elements X).
Typeclasses Opaque set_map.

Section fin_set.
Context `{FinSet A C}.
Implicit Types X Y : C.

Lemma fin_set_finite X : set_finite X.
Proof. by exists (elements X); intros; rewrite elem_of_elements. Qed.

Instance elem_of_dec_slow : RelDecision (∈@{C}) | 100.
Proof.
  refine (λ x X, cast_if (decide_rel (∈) x (elements X)));
    by rewrite <-(elem_of_elements _).
Defined.

(** * The [elements] operation *)
Global Instance set_unfold_elements X x P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ elements X) P.
Proof. constructor. by rewrite elem_of_elements, (set_unfold (x ∈ X) P). Qed.

Global Instance elements_proper: Proper ((≡) ==> (≡ₚ)) (elements (C:=C)).
Proof.
  intros ?? E. apply NoDup_Permutation.
  - apply NoDup_elements.
  - apply NoDup_elements.
  - intros. by rewrite !elem_of_elements, E.
Qed.

Lemma elements_empty : elements (∅ : C) = [].
Proof.
  apply elem_of_nil_inv; intros x.
  rewrite elem_of_elements, elem_of_empty; tauto.
Qed.
Lemma elements_empty_inv X : elements X = [] → X ≡ ∅.
Proof.
  intros HX; apply elem_of_equiv_empty; intros x.
  rewrite <-elem_of_elements, HX, elem_of_nil. tauto.
Qed.
Lemma elements_empty' X : elements X = [] ↔ X ≡ ∅.
Proof.
  split; intros HX; [by apply elements_empty_inv|].
  by rewrite <-Permutation_nil, HX, elements_empty.
Qed.

Lemma elements_union_singleton (X : C) x :
  x ∉ X → elements ({[ x ]} ∪ X) ≡ₚ x :: elements X.
Proof.
  intros ?; apply NoDup_Permutation.
  { apply NoDup_elements. }
  { by constructor; rewrite ?elem_of_elements; try apply NoDup_elements. }
  intros y; rewrite elem_of_elements, elem_of_union, elem_of_singleton.
  by rewrite elem_of_cons, elem_of_elements.
Qed.
Lemma elements_singleton x : elements ({[ x ]} : C) = [x].
Proof.
  apply Permutation_singleton. by rewrite <-(right_id ∅ (∪) {[x]}),
    elements_union_singleton, elements_empty by set_solver.
Qed.
Lemma elements_submseteq X Y : X ⊆ Y → elements X ⊆+ elements Y.
Proof.
  intros; apply NoDup_submseteq; eauto using NoDup_elements.
  intros x. rewrite !elem_of_elements; auto.
Qed.

(** * The [size] operation *)
Global Instance set_size_proper: Proper ((≡) ==> (=)) (@size C _).
Proof. intros ?? E. apply Permutation_length. by rewrite E. Qed.

Lemma size_empty : size (∅ : C) = 0.
Proof. unfold size, set_size. simpl. by rewrite elements_empty. Qed.
Lemma size_empty_inv (X : C) : size X = 0 → X ≡ ∅.
Proof.
  intros; apply equiv_empty; intros x; rewrite <-elem_of_elements.
  by rewrite (nil_length_inv (elements X)), ?elem_of_nil.
Qed.
Lemma size_empty_iff (X : C) : size X = 0 ↔ X ≡ ∅.
Proof. split. apply size_empty_inv. by intros ->; rewrite size_empty. Qed.
Lemma size_non_empty_iff (X : C) : size X ≠ 0 ↔ X ≢ ∅.
Proof. by rewrite size_empty_iff. Qed.

Lemma set_choose_or_empty X : (∃ x, x ∈ X) ∨ X ≡ ∅.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - apply equiv_empty; intros x. by rewrite <-elem_of_elements, HX, elem_of_nil.
  - exists x. rewrite <-elem_of_elements, HX. by left.
Qed.
Lemma set_choose X : X ≢ ∅ → ∃ x, x ∈ X.
Proof. intros. by destruct (set_choose_or_empty X). Qed.
Lemma set_choose_L `{!LeibnizEquiv C} X : X ≠ ∅ → ∃ x, x ∈ X.
Proof. unfold_leibniz. apply set_choose. Qed.
Lemma size_pos_elem_of X : 0 < size X → ∃ x, x ∈ X.
Proof.
  intros Hsz. destruct (set_choose_or_empty X) as [|HX]; [done|].
  contradict Hsz. rewrite HX, size_empty; lia.
Qed.

Lemma size_singleton (x : A) : size ({[ x ]} : C) = 1.
Proof. unfold size, set_size. simpl. by rewrite elements_singleton. Qed.
Lemma size_singleton_inv X x y : size X = 1 → x ∈ X → y ∈ X → x = y.
Proof.
  unfold size, set_size. simpl. rewrite <-!elem_of_elements.
  generalize (elements X). intros [|? l]; intro; simplify_eq/=.
  rewrite (nil_length_inv l), !elem_of_list_singleton by done; congruence.
Qed.
Lemma size_1_elem_of X : size X = 1 → ∃ x, X ≡ {[ x ]}.
Proof.
  intros E. destruct (size_pos_elem_of X); auto with lia.
  exists x. apply elem_of_equiv. split.
  - rewrite elem_of_singleton. eauto using size_singleton_inv.
  - set_solver.
Qed.

Lemma size_union X Y : X ## Y → size (X ∪ Y) = size X + size Y.
Proof.
  intros. unfold size, set_size. simpl. rewrite <-app_length.
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_elements.
  - apply NoDup_app; repeat split; try apply NoDup_elements.
    intros x; rewrite !elem_of_elements; set_solver.
  - intros. by rewrite elem_of_app, !elem_of_elements, elem_of_union.
Qed.
Lemma size_union_alt X Y : size (X ∪ Y) = size X + size (Y ∖ X).
Proof.
  rewrite <-size_union by set_solver.
  setoid_replace (Y ∖ X) with ((Y ∪ X) ∖ X) by set_solver.
  rewrite <-union_difference, (comm (∪)); set_solver.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof. intros. rewrite (union_difference X Y), size_union_alt by done. lia. Qed.
Lemma subset_size X Y : X ⊂ Y → size X < size Y.
Proof.
  intros. rewrite (union_difference X Y) by set_solver.
  rewrite size_union_alt, difference_twice.
  cut (size (Y ∖ X) ≠ 0); [lia |].
  by apply size_non_empty_iff, non_empty_difference.
Qed.

(** * Induction principles *)
Lemma set_wf : wf (⊂@{C}).
Proof. apply (wf_projected (<) size); auto using subset_size, lt_wf. Qed.
Lemma set_ind (P : C → Prop) :
  Proper ((≡) ==> iff) P →
  P ∅ → (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) → ∀ X, P X.
Proof.
  intros ? Hemp Hadd. apply well_founded_induction with (⊂).
  { apply set_wf. }
  intros X IH. destruct (set_choose_or_empty X) as [[x ?]|HX].
  - rewrite (union_difference {[ x ]} X) by set_solver.
    apply Hadd. set_solver. apply IH; set_solver.
  - by rewrite HX.
Qed.
Lemma set_ind_L `{!LeibnizEquiv C} (P : C → Prop) :
  P ∅ → (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) → ∀ X, P X.
Proof. apply set_ind. by intros ?? ->%leibniz_equiv_iff. Qed.

(** * The [set_fold] operation *)
Lemma set_fold_ind {B} (P : B → C → Prop) (f : A → B → B) (b : B) :
  Proper ((=) ==> (≡) ==> iff) P →
  P b ∅ → (∀ x X r, x ∉ X → P r X → P (f x r) ({[ x ]} ∪ X)) →
  ∀ X, P (set_fold f b X) X.
Proof.
  intros ? Hemp Hadd.
  cut (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ x ∈ l) → P (foldr f b l) X).
  { intros help ?. apply help; [apply NoDup_elements|].
    symmetry. apply elem_of_elements. }
  induction 1 as [|x l ?? IH]; simpl.
  - intros X HX. setoid_rewrite elem_of_nil in HX.
    rewrite equiv_empty. done. set_solver.
  - intros X HX. setoid_rewrite elem_of_cons in HX.
    rewrite (union_difference {[ x ]} X) by set_solver.
    apply Hadd. set_solver. apply IH. set_solver.
Qed.
Lemma set_fold_proper {B} (R : relation B) `{!Equivalence R}
    (f : A → B → B) (b : B) `{!Proper ((=) ==> R ==> R) f}
    (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((≡) ==> R) (set_fold f b : C → B).
Proof. intros ?? E. apply (foldr_permutation R f b); auto. by rewrite E. Qed.

(** * Minimal elements *)
Lemma minimal_exists R `{!Transitive R, ∀ x y, Decision (R x y)} (X : C) :
  X ≢ ∅ → ∃ x, x ∈ X ∧ minimal R x X.
Proof.
  pattern X; apply set_ind; clear X.
  { by intros X X' HX; setoid_rewrite HX. }
  { done. }
  intros x X ? IH Hemp. destruct (set_choose_or_empty X) as [[z ?]|HX].
  { destruct IH as (x' & Hx' & Hmin); [set_solver|].
    destruct (decide (R x x')).
    - exists x; split; [set_solver|].
      eauto using (union_minimal (C:=C)), (singleton_minimal (C:=C)), minimal_weaken.
    - exists x'; split; [set_solver|].
      eauto using (union_minimal (C:=C)), (singleton_minimal_not_above (C:=C)). }
  exists x; split; [set_solver|].
  rewrite HX, (right_id _ (∪)). apply singleton_minimal.
Qed.
Lemma minimal_exists_L R `{!LeibnizEquiv C, !Transitive R,
    ∀ x y, Decision (R x y)} (X : C) :
  X ≠ ∅ → ∃ x, x ∈ X ∧ minimal R x X.
Proof. unfold_leibniz. apply (minimal_exists R). Qed.

(** * Filter *)
Section filter.
  Context (P : A → Prop) `{!∀ x, Decision (P x)}.

  Lemma elem_of_filter X x : x ∈ filter P X ↔ P x ∧ x ∈ X.
  Proof.
    unfold filter, set_filter.
    by rewrite elem_of_list_to_set, elem_of_list_filter, elem_of_elements.
  Qed.
  Global Instance set_unfold_filter X Q :
    SetUnfold (x ∈ X) Q → SetUnfold (x ∈ filter P X) (P x ∧ Q).
  Proof.
    intros ??; constructor. by rewrite elem_of_filter, (set_unfold (x ∈ X) Q).
  Qed.

  Lemma filter_empty : filter P (∅:C) ≡ ∅.
  Proof. set_solver. Qed.
  Lemma filter_union X Y : filter P (X ∪ Y) ≡ filter P X ∪ filter P Y.
  Proof. set_solver. Qed.
  Lemma filter_singleton x : P x → filter P ({[ x ]} : C) ≡ {[ x ]}.
  Proof. set_solver. Qed.
  Lemma filter_singleton_not x : ¬P x → filter P ({[ x ]} : C) ≡ ∅.
  Proof. set_solver. Qed.

  Section leibniz_equiv.
    Context `{!LeibnizEquiv C}.
    Lemma filter_empty_L : filter P (∅:C) = ∅.
    Proof. set_solver. Qed.
    Lemma filter_union_L X Y : filter P (X ∪ Y) = filter P X ∪ filter P Y.
    Proof. set_solver. Qed.
    Lemma filter_singleton_L x : P x → filter P ({[ x ]} : C) = {[ x ]}.
    Proof. set_solver. Qed.
    Lemma filter_singleton_not_L x : ¬P x → filter P ({[ x ]} : C) = ∅.
    Proof. set_solver. Qed.
  End leibniz_equiv.
End filter.

(** * Map *)
Section map.
  Context `{Set_ B D}.

  Lemma elem_of_map (f : A → B) (X : C) y :
    y ∈ set_map (D:=D) f X ↔ ∃ x, y = f x ∧ x ∈ X.
  Proof.
    unfold set_map. rewrite elem_of_list_to_set, elem_of_list_fmap.
    by setoid_rewrite elem_of_elements.
  Qed.
  Global Instance set_unfold_map (f : A → B) (X : C) (P : A → Prop) :
    (∀ y, SetUnfold (y ∈ X) (P y)) →
    SetUnfold (x ∈ set_map (D:=D) f X) (∃ y, x = f y ∧ P y).
  Proof. constructor. rewrite elem_of_map; naive_solver. Qed.

  Global Instance set_map_proper :
    Proper (pointwise_relation _ (=) ==> (≡) ==> (≡)) (set_map (C:=C) (D:=D)).
  Proof. intros f g ? X Y. set_unfold; naive_solver. Qed.
  Global Instance set_map_mono :
    Proper (pointwise_relation _ (=) ==> (⊆) ==> (⊆)) (set_map (C:=C) (D:=D)).
  Proof. intros f g ? X Y. set_unfold; naive_solver. Qed.

  Lemma elem_of_map_1 (f : A → B) (X : C) (y : B) :
    y ∈ set_map (D:=D) f X → ∃ x, y = f x ∧ x ∈ X.
  Proof. set_solver. Qed.
  Lemma elem_of_map_2 (f : A → B) (X : C) (x : A) :
    x ∈ X → f x ∈ set_map (D:=D) f X.
  Proof. set_solver. Qed.
  Lemma elem_of_map_2_alt (f : A → B) (X : C) (x : A) (y : B) :
    x ∈ X → y = f x → y ∈ set_map (D:=D) f X.
  Proof. set_solver. Qed.
End map.

(** * Decision procedures *)
Lemma set_Forall_elements P X : set_Forall P X ↔ Forall P (elements X).
Proof. rewrite Forall_forall. by setoid_rewrite elem_of_elements. Qed.
Lemma set_Exists_elements P X : set_Exists P X ↔ Exists P (elements X).
Proof. rewrite Exists_exists. by setoid_rewrite elem_of_elements. Qed.

Lemma set_Forall_Exists_dec (P Q : A → Prop) (dec : ∀ x, {P x} + {Q x}) X :
  {set_Forall P X} + {set_Exists Q X}.
Proof.
 refine (cast_if (Forall_Exists_dec P Q dec (elements X)));
   [by apply set_Forall_elements|by apply set_Exists_elements].
Defined.

Lemma not_set_Forall_Exists P `{dec : ∀ x, Decision (P x)} X :
  ¬set_Forall P X → set_Exists (not ∘ P) X.
Proof. intro. by destruct (set_Forall_Exists_dec P (not ∘ P) dec X). Qed.
Lemma not_set_Exists_Forall P `{dec : ∀ x, Decision (P x)} X :
  ¬set_Exists P X → set_Forall (not ∘ P) X.
Proof.
  by destruct (set_Forall_Exists_dec
    (not ∘ P) P (λ x, swap_if (decide (P x))) X).
Qed.

Global Instance set_Forall_dec (P : A → Prop) `{∀ x, Decision (P x)} X :
  Decision (set_Forall P X) | 100.
Proof.
 refine (cast_if (decide (Forall P (elements X))));
   by rewrite set_Forall_elements.
Defined.
Global Instance set_Exists_dec `(P : A → Prop) `{∀ x, Decision (P x)} X :
  Decision (set_Exists P X) | 100.
Proof.
 refine (cast_if (decide (Exists P (elements X))));
   by rewrite set_Exists_elements.
Defined.
End fin_set.
