(* Copyright (c) 2012-2017, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on vectors
(lists of fixed length) and the fin type (bounded naturals). It uses the
definitions from the standard library, but renames or changes their notations,
so that it becomes more consistent with the naming conventions in this
development. *)
From stdpp Require Export list.
Set Default Proof Using "Type".
Open Scope vector_scope.

(** * The fin type *)
(** The type [fin n] represents natural numbers [i] with [0 ≤ i < n]. We
define a scope [fin], in which we declare notations for small literals of the
[fin] type. Whereas the standard library starts counting at [1], we start
counting at [0]. This way, the embedding [fin_to_nat] preserves [0], and allows
us to define [fin_to_nat] as a coercion without introducing notational
ambiguity. *)
Notation fin := Fin.t.
Notation FS := Fin.FS.

Delimit Scope fin_scope with fin.
Arguments Fin.FS _ _%fin.

Notation "0" := Fin.F1 : fin_scope. Notation "1" := (FS 0) : fin_scope.
Notation "2" := (FS 1) : fin_scope. Notation "3" := (FS 2) : fin_scope.
Notation "4" := (FS 3) : fin_scope. Notation "5" := (FS 4) : fin_scope.
Notation "6" := (FS 5) : fin_scope. Notation "7" := (FS 6) : fin_scope.
Notation "8" := (FS 7) : fin_scope. Notation "9" := (FS 8) : fin_scope.
Notation "10" := (FS 9) : fin_scope.

Fixpoint fin_to_nat {n} (i : fin n) : nat :=
  match i with 0%fin => 0 | FS _ i => S (fin_to_nat i) end.
Coercion fin_to_nat : fin >-> nat.

Notation fin_of_nat := Fin.of_nat_lt.
Notation fin_rect2 := Fin.rect2.

Instance fin_dec {n} : EqDecision (fin n).
Proof.
 refine (fin_rect2
  (λ n (i j : fin n), { i = j } + { i ≠ j })
  (λ _, left _)
  (λ _ _, right _)
  (λ _ _, right _)
  (λ _ _ _ H, cast_if H));
  abstract (f_equal; by auto using Fin.FS_inj).
Defined.

(** The inversion principle [fin_S_inv] is more convenient than its variant
[Fin.caseS] in the standard library, as we keep the parameter [n] fixed.
In the tactic [inv_fin i] to perform dependent case analysis on [i], we
therefore do not have to generalize over the index [n] and all assumptions
depending on it. Notice that contrary to [dependent destruction], which uses
the [JMeq_eq] axiom, the tactic [inv_fin] produces axiom free proofs.*)
Notation fin_0_inv := Fin.case0.

Definition fin_S_inv {n} (P : fin (S n) → Type)
  (H0 : P 0%fin) (HS : ∀ i, P (FS i)) (i : fin (S n)) : P i.
Proof.
  revert P H0 HS.
  refine match i with 0%fin => λ _ H0 _, H0 | FS _ i => λ _ _ HS, HS i end.
Defined.

Ltac inv_fin i :=
  match type of i with
  | fin 0 =>
    revert dependent i; match goal with |- ∀ i, @?P i => apply (fin_0_inv P) end
  | fin (S ?n) =>
    revert dependent i; match goal with |- ∀ i, @?P i => apply (fin_S_inv P) end
  end.

Instance FS_inj: Inj (=) (=) (@FS n).
Proof. intros n i j. apply Fin.FS_inj. Qed.
Instance fin_to_nat_inj : Inj (=) (=) (@fin_to_nat n).
Proof.
  intros n i. induction i; intros j; inv_fin j; intros; f_equal/=; auto with lia.
Qed.

Lemma fin_to_nat_lt {n} (i : fin n) : fin_to_nat i < n.
Proof. induction i; simpl; lia. Qed.
Lemma fin_to_of_nat n m (H : n < m) : fin_to_nat (fin_of_nat H) = n.
Proof.
  revert m H. induction n; intros [|?]; simpl; auto; intros; exfalso; lia.
Qed.
Lemma fin_of_to_nat {n} (i : fin n) H : @fin_of_nat (fin_to_nat i) n H = i.
Proof. apply (inj fin_to_nat), fin_to_of_nat. Qed.

Fixpoint fin_plus_inv {n1 n2} : ∀ (P : fin (n1 + n2) → Type)
    (H1 : ∀ i1 : fin n1, P (Fin.L n2 i1))
    (H2 : ∀ i2, P (Fin.R n1 i2)) (i : fin (n1 + n2)), P i :=
  match n1 with
  | 0 => λ P H1 H2 i, H2 i
  | S n => λ P H1 H2, fin_S_inv P (H1 0%fin) (fin_plus_inv _ (λ i, H1 (FS i)) H2)
  end.

Lemma fin_plus_inv_L {n1 n2} (P : fin (n1 + n2) → Type)
    (H1: ∀ i1 : fin n1, P (Fin.L _ i1)) (H2: ∀ i2, P (Fin.R _ i2)) (i: fin n1) :
  fin_plus_inv P H1 H2 (Fin.L n2 i) = H1 i.
Proof.
  revert P H1 H2 i.
  induction n1 as [|n1 IH]; intros P H1 H2 i; inv_fin i; simpl; auto.
  intros i. apply (IH (λ i, P (FS i))).
Qed.

Lemma fin_plus_inv_R {n1 n2} (P : fin (n1 + n2) → Type)
    (H1: ∀ i1 : fin n1, P (Fin.L _ i1)) (H2: ∀ i2, P (Fin.R _ i2)) (i: fin n2) :
  fin_plus_inv P H1 H2 (Fin.R n1 i) = H2 i.
Proof.
  revert P H1 H2 i; induction n1 as [|n1 IH]; intros P H1 H2 i; simpl; auto.
  apply (IH (λ i, P (FS i))).
Qed.

(** * Vectors *)
(** The type [vec n] represents lists of consisting of exactly [n] elements.
Whereas the standard library declares exactly the same notations for vectors as
used for lists, we use slightly different notations so it becomes easier to use
lists and vectors together. *)
Notation vec := Vector.t.
Notation vnil := Vector.nil.
Arguments vnil {_}.
Notation vcons := Vector.cons.
Notation vapp := Vector.append.
Arguments vcons {_} _ {_} _.

Infix ":::" := vcons (at level 60, right associativity) : vector_scope.
Notation "(:::)" := vcons (only parsing) : vector_scope.
Notation "( x :::)" := (vcons x) (only parsing) : vector_scope.
Notation "(::: v )" := (λ x, vcons x v) (only parsing) : vector_scope.
Notation "[# ] " := vnil : vector_scope.
Notation "[# x ] " := (vcons x vnil) : vector_scope.
Notation "[# x ; .. ; y ] " := (vcons x .. (vcons y vnil) ..) : vector_scope.
Infix "+++" := vapp (at level 60, right associativity) : vector_scope.
Notation "(+++)" := vapp (only parsing) : vector_scope.
Notation "( v +++)" := (vapp v) (only parsing) : vector_scope.
Notation "(+++ w )" := (λ v, vapp v w) (only parsing) : vector_scope.

(** Notice that we cannot define [Vector.nth] as an instance of our [Lookup]
type class, as it has a dependent type. *)
Arguments Vector.nth {_ _} !_ !_%fin /.
Infix "!!!" := Vector.nth (at level 20) : vector_scope.

(** The tactic [vec_double_ind v1 v2] performs double induction on [v1] and [v2]
provided that they have the same length. *)
Notation vec_rect2 := Vector.rect2.
Ltac vec_double_ind v1 v2 :=
  match type of v1 with
  | vec _ ?n =>
    repeat match goal with
    | H' : context [ n ] |- _ => var_neq v1 H'; var_neq v2 H'; revert H'
    end;
    revert n v1 v2;
    match goal with |- ∀ n v1 v2, @?P n v1 v2 => apply (vec_rect2 P) end
  end.

Notation vcons_inj := VectorSpec.cons_inj.
Lemma vcons_inj_1 {A n} x y (v w : vec A n) : x ::: v = y ::: w → x = y.
Proof. apply vcons_inj. Qed.
Lemma vcons_inj_2 {A n} x y (v w : vec A n) : x ::: v = y ::: w → v = w.
Proof. apply vcons_inj. Qed.

Lemma vec_eq {A n} (v w : vec A n) : (∀ i, v !!! i = w !!! i) → v = w.
Proof.
  vec_double_ind v w; [done|]. intros n v w IH x y Hi. f_equal.
  - apply (Hi 0%fin).
  - apply IH. intros i. apply (Hi (FS i)).
Qed.

Instance vec_dec {A} {dec : EqDecision A} {n} : EqDecision (vec A n).
Proof.
 refine (vec_rect2
  (λ n (v w : vec A n), { v = w } + { v ≠ w })
  (left _)
  (λ _ _ _ H x y, cast_if_and (dec x y) H));
  f_equal; eauto using vcons_inj_1, vcons_inj_2.
Defined.

(** Similar to [fin], we provide an inversion principle that keeps the length
fixed. We define a tactic [inv_vec v] to perform case analysis on [v], using
this inversion principle. *)
Notation vec_0_inv := Vector.case0.
Definition vec_S_inv {A n} (P : vec A (S n) → Type)
  (Hcons : ∀ x v, P (x ::: v)) v : P v.
Proof.
  revert P Hcons.
  refine match v with [#] => tt | x ::: v => λ P Hcons, Hcons x v end.
Defined.

Ltac inv_vec v :=
  let T := type of v in
  match eval hnf in T with
  | vec _ 0 =>
    revert dependent v; match goal with |- ∀ v, @?P v => apply (vec_0_inv P) end
  | vec _ (S ?n) =>
    revert dependent v; match goal with |- ∀ v, @?P v => apply (vec_S_inv P) end;
    try (let x := fresh "x" in intros x v; inv_vec v; revert x)
  end.

(** The following tactic performs case analysis on all hypotheses of the shape
[fin 0], [fin (S n)], [vec A 0] and [vec A (S n)] until no further case
analyses are possible. *)
Ltac inv_all_vec_fin := block_goal;
  repeat match goal with
  | v : vec _ _ |- _ => inv_vec v; intros
  | i : fin _ |- _ => inv_fin i; intros
  end; unblock_goal.

(** We define a coercion from [vec] to [list] and show that it preserves the
operations on vectors. We also define a function to go in the other way, but
do not define it as a coercion, as it would otherwise introduce ambiguity. *)
Fixpoint vec_to_list {A n} (v : vec A n) : list A :=
  match v with [#] => [] | x ::: v => x :: vec_to_list v end.
Coercion vec_to_list : vec >-> list.
Notation list_to_vec := Vector.of_list.

Lemma vec_to_list_cons {A n} x (v : vec A n) :
  vec_to_list (x ::: v) = x :: vec_to_list v.
Proof. done. Qed.
Lemma vec_to_list_app {A n m} (v : vec A n) (w : vec A m) :
  vec_to_list (v +++ w) = vec_to_list v ++ vec_to_list w.
Proof. by induction v; f_equal/=. Qed.
Lemma vec_to_list_of_list {A} (l : list A): vec_to_list (list_to_vec l) = l.
Proof. by induction l; f_equal/=. Qed.
Lemma vec_to_list_length {A n} (v : vec A n) : length (vec_to_list v) = n.
Proof. induction v; simpl; by f_equal. Qed.
Lemma vec_to_list_same_length {A B n} (v : vec A n) (w : vec B n) :
  length v = length w.
Proof. by rewrite !vec_to_list_length. Qed.
Lemma vec_to_list_inj1 {A n m} (v : vec A n) (w : vec A m) :
  vec_to_list v = vec_to_list w → n = m.
Proof.
  revert m w. induction v; intros ? [|???] ?;
    simplify_eq/=; f_equal; eauto.
Qed.
Lemma vec_to_list_inj2 {A n} (v : vec A n) (w : vec A n) :
  vec_to_list v = vec_to_list w → v = w.
Proof.
  revert w. induction v; intros w; inv_vec w; intros;
    simplify_eq/=; f_equal; eauto.
Qed.
Lemma vlookup_middle {A n m} (v : vec A n) (w : vec A m) x :
  ∃ i : fin (n + S m), x = (v +++ x ::: w) !!! i.
Proof.
  induction v; simpl; [by eexists 0%fin|].
  destruct IHv as [i ?]. by exists (FS i).
Qed.
Lemma vec_to_list_lookup_middle {A n} (v : vec A n) (l k : list A) x :
  vec_to_list v = l ++ x :: k →
    ∃ i : fin n, l = take i v ∧ x = v !!! i ∧ k = drop (S i) v.
Proof.
  intros H.
  rewrite <-(vec_to_list_of_list l), <-(vec_to_list_of_list k) in H.
  rewrite <-vec_to_list_cons, <-vec_to_list_app in H.
  pose proof (vec_to_list_inj1 _ _ H); subst.
  apply vec_to_list_inj2 in H; subst. induction l. simpl.
  - eexists 0%fin. simpl. by rewrite vec_to_list_of_list.
  - destruct IHl as [i ?]. exists (FS i). simpl. intuition congruence.
Qed.
Lemma vec_to_list_drop_lookup {A n} (v : vec A n) (i : fin n) :
  drop i v = v !!! i :: drop (S i) v.
Proof. induction i; inv_vec v; simpl; intros; [done | by rewrite IHi]. Qed.
Lemma vec_to_list_take_drop_lookup {A n} (v : vec A n) (i : fin n) :
  vec_to_list v = take i v ++ v !!! i :: drop (S i) v.
Proof. rewrite <-(take_drop i v) at 1. by rewrite vec_to_list_drop_lookup. Qed.

Lemma vlookup_lookup {A n} (v : vec A n) (i : fin n) x :
  v !!! i = x ↔ (v : list A) !! (i : nat) = Some x.
Proof.
  induction v as [|? ? v IH]; inv_fin i. simpl; split; congruence. done.
Qed.
Lemma vlookup_lookup' {A n} (v : vec A n) (i : nat) x :
  (∃ H : i < n, v !!! (fin_of_nat H) = x) ↔ (v : list A) !! i = Some x.
Proof.
  split.
  - intros [Hlt ?]. rewrite <-(fin_to_of_nat i n Hlt). by apply vlookup_lookup.
  - intros Hvix. assert (Hlt:=lookup_lt_Some _ _ _ Hvix).
    rewrite vec_to_list_length in Hlt. exists Hlt.
    apply vlookup_lookup. by rewrite fin_to_of_nat.
Qed.
Lemma elem_of_vlookup {A n} (v : vec A n) x :
  x ∈ vec_to_list v ↔ ∃ i, v !!! i = x.
Proof.
  rewrite elem_of_list_lookup. setoid_rewrite <-vlookup_lookup'.
  split; [by intros (?&?&?); eauto|]. intros [i Hx].
  exists i, (fin_to_nat_lt _). by rewrite fin_of_to_nat.
Qed.

Lemma Forall_vlookup {A} (P : A → Prop) {n} (v : vec A n) :
  Forall P (vec_to_list v) ↔ ∀ i, P (v !!! i).
Proof. rewrite Forall_forall. setoid_rewrite elem_of_vlookup. naive_solver. Qed.
Lemma Forall_vlookup_1 {A} (P : A → Prop) {n} (v : vec A n) i :
  Forall P (vec_to_list v) → P (v !!! i).
Proof. by rewrite Forall_vlookup. Qed.
Lemma Forall_vlookup_2 {A} (P : A → Prop) {n} (v : vec A n) :
  (∀ i, P (v !!! i)) → Forall P (vec_to_list v).
Proof. by rewrite Forall_vlookup. Qed.
Lemma Exists_vlookup {A} (P : A → Prop) {n} (v : vec A n) :
  Exists P (vec_to_list v) ↔ ∃ i, P (v !!! i).
Proof. rewrite Exists_exists. setoid_rewrite elem_of_vlookup. naive_solver. Qed.
Lemma Forall2_vlookup {A B} (P : A → B → Prop) {n}
    (v1 : vec A n) (v2 : vec B n) :
  Forall2 P (vec_to_list v1) (vec_to_list v2) ↔ ∀ i, P (v1 !!! i) (v2 !!! i).
Proof.
  split.
  - vec_double_ind v1 v2; [intros _ i; inv_fin i |].
    intros n v1 v2 IH a b; simpl. inversion_clear 1.
    intros i. inv_fin i; simpl; auto.
  - vec_double_ind v1 v2; [constructor|].
    intros ??? IH ?? H. constructor. apply (H 0%fin). apply IH, (λ i, H (FS i)).
Qed.

(** The function [vmap f v] applies a function [f] element wise to [v]. *)
Notation vmap := Vector.map.

Lemma vlookup_map `(f : A → B) {n} (v : vec A n) i :
  vmap f v !!! i = f (v !!! i).
Proof. by apply Vector.nth_map. Qed.
Lemma vec_to_list_map `(f : A → B) {n} (v : vec A n) :
  vec_to_list (vmap f v) = f <$> vec_to_list v.
Proof. induction v; simpl. done. by rewrite IHv. Qed.

(** The function [vzip_with f v w] combines the vectors [v] and [w] element
wise using the function [f]. *)
Notation vzip_with := Vector.map2.

Lemma vlookup_zip_with `(f : A → B → C) {n} (v1 : vec A n) (v2 : vec B n) i :
  vzip_with f v1 v2 !!! i = f (v1 !!! i) (v2 !!! i).
Proof. by apply Vector.nth_map2. Qed.
Lemma vec_to_list_zip_with `(f : A → B → C) {n} (v1 : vec A n) (v2 : vec B n) :
  vec_to_list (vzip_with f v1 v2) =
    zip_with f (vec_to_list v1) (vec_to_list v2).
Proof.
  revert v2. induction v1; intros v2; inv_vec v2; intros; simpl; [done|].
  by rewrite IHv1.
Qed.

(** Similar to vlookup, we cannot define [vinsert] as an instance of the
[Insert] type class, as it has a dependent type. *)
Fixpoint vinsert {A n} (i : fin n) (x : A) : vec A n → vec A n :=
  match i with
  | 0%fin => vec_S_inv _ (λ _ v, x ::: v)
  | FS _ i => vec_S_inv _ (λ y v, y ::: vinsert i x v)
  end.

Lemma vec_to_list_insert {A n} i x (v : vec A n) :
  vec_to_list (vinsert i x v) = insert (fin_to_nat i) x (vec_to_list v).
Proof. induction v; inv_fin i. done. simpl. intros. by rewrite IHv. Qed.
Lemma vlookup_insert {A n} i x (v : vec A n) : vinsert i x v !!! i = x.
Proof. by induction i; inv_vec v. Qed.
Lemma vlookup_insert_ne {A n} i j x (v : vec A n) :
  i ≠ j → vinsert i x v !!! j = v !!! j.
Proof.
  induction i; inv_fin j; inv_vec v; simpl; try done.
  intros. apply IHi. congruence.
Qed.
Lemma vlookup_insert_self {A n} i (v : vec A n) : vinsert i (v !!! i) v = v.
Proof. by induction v; inv_fin i; intros; f_equal/=. Qed.

(** The function [vreplicate n x] generates a vector with length [n] of elements
with value [x]. *)
Fixpoint vreplicate {A} (n : nat) (x : A) : vec A n :=
  match n with 0 => [#] | S n => x ::: vreplicate n x end.

(* Vectors can be inhabited. *)
Global Instance vec_0_inhabited T : Inhabited (vec T 0) := populate [#].
Global Instance vec_inhabited `{Inhabited T} n : Inhabited (vec T n) :=
  populate (vreplicate n inhabitant).
