(** * Theorems on well founded relations *)
From stdpp Require Import base.
From stdpp Require Import options.

Lemma Acc_impl {A} (R1 R2 : relation A) x :
  Acc R1 x → (∀ y1 y2, R2 y1 y2 → R1 y1 y2) → Acc R2 x.
Proof. induction 1; constructor; auto. Qed.

Notation wf := well_founded.

(** The function [wf_guard n wfR] adds [2 ^ n - 1] times an [Acc_intro]
constructor ahead of the [wfR] proof. This definition can be used to make
opaque [wf] proofs "compute". For big enough [n], say [32], computation will
reach implementation limits before running into the opaque [wf] proof.

This trick is originally due to Georges Gonthier, see
https://sympa.inria.fr/sympa/arc/coq-club/2007-07/msg00013.html *)
Definition wf_guard `{R : relation A} (n : nat) (wfR : wf R) : wf R :=
  Acc_intro_generator n wfR.

(* Generally we do not want [wf_guard] to be expanded (neither by tactics,
nor by conversion tests in the kernel), but in some cases we do need it for
computation (that is, we cannot make it opaque). We use the [Strategy]
command to make its expanding behavior less eager. *)
Strategy 100 [wf_guard].

Lemma wf_projected `{R1 : relation A} `(R2 : relation B) (f : A → B) :
  (∀ x y, R1 x y → R2 (f x) (f y)) →
  wf R2 → wf R1.
Proof.
  intros Hf Hwf.
  cut (∀ y, Acc R2 y → ∀ x, y = f x → Acc R1 x).
  { intros aux x. apply (aux (f x)); auto. }
  induction 1 as [y _ IH]. intros x ?. subst.
  constructor. intros y ?. apply (IH (f y)); auto.
Qed.

Lemma Fix_F_proper `{R : relation A} (B : A → Type) (E : ∀ x, relation (B x))
    (F : ∀ x, (∀ y, R y x → B y) → B x)
    (HF : ∀ (x : A) (f g : ∀ y, R y x → B y),
      (∀ y Hy Hy', E _ (f y Hy) (g y Hy')) → E _ (F x f) (F x g))
    (x : A) (acc1 acc2 : Acc R x) :
  E _ (Fix_F B F acc1) (Fix_F B F acc2).
Proof. revert x acc1 acc2. fix FIX 2. intros x [acc1] [acc2]; simpl; auto. Qed.

Lemma Fix_unfold_rel `{R : relation A} (wfR : wf R) (B : A → Type) (E : ∀ x, relation (B x))
    (F: ∀ x, (∀ y, R y x → B y) → B x)
    (HF: ∀ (x: A) (f g: ∀ y, R y x → B y),
           (∀ y Hy Hy', E _ (f y Hy) (g y Hy')) → E _ (F x f) (F x g))
    (x: A) :
  E _ (Fix wfR B F x) (F x (λ y _, Fix wfR B F y)).
Proof.
  unfold Fix.
  destruct (wfR x); simpl.
  apply HF; intros.
  apply Fix_F_proper; auto.
Qed.
