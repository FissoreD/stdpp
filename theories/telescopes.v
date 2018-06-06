From stdpp Require Import base tactics.
Set Default Proof Using "Type".

(** Telescopes *)
Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X → tele) : tele.

Arguments TeleS {_} _.

(** The telescope version of Coq's function type *)
Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => ∀ x, tele_fun (b x) T
  end.

Notation "TT -t> A" :=
  (tele_fun TT A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [tele_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition tele_fold {X Y} {TT : tele} (step : ∀ {A : Type}, (A → Y) → Y) (base : X → Y)
  : (TT -t> X) → Y :=
  (fix rec {TT} : (TT -t> X) → Y :=
     match TT as TT return (TT -t> X) → Y with
     | TeleO => λ x : X, base x
     | TeleS b => λ f, step (λ x, rec (f x))
     end) TT.
Arguments tele_fold {_ _ !_} _ _ _ /.

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Inductive tele_arg : tele → Type :=
| TargO : tele_arg TeleO
(* the [x] is the only relevant data here *)
| TargS {X} {binder} (x : X) : tele_arg (binder x) → tele_arg (TeleS binder).

Definition tele_app {TT : tele} {T} (f : TT -t> T) : tele_arg TT → T :=
  λ a, (fix rec {TT} (a : tele_arg TT) : (TT -t> T) → T :=
     match a in tele_arg TT return (TT -t> T) → T with
     | TargO => λ t : T, t
     | TargS x a => λ f, rec a (f x)
     end) TT a f.
Arguments tele_app {!_ _} _ !_ /.

Coercion tele_arg : tele >-> Sortclass.
Coercion tele_app : tele_fun >-> Funclass.

(** Inversion lemma for [tele_arg] *)
Lemma tele_arg_inv {TT : tele} (a : TT) :
  match TT as TT return TT → Prop with
  | TeleO => λ a, a = TargO
  | TeleS f => λ a, ∃ x a', a = TargS x a'
  end a.
Proof. induction a; eauto. Qed.
Lemma tele_arg_O_inv (a : TeleO) : a = TargO.
Proof. exact (tele_arg_inv a). Qed.
Lemma tele_arg_S_inv {X} {f : X → tele} (a : TeleS f) :
  ∃ x a', a = TargS x a'.
Proof. exact (tele_arg_inv a). Qed.

(** Map below a tele_fun *)
Fixpoint tele_map {T U} {TT : tele} : (T → U) → (TT -t> T) → TT -t> U :=
  match TT as TT return (T → U) → (TT -t> T) → TT -t> U with
  | TeleO => λ F : T → U, F
  | @TeleS X b => λ (F : T → U) (f : TeleS b -t> T) (x : X),
                  tele_map F (f x)
  end.
Arguments tele_map {_ _ !_} _ _ /.

Lemma tele_map_app {T U} {TT : tele} (F : T → U) (t : TT -t> T) (x : TT) :
  (tele_map F t) x = F (t x).
Proof.
  induction TT as [|X f IH]; simpl in *.
  - rewrite (tele_arg_O_inv x). done.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. done.
Qed.

Global Instance tele_fmap {TT : tele} : FMap (tele_fun TT) := λ T U, tele_map.

Lemma tele_fmap_app {T U} {TT : tele} (F : T → U) (t : TT -t> T) (x : TT) :
  (F <$> t) x = F (t x).
Proof. apply tele_map_app. Qed.

Global Instance tele_fmap2 {TT1 TT2 : tele} : FMap (tele_fun TT1 ∘ tele_fun TT2) :=
  λ T U, tele_map ∘ tele_map.

Lemma tele_fmap2_app {T U} {TT1 TT2 : tele} (F : T → U) (t : TT1 -t> TT2 -t> T)
      (x : TT1) (y : TT2) :
  (F <$> t) x y = F (t x y).
Proof.
  unfold fmap, tele_fmap2. simpl.
  rewrite !tele_map_app. done.
Qed.

(** Operate below [tele_fun]s with argument telescope [TT]. *)
Fixpoint tele_bind {U} {TT : tele} : (TT → U) → TT -t> U :=
  match TT as TT return (TT → U) → TT -t> U with
  | TeleO => λ F, F TargO
  | @TeleS X b => λ (F : TeleS b → U) (x : X), (* b x -t> U *)
                  tele_bind (λ a, F (TargS x a))
  end.
Arguments tele_bind {_ !_} _ /.

(** A function that looks funny. *)
Definition tele_arg_id (TT : tele) : TT -t> TT := tele_bind id.

(** Notation *)
Notation "'[tele' x .. z ]" :=
  (TeleS (fun x => .. (TeleS (fun z => TeleO)) ..))
  (x binder, z binder, format "[tele  '[hv' x .. z ']' ]").
Notation "'[tele' ]" := (TeleO)
  (format "[tele ]").

Notation "'[tele_arg' x ; .. ; z ]" :=
  (TargS x ( .. (TargS z TargO) ..))
  (format "[tele_arg  '[hv' x ;  .. ;  z ']' ]").
Notation "'[tele_arg' ]" := (TargO)
  (format "[tele_arg ]").

(** Notation-compatible telescope mapping *)
Notation "'λ..' x .. y , e" :=
  (tele_app $ tele_bind (λ x, .. (tele_app $ tele_bind (λ y, e)) .. ))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e").
