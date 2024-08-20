(** Coq configuration for std++ (not meant to leak to clients).
If you are a user of std++, note that importing this file means
you are implicitly opting-in to every new option we will add here
in the future. We are *not* guaranteeing any kind of stability here.
Instead our advice is for you to have your own options file; then
you can re-export the std++ file there but if we ever add an option
you disagree with you can easily overwrite it in one central location. *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

(** Allow async proof-checking of sections. *)
#[export] Set Default Proof Using "Type".
(* FIXME: cannot enable this yet as some files disable 'Default Proof Using'.
#[export] Set Suggest Proof Using. *)

(** Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
#[export] Set Default Goal Selector "!".

(* "Fake" import to whitelist this file for the check that ensures we import
this file everywhere.
From stdpp Require Import options.
*)
From elpi.apps Require Export tc.
(* #[export] Elpi TC Set Time All. *)

(* Uncomment following line to print stats *)
(* Global Set Debug "elpitime".
Elpi Accumulate tc.db lp:{{
  :after "0"
  time-is-active _ :- !.
}}. *)

Elpi Accumulate TC.Solver lp:{{
  pred is-seal-mode i:sealed-goal, o:sealed-goal.
  is-seal-mode (seal-mode S) S :- !.
  is-seal-mode (seal G) (seal G) :- !.
  is-seal-mode (nabla B) (nabla C) :- pi x\ is-seal-mode (B x) (C x).

  pred partition-clean-s-mode i:list A, o:list B, o:list A.
  partition-clean-s-mode [] [] [] :- !.
  partition-clean-s-mode [H|L] [A|M] N :- is-seal-mode H A, !, partition-clean-s-mode L M N.
  partition-clean-s-mode [H|L] M [H|N] :- partition-clean-s-mode L M N.

  type seal-mode sealed-goal -> sealed-goal.

  :after "0"
  % tc.refine-proof tc.tc.mode_fail G [seal-mode (seal G)] :- !.
  tc.refine-proof tc.tc.mode_fail G [seal-mode (seal G)] :- !.
  :after "0" 
  msolve L N :-
    std.length L Len,
    % tc.time-it tc.oTC-time-msolve (coq.ltac.all (coq.ltac.open tc.solve-aux) L N') "msolve",
    tc.time-it tc.oTC-time-msolve (coq.ltac.all (coq.ltac.open tc.solve-aux) L N') "msolve",
    partition-clean-s-mode N' SealMode Seal,
    if2 (SealMode = []) (N = N') 
        (std.length SealMode Len) (N = SealMode)
        (msolve SealMode N'', std.append Seal N'' N).
  :after "1"
  msolve L _ :-
    coq.ltac.fail _ "[TC] fail to solve" L.
}}.
Set Warnings "+elpi".
Elpi Typecheck TC.Solver.