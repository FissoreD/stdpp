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
(* From elpi Require Export tc. *)
(* #[export] Elpi TC Set Time All. *)
From elpi Require Import elpi.
Elpi Command TC.
Elpi Accumulate TC lp:{{
  main _.
}}.

Elpi Command TC.AddAllClasses.
Elpi Accumulate TC.AddAllClasses lp:{{
  main _.
  % :after "0" main _.
}}.
Elpi Command TC.AddAllInstances.
Elpi Accumulate TC.AddAllInstances lp:{{
  main _.
  % :after "0" main _.
}}.
Elpi Command TC.AddInstances.
Elpi Accumulate TC.AddInstances lp:{{
  main _.
  % :after "0" main _.
}}.
Elpi Command TC.Pending_mode.
Elpi Accumulate TC.Pending_mode lp:{{
  main _.
  % :after "0" main _.
}}.
Elpi Tactic TC.Solver.
Elpi Accumulate TC.Solver lp:{{
  main _.
  % :after "0" main _.
}}.
Elpi Command TC.Compiler.
Elpi Accumulate TC.Compiler lp:{{
  main _.
  % :after "0" main _.
}}.

Elpi Export TC.Pending_mode.
Elpi Export TC.AddAllClasses.
Elpi Export TC.AddAllInstances.
Elpi Export TC.AddInstances.
Elpi Export TC.Solver.



(* Uncomment following line to print stats *)
(* Global Set Debug "elpitime".
Elpi Accumulate tc.db lp:{{
  :after "0"
  time-aux _ Msg Time :- !,
  coq.debug "[TC] Benching - Time of" Msg "is" Time. 
}}. *)