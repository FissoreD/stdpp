From elpi Require Import elpi.

Elpi Command B.
Section A.
  Context (A:Type).
  Elpi Query  lp:{{
    X = {{A}}
  }}.
  Elpi Accumulate  lp:{{
    pred x i:term.
    % x {{A}}. ERROR
    x (global {{:gref A}}).
  }}.
  Elpi Typecheck.


