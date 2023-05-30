From stdpp Require Import strings.
From stdpp.unstable Require Import bitvector.

Check "notation_test".
Check (BV 10 3 = BV 10 5).
Fail Check (BV 2 3 = BV 10 5).
Check (BV 2 3 =@{bvn} BV 10 5).

Check "bvn_to_bv_test".
Goal bvn_to_bv 2 (BV 2 3) = Some (BV 2 3). Proof. simpl. Show. done. Abort.
