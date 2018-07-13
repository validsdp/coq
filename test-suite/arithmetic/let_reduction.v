Require Import Int63.

Open Scope int63_scope.

Definition div_eucl_plus_one i1 i2 :=
  let (q,r) := diveucl i1 i2 in
  (q+1, r+1)%int63.

Definition rcbn := Eval cbn in div_eucl_plus_one 3 2.
Check (eq_refl : rcbn = (2, 2)).

Definition rcbv := Eval cbv in div_eucl_plus_one 3 2.
Check (eq_refl : rcbv = (2, 2)).

Definition rvmc := Eval vm_compute in div_eucl_plus_one 3 2.
Check (eq_refl : rvmc = (2, 2)).
