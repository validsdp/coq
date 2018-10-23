Require Import ZArith Int63 Float.

Open Scope float_scope.

Definition three := Eval compute in of_int63 3%int63.
Definition nine := Eval compute in of_int63 9%int63.

Check (eq_refl : sqrt nine = three).
Check (eq_refl three <: sqrt nine = three).
Definition compute1 := Eval compute in sqrt nine.
Check (eq_refl : three = three).

Definition huge := Eval compute in ldexp one (1023)%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.
Definition denorm := Eval compute in ldexp one (-1074)%Z.

Goal (Prim2EF (sqrt huge) = EF64sqrt (Prim2EF huge)).
  now compute. Undo. now vm_compute.
Qed.

Goal (Prim2EF (sqrt tiny) = EF64sqrt (Prim2EF tiny)).
  now compute. Undo. now vm_compute.
Qed.

Goal (Prim2EF (sqrt denorm) = EF64sqrt (Prim2EF denorm)).
  now compute. Undo. now vm_compute.
Qed.

Check (eq_refl : sqrt neg_zero = neg_zero).
Check (eq_refl neg_zero <: sqrt neg_zero = neg_zero).
Check (eq_refl neg_zero <<: sqrt neg_zero = neg_zero).
Check (eq_refl : sqrt zero = zero).
Check (eq_refl zero <: sqrt zero = zero).
Check (eq_refl zero <<: sqrt zero = zero).
Check (eq_refl : sqrt one = one).
Check (eq_refl one <: sqrt one = one).
Check (eq_refl one <<: sqrt one = one).
Check (eq_refl : sqrt (-one) = nan).
Check (eq_refl nan <: sqrt (-one) = nan).
Check (eq_refl nan <<: sqrt (-one) = nan).
Check (eq_refl : sqrt infinity = infinity).
Check (eq_refl infinity <: sqrt infinity = infinity).
Check (eq_refl infinity <<: sqrt infinity = infinity).
Check (eq_refl : sqrt neg_infinity = nan).
Check (eq_refl nan <: sqrt neg_infinity = nan).
Check (eq_refl nan <<: sqrt neg_infinity = nan).
Check (eq_refl : sqrt infinity = infinity).
Check (eq_refl infinity <: sqrt infinity = infinity).
Check (eq_refl infinity <<: sqrt infinity = infinity).
