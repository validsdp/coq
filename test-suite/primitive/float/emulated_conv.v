Require Import ZArith Float.

Definition two := Eval compute in (one + one)%float.
Definition half := Eval compute in (one / two)%float.
Definition huge := Eval compute in ldexp one (1023)%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.
Definition denorm := Eval compute in ldexp one (-1074)%Z.

Check (eq_refl : EF2Prim (Prim2EF zero) = zero).
Check (eq_refl : EF2Prim (Prim2EF neg_zero) = neg_zero).
Check (eq_refl : EF2Prim (Prim2EF one) = one).
Check (eq_refl : EF2Prim (Prim2EF (-one)) = (-one)%float).
Check (eq_refl : EF2Prim (Prim2EF infinity) = infinity).
Check (eq_refl : EF2Prim (Prim2EF neg_infinity) = neg_infinity).
Check (eq_refl : EF2Prim (Prim2EF huge) = huge).
Check (eq_refl : EF2Prim (Prim2EF tiny) = tiny).
Check (eq_refl : EF2Prim (Prim2EF denorm) = denorm).
Check (eq_refl : EF2Prim (Prim2EF nan) = nan).
Check (eq_refl : EF2Prim (Prim2EF two) = two).
Check (eq_refl : EF2Prim (Prim2EF half) = half).
