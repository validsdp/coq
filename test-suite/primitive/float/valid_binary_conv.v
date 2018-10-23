Require Import ZArith Float.

Definition two := Eval compute in (one + one)%float.
Definition half := Eval compute in (one / two)%float.
Definition huge := Eval compute in ldexp one (1023)%Z.
Definition tiny := Eval compute in ldexp one (-1022)%Z.
Definition denorm := Eval compute in ldexp one (-1074)%Z.

Check (eq_refl : valid_binary (Prim2EF zero) = true).
Check (eq_refl : valid_binary (Prim2EF neg_zero) = true).
Check (eq_refl : valid_binary (Prim2EF one) = true).
Check (eq_refl : valid_binary (Prim2EF (-one)) = true).
Check (eq_refl : valid_binary (Prim2EF infinity) = true).
Check (eq_refl : valid_binary (Prim2EF neg_infinity) = true).
Check (eq_refl : valid_binary (Prim2EF huge) = true).
Check (eq_refl : valid_binary (Prim2EF tiny) = true).
Check (eq_refl : valid_binary (Prim2EF denorm) = true).
Check (eq_refl : valid_binary (Prim2EF nan) = true).
Check (eq_refl : valid_binary (Prim2EF two) = true).
Check (eq_refl : valid_binary (Prim2EF half) = true).

Check (eq_refl true <: valid_binary (Prim2EF zero) = true).
Check (eq_refl true <: valid_binary (Prim2EF neg_zero) = true).
Check (eq_refl true <: valid_binary (Prim2EF one) = true).
Check (eq_refl true <: valid_binary (Prim2EF (-one)) = true).
Check (eq_refl true <: valid_binary (Prim2EF infinity) = true).
Check (eq_refl true <: valid_binary (Prim2EF neg_infinity) = true).
Check (eq_refl true <: valid_binary (Prim2EF huge) = true).
Check (eq_refl true <: valid_binary (Prim2EF tiny) = true).
Check (eq_refl true <: valid_binary (Prim2EF denorm) = true).
Check (eq_refl true <: valid_binary (Prim2EF nan) = true).
Check (eq_refl true <: valid_binary (Prim2EF two) = true).
Check (eq_refl true <: valid_binary (Prim2EF half) = true).

Check (eq_refl true <<: valid_binary (Prim2EF zero) = true).
Check (eq_refl true <<: valid_binary (Prim2EF neg_zero) = true).
Check (eq_refl true <<: valid_binary (Prim2EF one) = true).
Check (eq_refl true <<: valid_binary (Prim2EF (-one)) = true).
Check (eq_refl true <<: valid_binary (Prim2EF infinity) = true).
Check (eq_refl true <<: valid_binary (Prim2EF neg_infinity) = true).
Check (eq_refl true <<: valid_binary (Prim2EF huge) = true).
Check (eq_refl true <<: valid_binary (Prim2EF tiny) = true).
Check (eq_refl true <<: valid_binary (Prim2EF denorm) = true).
Check (eq_refl true <<: valid_binary (Prim2EF nan) = true).
Check (eq_refl true <<: valid_binary (Prim2EF two) = true).
Check (eq_refl true <<: valid_binary (Prim2EF half) = true).
