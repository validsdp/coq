Require Import ZArith Int63 Float.

Open Scope float_scope.

Definition f0 := zero.
Definition f1 := neg_zero.
Definition f2 := Eval compute in ldexp one 0.
Definition f3 := Eval compute in -f1.
(* smallest positive float *)
Definition f4 := Eval compute in ldexp one (-1074).
Definition f5 := Eval compute in -f3.
Definition f6 := infinity.
Definition f7 := neg_infinity.
Definition f8 := Eval compute in ldexp one (-1).
Definition f9 := Eval compute in -f8.
Definition f10 := Eval compute in of_int63 42.
Definition f11 := Eval compute in -f10.
(* max float *)
Definition f12 := Eval compute in ldexp (of_int63 9007199254740991) 1024.
Definition f13 := Eval compute in -f12.
(* smallest positive normalized float *)
Definition f14 := Eval compute in ldexp one (-1022).
Definition f15 := Eval compute in -f14.

Check (eq_refl : Prim2EF (next_up f0) = EF64succ (Prim2EF f0)).
Check (eq_refl : Prim2EF (next_down f0) = EF64pred (Prim2EF f0)).
Check (eq_refl : Prim2EF (next_up f1) = EF64succ (Prim2EF f1)).
Check (eq_refl : Prim2EF (next_down f1) = EF64pred (Prim2EF f1)).
Check (eq_refl : Prim2EF (next_up f2) = EF64succ (Prim2EF f2)).
Check (eq_refl : Prim2EF (next_down f2) = EF64pred (Prim2EF f2)).
Check (eq_refl : Prim2EF (next_up f3) = EF64succ (Prim2EF f3)).
Check (eq_refl : Prim2EF (next_down f3) = EF64pred (Prim2EF f3)).
Check (eq_refl : Prim2EF (next_up f4) = EF64succ (Prim2EF f4)).
Check (eq_refl : Prim2EF (next_down f4) = EF64pred (Prim2EF f4)).
Check (eq_refl : Prim2EF (next_up f5) = EF64succ (Prim2EF f5)).
Check (eq_refl : Prim2EF (next_down f5) = EF64pred (Prim2EF f5)).
Check (eq_refl : Prim2EF (next_up f6) = EF64succ (Prim2EF f6)).
Check (eq_refl : Prim2EF (next_down f6) = EF64pred (Prim2EF f6)).
Check (eq_refl : Prim2EF (next_up f7) = EF64succ (Prim2EF f7)).
Check (eq_refl : Prim2EF (next_down f7) = EF64pred (Prim2EF f7)).
Check (eq_refl : Prim2EF (next_up f8) = EF64succ (Prim2EF f8)).
Check (eq_refl : Prim2EF (next_down f8) = EF64pred (Prim2EF f8)).
Check (eq_refl : Prim2EF (next_up f9) = EF64succ (Prim2EF f9)).
Check (eq_refl : Prim2EF (next_down f9) = EF64pred (Prim2EF f9)).
Check (eq_refl : Prim2EF (next_up f10) = EF64succ (Prim2EF f10)).
Check (eq_refl : Prim2EF (next_down f10) = EF64pred (Prim2EF f10)).
Check (eq_refl : Prim2EF (next_up f11) = EF64succ (Prim2EF f11)).
Check (eq_refl : Prim2EF (next_down f11) = EF64pred (Prim2EF f11)).
Check (eq_refl : Prim2EF (next_up f12) = EF64succ (Prim2EF f12)).
Check (eq_refl : Prim2EF (next_down f12) = EF64pred (Prim2EF f12)).
Check (eq_refl : Prim2EF (next_up f13) = EF64succ (Prim2EF f13)).
Check (eq_refl : Prim2EF (next_down f13) = EF64pred (Prim2EF f13)).
Check (eq_refl : Prim2EF (next_up f14) = EF64succ (Prim2EF f14)).
Check (eq_refl : Prim2EF (next_down f14) = EF64pred (Prim2EF f14)).
Check (eq_refl : Prim2EF (next_up f15) = EF64succ (Prim2EF f15)).
Check (eq_refl : Prim2EF (next_down f15) = EF64pred (Prim2EF f15)).

Check (eq_refl (EF64succ (Prim2EF f0)) <: Prim2EF (next_up f0) = EF64succ (Prim2EF f0)).
Check (eq_refl (EF64pred (Prim2EF f0)) <: Prim2EF (next_down f0) = EF64pred (Prim2EF f0)).
Check (eq_refl (EF64succ (Prim2EF f1)) <: Prim2EF (next_up f1) = EF64succ (Prim2EF f1)).
Check (eq_refl (EF64pred (Prim2EF f1)) <: Prim2EF (next_down f1) = EF64pred (Prim2EF f1)).
Check (eq_refl (EF64succ (Prim2EF f2)) <: Prim2EF (next_up f2) = EF64succ (Prim2EF f2)).
Check (eq_refl (EF64pred (Prim2EF f2)) <: Prim2EF (next_down f2) = EF64pred (Prim2EF f2)).
Check (eq_refl (EF64succ (Prim2EF f3)) <: Prim2EF (next_up f3) = EF64succ (Prim2EF f3)).
Check (eq_refl (EF64pred (Prim2EF f3)) <: Prim2EF (next_down f3) = EF64pred (Prim2EF f3)).
Check (eq_refl (EF64succ (Prim2EF f4)) <: Prim2EF (next_up f4) = EF64succ (Prim2EF f4)).
Check (eq_refl (EF64pred (Prim2EF f4)) <: Prim2EF (next_down f4) = EF64pred (Prim2EF f4)).
Check (eq_refl (EF64succ (Prim2EF f5)) <: Prim2EF (next_up f5) = EF64succ (Prim2EF f5)).
Check (eq_refl (EF64pred (Prim2EF f5)) <: Prim2EF (next_down f5) = EF64pred (Prim2EF f5)).
Check (eq_refl (EF64succ (Prim2EF f6)) <: Prim2EF (next_up f6) = EF64succ (Prim2EF f6)).
Check (eq_refl (EF64pred (Prim2EF f6)) <: Prim2EF (next_down f6) = EF64pred (Prim2EF f6)).
Check (eq_refl (EF64succ (Prim2EF f7)) <: Prim2EF (next_up f7) = EF64succ (Prim2EF f7)).
Check (eq_refl (EF64pred (Prim2EF f7)) <: Prim2EF (next_down f7) = EF64pred (Prim2EF f7)).
Check (eq_refl (EF64succ (Prim2EF f8)) <: Prim2EF (next_up f8) = EF64succ (Prim2EF f8)).
Check (eq_refl (EF64pred (Prim2EF f8)) <: Prim2EF (next_down f8) = EF64pred (Prim2EF f8)).
Check (eq_refl (EF64succ (Prim2EF f9)) <: Prim2EF (next_up f9) = EF64succ (Prim2EF f9)).
Check (eq_refl (EF64pred (Prim2EF f9)) <: Prim2EF (next_down f9) = EF64pred (Prim2EF f9)).
Check (eq_refl (EF64succ (Prim2EF f10)) <: Prim2EF (next_up f10) = EF64succ (Prim2EF f10)).
Check (eq_refl (EF64pred (Prim2EF f10)) <: Prim2EF (next_down f10) = EF64pred (Prim2EF f10)).
Check (eq_refl (EF64succ (Prim2EF f11)) <: Prim2EF (next_up f11) = EF64succ (Prim2EF f11)).
Check (eq_refl (EF64pred (Prim2EF f11)) <: Prim2EF (next_down f11) = EF64pred (Prim2EF f11)).
Check (eq_refl (EF64succ (Prim2EF f12)) <: Prim2EF (next_up f12) = EF64succ (Prim2EF f12)).
Check (eq_refl (EF64pred (Prim2EF f12)) <: Prim2EF (next_down f12) = EF64pred (Prim2EF f12)).
Check (eq_refl (EF64succ (Prim2EF f13)) <: Prim2EF (next_up f13) = EF64succ (Prim2EF f13)).
Check (eq_refl (EF64pred (Prim2EF f13)) <: Prim2EF (next_down f13) = EF64pred (Prim2EF f13)).
Check (eq_refl (EF64succ (Prim2EF f14)) <: Prim2EF (next_up f14) = EF64succ (Prim2EF f14)).
Check (eq_refl (EF64pred (Prim2EF f14)) <: Prim2EF (next_down f14) = EF64pred (Prim2EF f14)).
Check (eq_refl (EF64succ (Prim2EF f15)) <: Prim2EF (next_up f15) = EF64succ (Prim2EF f15)).
Check (eq_refl (EF64pred (Prim2EF f15)) <: Prim2EF (next_down f15) = EF64pred (Prim2EF f15)).
