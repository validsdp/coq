Require Import ZArith Float.

Definition denorm := Eval compute in ldexp one (-1074)%Z.
Definition neg_one := Eval compute in (-one)%float.

Check (eq_refl : let (m,e) := frexp infinity in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF infinity)).
Check (eq_refl (EFfrexp prec emax (Prim2EF infinity)) <: let (m,e) := frexp infinity in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF infinity)).
Check (eq_refl (EFfrexp prec emax (Prim2EF infinity)) <<: let (m,e) := frexp infinity in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF infinity)).

Check (eq_refl : let (m,e) := frexp nan in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF nan)).
Check (eq_refl (EFfrexp prec emax (Prim2EF nan)) <: let (m,e) := frexp nan in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF nan)).
Check (eq_refl (EFfrexp prec emax (Prim2EF nan)) <<: let (m,e) := frexp nan in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF nan)).

Check (eq_refl : let (m,e) := frexp zero in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF zero)).
Check (eq_refl (EFfrexp prec emax (Prim2EF zero)) <: let (m,e) := frexp zero in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF zero)).
Check (eq_refl (EFfrexp prec emax (Prim2EF zero)) <<: let (m,e) := frexp zero in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF zero)).

Check (eq_refl : let (m,e) := frexp one in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF one)).
Check (eq_refl (EFfrexp prec emax (Prim2EF one)) <: let (m,e) := frexp one in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF one)).
Check (eq_refl (EFfrexp prec emax (Prim2EF one)) <<: let (m,e) := frexp one in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF one)).

Check (eq_refl : let (m,e) := frexp neg_one in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF neg_one)).
Check (eq_refl (EFfrexp prec emax (Prim2EF neg_one)) <: let (m,e) := frexp neg_one in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF neg_one)).
Check (eq_refl (EFfrexp prec emax (Prim2EF neg_one)) <<: let (m,e) := frexp neg_one in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF neg_one)).

Check (eq_refl : let (m,e) := frexp denorm in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF denorm)).
Check (eq_refl (EFfrexp prec emax (Prim2EF denorm)) <: let (m,e) := frexp denorm in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF denorm)).
Check (eq_refl (EFfrexp prec emax (Prim2EF denorm)) <<: let (m,e) := frexp denorm in (Prim2EF m, e) = EFfrexp prec emax (Prim2EF denorm)).
