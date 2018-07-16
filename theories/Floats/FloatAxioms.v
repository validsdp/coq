Require Import ZArith Int63 EmulatedFloat FloatNative.

(* Properties of the Binary64 IEEE 754 format *)
Definition prec := 53%Z.
Definition emax := 1024%Z.

Notation valid_binary := (valid_binary prec emax).

Definition EF64mult := EFmult prec emax.
Definition EF64plus := EFplus prec emax.
Definition EF64minus := EFminus prec emax.
Definition EF64div := EFdiv prec emax.
Definition EF64sqrt := EFsqrt prec emax.

Definition Prim2EF f :=
  if is_nan f then E754_nan
  else if is_zero f then E754_zero (get_sign f)
       else if is_infinity f then E754_infinity (get_sign f)
            else
              let (r, exp) := frexp f in
              let m := ldexp r prec in
              let e := (exp - prec)%Z in
              match [| to_int63 m |]%int63 with
              | Zpos p => E754_finite false p e
              | Zneg p => E754_finite true p e
              | Z0 => E754_zero false
              end.

Definition EF2Prim ef :=
  match ef with
  | E754_nan => nan
  | E754_zero false => zero
  | E754_zero true => neg_zero
  | E754_infinity false => infinity
  | E754_infinity true => neg_infinity
  | E754_finite s m e =>
    let pm := of_int63 (of_Z (Zpos m)) in
    let f := ldexp pm e in
    if s then (-f)%float else f
  end.

Axiom Prim2EF_valid : forall x, valid_binary (Prim2EF x) = true.
Axiom EF2Prim_Prim2EF : forall x, EF2Prim (Prim2EF x) = x.
Axiom Prim2EF_EF2Prim : forall x, valid_binary x = true -> Prim2EF (EF2Prim x) = x.

Theorem Prim2EF_inj : forall x y, Prim2EF x = Prim2EF y -> x = y.
  intros. rewrite <- EF2Prim_Prim2EF. symmetry. rewrite <- EF2Prim_Prim2EF. now rewrite H.
Qed.

Theorem EF2Prim_inj : forall x y, EF2Prim x = EF2Prim y -> valid_binary x = true -> valid_binary y = true -> x = y.
  intros. rewrite <- Prim2EF_EF2Prim by assumption. symmetry. rewrite <- Prim2EF_EF2Prim by assumption. rewrite H. reflexivity.
Qed.


Axiom FPopp_EFopp : forall x, Prim2EF (-x)%float = EFopp (Prim2EF x).
Axiom FPabs_EFabs : forall x, Prim2EF (abs x) = EFabs (Prim2EF x).
Axiom FPcompare_EFcompare : forall x y, (x ?= y)%float = EFcompare (Prim2EF x) (Prim2EF y).
Axiom FPmult_EFmult : forall x y, Prim2EF (x * y)%float = EF64mult (Prim2EF x) (Prim2EF y).
Axiom FPplus_EFplus : forall x y, Prim2EF (x + y)%float = EF64plus (Prim2EF x) (Prim2EF y).
Axiom FPminus_EFminus : forall x y, Prim2EF (x - y)%float = EF64minus (Prim2EF x) (Prim2EF y).
Axiom FPdiv_EFdiv : forall x y, Prim2EF (x / y)%float = EF64div (Prim2EF x) (Prim2EF y).
Axiom FPsqrt_EFsqrt : forall x, Prim2EF (sqrt x) = EF64sqrt (Prim2EF x).
