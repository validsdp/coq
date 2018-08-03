Require Import ZArith Int63 EmulatedFloat FloatNative FloatOps.

Notation valid_binary := (valid_binary prec emax).

Definition EF64mult := EFmult prec emax.
Definition EF64plus := EFplus prec emax.
Definition EF64minus := EFminus prec emax.
Definition EF64div := EFdiv prec emax.
Definition EF64sqrt := EFsqrt prec emax.

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

Axiom of_int63_spec : forall n, Prim2EF (of_int63 n) = binary_normalize prec emax (to_Z n) 0%Z false.
Axiom normfr_mantissa_spec : forall f, to_Z (normfr_mantissa f) = Z.of_N (EFnormfr_mantissa prec (Prim2EF f)).

Axiom frshiftexp_spec : forall f, let (m,e) := frshiftexp f in (Prim2EF m, ((to_Z e) - (to_Z shift))%Z) = EFfrexp prec emax (Prim2EF f).
Axiom ldshiftexp_spec : forall f e, Prim2EF (ldshiftexp f e) = EFldexp prec emax (Prim2EF f) ((to_Z e) - (to_Z shift)).
