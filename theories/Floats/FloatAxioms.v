Require Import ZArith Int63 SpecFloat FloatNative FloatOps.

Notation valid_binary := (valid_binary prec emax).

Definition SF64classify := SFclassify prec.
Definition SF64mult := SFmult prec emax.
Definition SF64plus := SFplus prec emax.
Definition SF64minus := SFminus prec emax.
Definition SF64div := SFdiv prec emax.
Definition SF64sqrt := SFsqrt prec emax.

Axiom Prim2SF_valid : forall x, valid_binary (Prim2SF x) = true.
Axiom SF2Prim_Prim2SF : forall x, SF2Prim (Prim2SF x) = x.
Axiom Prim2SF_SF2Prim : forall x, valid_binary x = true -> Prim2SF (SF2Prim x) = x.

Theorem Prim2SF_inj : forall x y, Prim2SF x = Prim2SF y -> x = y.
  intros. rewrite <- SF2Prim_Prim2SF. symmetry. rewrite <- SF2Prim_Prim2SF. now rewrite H.
Qed.

Theorem SF2Prim_inj : forall x y, SF2Prim x = SF2Prim y -> valid_binary x = true -> valid_binary y = true -> x = y.
  intros. rewrite <- Prim2SF_SF2Prim by assumption. symmetry. rewrite <- Prim2SF_SF2Prim by assumption. rewrite H. reflexivity.
Qed.

Axiom opp_SFopp : forall x, Prim2SF (-x)%float = SFopp (Prim2SF x).
Axiom abs_SFabs : forall x, Prim2SF (abs x) = SFabs (Prim2SF x).
Definition flatten_cmp_opt c :=
  match c with
  | None => FNotComparable
  | Some Eq => FEq
  | Some Lt => FLt
  | Some Gt => FGt
  end.
Axiom compare_SFcompare : forall x y, (x ?= y)%float = flatten_cmp_opt (SFcompare (Prim2SF x) (Prim2SF y)).
Axiom classify_SFclassify : forall x, classify x = SF64classify (Prim2SF x).
Axiom mult_SFmult : forall x y, Prim2SF (x * y)%float = SF64mult (Prim2SF x) (Prim2SF y).
Axiom plus_SFplus : forall x y, Prim2SF (x + y)%float = SF64plus (Prim2SF x) (Prim2SF y).
Axiom minus_SFminus : forall x y, Prim2SF (x - y)%float = SF64minus (Prim2SF x) (Prim2SF y).
Axiom div_SFdiv : forall x y, Prim2SF (x / y)%float = SF64div (Prim2SF x) (Prim2SF y).
Axiom sqrt_SFsqrt : forall x, Prim2SF (sqrt x) = SF64sqrt (Prim2SF x).

Axiom of_int63_spec : forall n, Prim2SF (of_int63 n) = binary_normalize prec emax (to_Z n) 0%Z false.
Axiom normfr_mantissa_SFnormfr_mantissa : forall f, to_Z (normfr_mantissa f) = Z.of_N (SFnormfr_mantissa prec (Prim2SF f)).

Axiom frshiftexp_SFfrexp : forall f, let (m,e) := frshiftexp f in (Prim2SF m, ((to_Z e) - (to_Z shift))%Z) = SFfrexp prec emax (Prim2SF f).
Axiom ldshiftexp_SFldexp : forall f e, Prim2SF (ldshiftexp f e) = SFldexp prec emax (Prim2SF f) ((to_Z e) - (to_Z shift)).
