Require Import Int63.

Register Inductive option as ind_option.

Primitive float := #float64_type.

Delimit Scope float_scope with float.
Bind Scope float_scope with float.

Primitive opp := #float64_opp.
Notation "- x" := (opp x) : float_scope.

Primitive abs := #float64_abs.

Primitive compare := #float64_compare.
Notation "x ?= y" := (compare x y) (at level 70, no associativity) : float_scope.

Primitive mul := #float64_mul.
Notation "x * y" := (mul x y) : float_scope.

Primitive add := #float64_add.
Notation "x + y" := (add x y) : float_scope.
Primitive sub := #float64_sub.
Notation "x - y" := (sub x y) : float_scope.

Primitive div := #float64_div.
Notation "x / y" := (div x y) : float_scope.

Primitive sqrt := #float64_sqrt.

(* Conversion from/to int63 *)
Primitive of_int63 := #float64_of_int63.
Primitive to_int63 := #float64_to_int63.

Local Open Scope float_scope.

(* Special values *)
Definition zero := Eval compute in (of_int63 0).
Definition neg_zero := Eval compute in (-zero).
Definition one := Eval compute in (of_int63 1).
Definition infinity := Eval compute in (one / zero).
Definition neg_infinity := Eval compute in (-infinity).
Definition nan := Eval compute in (zero / zero).
Definition two := Eval compute in one + one.
Definition half := Eval compute in one / two.

Definition is_nan f :=
  match f ?= f with
  | None => true
  | _ => false
  end.

Definition is_zero f :=
  match f ?= zero with
  | Some Eq => true (* note: 0 == -0 with floats *)
  | _ => false
  end.

Definition is_infinity f :=
  match f ?= infinity with
  | Some Eq => true
  | Some Lt => match f ?= neg_infinity with
              | Some Eq => true
              | _ => false
              end
  | _ => false
  end.

Definition get_sign f := (* + => false, - => true *)
  let f := if is_zero f then one / f else f in
  match f ?= zero with
  | Some Gt => false
  | _ => true
  end.

Definition prec_bin := 52%int63.
Definition shift := (1022 + prec_bin)%int63.
Primitive frshiftexp := #float64_frshiftexp.
Primitive ldshiftexp := #float64_ldshiftexp.

(*Axiom frshiftexp_spec : forall f, is_nan f = false -> is_zero f = false -> is_infinity f = false -> let (m, se) := frshiftexp f in (f ?= half = Some Gt \/ f ?= half = Some Eq) /\ f ?= one = Some Lt /\ ldshiftexp m se = f *)
