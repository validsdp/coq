Require Import Int63.

Register Inductive option as ind_option.

Register Primitive float : Set as float64_type.

Delimit Scope float_scope with float.
Bind Scope float_scope with float.

Register Primitive opp : float -> float as float64_opp.
Notation "- x" := (opp x) : float_scope.

Register Primitive abs : float -> float as float64_abs.

Register Primitive compare : float -> float -> option comparison as float64_compare.
Notation "x ?= y" := (compare x y) (at level 70, no associativity) : float_scope.

Register Primitive mul : float -> float -> float as float64_mul.
Notation "x * y" := (mul x y) : float_scope.

Register Primitive add : float -> float -> float as float64_add.
Notation "x + y" := (add x y) : float_scope.
Register Primitive sub : float -> float -> float as float64_sub.
Notation "x - y" := (sub x y) : float_scope.

Register Primitive div : float -> float -> float as float64_div.
Notation "x / y" := (div x y) : float_scope.

Register Primitive sqrt : float -> float as float64_sqrt.


(* Convert a primitive integer into a float value.
 * The value is rounded if necessary. *)
Register Primitive of_int63 : int -> float as float64_of_int63.

(* If the input is a float value with an absolute value
 * inside ]1.;0.5] then return its mantissa as a primitive integer.
 * The mantissa will be a 53-bit integer with its most significant bit set to 1.
 * Else return zero.
 * The sign bit is always ignored. *)
Register Primitive normfr_mantissa : float -> int as float64_normfr_mantissa.


(* Exponent manipulation functions *)
Definition shift := (1022 + 52)%int63.
Register Primitive frshiftexp : float -> float * int as float64_frshiftexp.
Register Primitive ldshiftexp : float -> int -> float as float64_ldshiftexp.

Definition frexp f :=
  let (m, se) := frshiftexp f in
  (m, ([| se |] - [| shift |])%Z%int63).

Definition ldexp f e := ldshiftexp f (of_Z e + shift).


Local Open Scope float_scope.

(* Special values *)
Definition zero := Eval compute in (of_int63 0).
Definition neg_zero := Eval compute in (-zero).
Definition one := Eval compute in (of_int63 1).
Definition infinity := Eval compute in (one / zero).
Definition neg_infinity := Eval compute in (-infinity).
Definition nan := Eval compute in (zero / zero).

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
