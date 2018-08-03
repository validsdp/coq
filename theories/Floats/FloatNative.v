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
 * inside [0.5; 1.) then return its mantissa as a primitive integer.
 * The mantissa will be a 53-bit integer with its most significant bit set to 1.
 * Else return zero.
 * The sign bit is always ignored. *)
Register Primitive normfr_mantissa : float -> int as float64_normfr_mantissa.


(* Exponent manipulation functions *)
Definition shift := (2101)%int63. (* = 2*emax + prec *)
Register Primitive frshiftexp : float -> float * int as float64_frshiftexp.
Register Primitive ldshiftexp : float -> int -> float as float64_ldshiftexp.
