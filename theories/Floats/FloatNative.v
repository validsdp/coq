Require Import Int63.

Inductive float_comparison : Set := FEq | FLt | FGt | FNotComparable.

Register float_comparison as kernel.ind_f_cmp.

Primitive float := #float64_type.

Declare Scope float_scope.
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

(* Convert a primitive integer into a float value.
 * The value is rounded if necessary. *)
Primitive of_int63 := #float64_of_int63.

(* If the input is a float value with an absolute value
 * inside [0.5; 1.) then return its mantissa as a primitive integer.
 * The mantissa will be a 53-bit integer with its most significant bit set to 1.
 * Else return zero.
 * The sign bit is always ignored. *)
Primitive normfr_mantissa := #float64_normfr_mantissa.

(* Exponent manipulation functions *)
Definition shift := (2101)%int63. (* = 2*emax + prec *)
Primitive frshiftexp := #float64_frshiftexp.
Primitive ldshiftexp := #float64_ldshiftexp.
