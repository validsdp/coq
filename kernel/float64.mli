(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t

(** Test functions for special values to avoid calling [classify] *)
val is_nan : t -> bool
val is_infinity : t -> bool
val is_neg_infinity : t -> bool

val to_string : t -> string
val of_string : string -> t

val compile : t -> string

val of_float : float -> t

val opp : t -> t
val abs : t -> t

type float_comparison = FEq | FLt | FGt | FNotComparable

(** The IEEE 754 float comparison.
 * NotComparable is returned if there is a NaN in the arguments *)
val compare : t -> t -> float_comparison

type float_class =
  | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN

val classify : t -> float_class

val mul : t -> t -> t
val add : t -> t -> t
val sub : t -> t -> t
val div : t -> t -> t
val sqrt : t -> t

(** Link with integers *)
val of_int63 : Uint63.t -> t
val normfr_mantissa : t -> Uint63.t

(** Shifted exponent extraction *)
val eshift : int
val frshiftexp : t -> t * Uint63.t (* float remainder, shifted exponent *)
val ldshiftexp : t -> Uint63.t -> t

val next_up : t -> t
val next_down : t -> t

(** Return true if two floats are equal.
 * All NaN values are considered equal. *)
val equal : t -> t -> bool

val hash : t -> int

(** Total order relation over float values. Behaves like [Pervasives.compare].*)
val total_compare : t -> t -> int

val is_float64 : Obj.t -> bool
