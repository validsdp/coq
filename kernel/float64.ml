(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* OCaml's float type follows the IEEE 754 Binary 64 (double precision)
 * format *)
type t = float

let is_nan f = f <> f

(* OCaml give a sign to nan values which should not be displayed as all nan are
 * considered equal *)
let to_string f = if is_nan f then "nan" else string_of_float f
let of_string = float_of_string

let of_float f = f

let opp = ( ~-. )
let abs = abs_float

type float_comparison = Eq | Lt | Gt | NotComparable

let compare x y =
  if x = y then Eq
  else
  (
    if x < y then Lt
    else
    (
      if x > y then Gt
      else NotComparable (* NaN case *)
    )
  )

let mul = ( *. )
let add = ( +. )
let sub = ( -. )
let div = ( /. )
let sqrt = Pervasives.sqrt

let of_int63 = Uint63.to_float

let prec = 53
let normfr_mantissa f =
  let f = abs f in
  if f >= 0.5 && f < 1. then Uint63.of_float (ldexp f prec)
  else Uint63.zero

let eshift = 2101 (* 2*emax + prec *)

let frshiftexp f =
  match classify_float f with
  | FP_zero | FP_infinite | FP_nan -> (f, Uint63.zero)
  | FP_normal | FP_subnormal ->
  let (m, e) = frexp f in
  (m, Uint63.of_int (e + eshift))

let ldshiftexp f e = ldexp f (snd (Uint63.to_int2 e) - eshift)

let equal f1 f2 =
  match classify_float f1 with
  | FP_normal | FP_subnormal | FP_infinite -> (f1 = f2)
  | FP_nan -> is_nan f2
  | FP_zero -> f1 = f2 && 1. /. f1 = 1. /. f2 (* OCaml consider 0. = -0. *)

let hash f =
  let f = if is_nan f then nan else f in (* Consider all NaNs are equal *)
  Hashtbl.hash f

let total_compare f1 f2 =
  if f1 = 0. && f2 = 0. then Pervasives.compare (1. /. f1) (1. /. f2)
  else Pervasives.compare f1 f2
