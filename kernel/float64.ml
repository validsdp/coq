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

(* Compiles a float to OCaml code *)
let compile f =
  (* TODO: use OCaml printf %.17F
     once Coq version requirement for OCaml meets >= 4.09 *)
  let s = match classify_float f with
    | FP_normal | FP_subnormal | FP_zero ->
       let s = Printf.sprintf "%.17g" f in
       let len = String.length s in
       let rec ml i =
         i < len && (s.[i] = '.' || s.[i] = 'e' || s.[i] = 'E' || ml (i + 1)) in
       if ml 0 then s else s ^ "."
    | FP_infinite -> if 0. <= f then "infinity" else "neg_infinity"
    | FP_nan -> "nan" in
  "Float64.of_float (" ^ s ^ ")"

let of_float f = f

let opp = ( ~-. )
let abs = abs_float

type float_comparison = FEq | FLt | FGt | FNotComparable

let compare x y =
  if x < y then FLt
  else
  (
    if x > y then FGt
    else
    (
      if x = y then FEq
      else FNotComparable (* NaN case *)
    )
  )

type float_class =
  | PNormal | NNormal | PSubn | NSubn | PZero | NZero | PInf | NInf | NaN

let classify x =
  match classify_float x with
  | FP_normal -> if 0. < x then PNormal else NNormal
  | FP_subnormal -> if 0. < x then PSubn else NSubn
  | FP_zero -> if 0. < 1. /. x then PZero else NZero
  | FP_infinite -> if 0. < x then PInf else NInf
  | FP_nan -> NaN

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

let eta_float = ldexp 1. (-1074) (* smallest positive float (subnormal) *)

let next_up f =
  match classify_float f with
  | FP_nan -> f
  | FP_infinite -> if 0. < f then f else -.max_float
  | FP_zero | FP_subnormal ->
     let f = f +. eta_float in
     if f = 0. then -0. else f (* or next_down may return -0. *)
  | FP_normal ->
     let f, e = frexp f in
     if 0. < f || f <> -0.5 || e = -1021 then
       ldexp (f +. epsilon_float /. 2.) e
     else
       ldexp (-0.5 +. epsilon_float /. 4.) e

let next_down f = -.(next_up (-.f))

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
