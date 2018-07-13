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
let to_int63 = Uint63.of_float

let eshift = 1022 + 52 (* minimum negative exponent + precision *)

let frshiftexp f =
  let (m, e) = frexp f in
  (m, Uint63.of_int (e + eshift))

let ldshiftexp f e = ldexp f (snd (Uint63.to_int2 e) - eshift)

(* FIXME: Sign of 0 is ignored for equal, hash and total_compare *)

let equal f1 f2 = (f1 = f2) || (is_nan f1 && is_nan f2)

let hash f =
  let f = if is_nan f then nan else f in (* Consider all NaNs are equal *)
  Hashtbl.hash f (* TODO: Consider hashing in a more predictable way *)

let total_compare = Pervasives.compare
