(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  | Int63head0
  | Int63tail0
  | Int63add
  | Int63sub
  | Int63mul
  | Int63div
  | Int63mod
  | Int63lsr
  | Int63lsl
  | Int63land
  | Int63lor
  | Int63lxor
  | Int63addc
  | Int63subc
  | Int63addCarryC
  | Int63subCarryC
  | Int63mulc
  | Int63diveucl
  | Int63div21
  | Int63addMulDiv
  | Int63eq
  | Int63lt
  | Int63le
  | Int63compare
  | Float64opp
  | Float64abs
  | Float64compare
  | Float64add
  | Float64sub
  | Float64mul
  | Float64div
  | Float64sqrt
  | Float64ofInt63
  | Float64toInt63
  | Float64frshiftexp
  | Float64ldshiftexp

let equal (p1 : t) (p2 : t) =
  p1 == p2

let hash = function
  | Int63head0 -> 1
  | Int63tail0 -> 2
  | Int63add -> 3
  | Int63sub -> 4
  | Int63mul -> 5
  | Int63div -> 6
  | Int63mod -> 7
  | Int63lsr -> 8
  | Int63lsl -> 9
  | Int63land -> 10
  | Int63lor -> 11
  | Int63lxor -> 12
  | Int63addc -> 13
  | Int63subc -> 14
  | Int63addCarryC -> 15
  | Int63subCarryC -> 16
  | Int63mulc -> 17
  | Int63diveucl -> 18
  | Int63div21 -> 19
  | Int63addMulDiv -> 20
  | Int63eq -> 21
  | Int63lt -> 22
  | Int63le -> 23
  | Int63compare -> 24
  | Float64opp -> 25
  | Float64abs -> 26
  | Float64compare -> 27
  | Float64add -> 28
  | Float64sub -> 29
  | Float64mul -> 30
  | Float64div -> 31
  | Float64sqrt -> 32
  | Float64ofInt63 -> 33
  | Float64toInt63 -> 34
  | Float64frshiftexp -> 35
  | Float64ldshiftexp -> 36

(* Should match names in nativevalues.ml *)
let to_string = function
  | Int63head0 -> "head0"
  | Int63tail0 -> "tail0"
  | Int63add -> "add"
  | Int63sub -> "sub"
  | Int63mul -> "mul"
  | Int63div -> "div"
  | Int63mod -> "rem"
  | Int63lsr -> "l_sr"
  | Int63lsl -> "l_sl"
  | Int63land -> "l_and"
  | Int63lor -> "l_or"
  | Int63lxor -> "l_xor"
  | Int63addc -> "addc"
  | Int63subc -> "subc"
  | Int63addCarryC -> "addCarryC"
  | Int63subCarryC -> "subCarryC"
  | Int63mulc -> "mulc"
  | Int63diveucl -> "diveucl"
  | Int63div21 -> "div21"
  | Int63addMulDiv -> "addMulDiv"
  | Int63eq -> "eq"
  | Int63lt -> "lt"
  | Int63le -> "le"
  | Int63compare -> "compare"
  | Float64opp -> "fopp"
  | Float64abs -> "fabs"
  | Float64compare -> "fcompare"
  | Float64add -> "fadd"
  | Float64sub -> "fsub"
  | Float64mul -> "fmul"
  | Float64div -> "fdiv"
  | Float64sqrt -> "fsqrt"
  | Float64ofInt63 -> "float_of_int"
  | Float64toInt63 -> "float_to_int"
  | Float64frshiftexp -> "frshiftexp"
  | Float64ldshiftexp -> "ldshiftexp"

type arg_kind =
  | Kparam (* not needed for the evaluation of the primitive when it reduces *)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf. example: [v] in [Array.set t i v] *)

type args_red = arg_kind list

(* Invariant only argument of type int63, float, or an inductive can
   have kind Kwhnf *)

let kind = function
  | Int63head0 | Int63tail0 -> [Kwhnf]

  | Int63add | Int63sub | Int63mul
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor
  | Int63addc | Int63subc
  | Int63addCarryC | Int63subCarryC  | Int63mulc | Int63diveucl
  | Int63eq | Int63lt | Int63le | Int63compare -> [Kwhnf; Kwhnf]

  | Int63div21 | Int63addMulDiv -> [Kwhnf; Kwhnf; Kwhnf]

  | Float64opp | Float64abs | Float64sqrt | Float64ofInt63 | Float64toInt63
  | Float64frshiftexp -> [Kwhnf]

  | Float64compare | Float64add | Float64sub | Float64mul
  | Float64div | Float64ldshiftexp -> [Kwhnf;Kwhnf]

let arity = function
  | Int63head0 | Int63tail0 -> 1
  | Int63add | Int63sub | Int63mul
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor
  | Int63addc | Int63subc
  | Int63addCarryC | Int63subCarryC | Int63mulc | Int63diveucl
  | Int63eq | Int63lt | Int63le
  | Int63compare -> 2

  | Int63div21 | Int63addMulDiv -> 3
  | Float64opp | Float64abs | Float64sqrt
  | Float64ofInt63 | Float64toInt63
  | Float64frshiftexp -> 1

  | Float64compare | Float64add | Float64sub | Float64mul
  | Float64div | Float64ldshiftexp -> 2

(** Special Entries for Register **)

type prim_ind =
  | PIT_bool
  | PIT_carry
  | PIT_pair
  | PIT_cmp
  | PIT_option

type prim_type =
  | PT_int63
  | PT_float64

type op_or_type =
  | OT_op of t
  | OT_type of prim_type

let prim_ind_to_string = function
  | PIT_bool -> "bool"
  | PIT_carry -> "carry"
  | PIT_pair -> "pair"
  | PIT_cmp -> "cmp"
  | PIT_option -> "option"

let prim_type_to_string = function
  | PT_int63 -> "int63_type"
  | PT_float64 -> "float64_type"

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t
