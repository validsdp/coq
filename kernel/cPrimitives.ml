(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type operation =
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
  | Int63eqb_correct

type iterator =
  | Int63foldi
  | Int63foldi_down

type t =
  | Operation of operation
  | Iterator of iterator

let equal (p1 : t) (p2 : t) =
  p1 == p2

let hash_operation = function
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
  | Int63eqb_correct -> 25

let hash_iterator = function
  | Int63foldi -> 1
  | Int63foldi_down -> 2

open Hashset.Combine

let hash = function
  | Operation op -> combinesmall 1 (hash_operation op)
  | Iterator it -> combinesmall 2 (hash_iterator it)

(* Should match names in nativevalues.ml *)
let operation_to_string = function
  | Int63head0     -> "head0"
  | Int63tail0     -> "tail0"
  | Int63add       -> "add"
  | Int63sub       -> "sub"
  | Int63mul       -> "mul"
  | Int63div       -> "div"
  | Int63mod       -> "rem"
  | Int63lsr       -> "l_sr"
  | Int63lsl       -> "l_sl"
  | Int63land      -> "l_and"
  | Int63lor       -> "l_or"
  | Int63lxor      -> "l_xor"
  | Int63addc      -> "addc"
  | Int63subc      -> "subc"
  | Int63addCarryC -> "addCarryC"
  | Int63subCarryC -> "subCarryC"
  | Int63mulc      -> "mulc"
  | Int63diveucl   -> "diveucl"
  | Int63div21     -> "div21"
  | Int63addMulDiv -> "addMulDiv"
  | Int63eq        -> "eq"
  | Int63lt        -> "lt"
  | Int63le        -> "le"
  | Int63compare   -> "compare"
  | Int63eqb_correct -> "eqb_correct"

let iterator_to_string = function
  | Int63foldi    -> "foldi"
  | Int63foldi_down -> "foldi_down"

let to_string = function
  | Operation op -> operation_to_string op
  | Iterator it -> iterator_to_string it

type arg_kind =
  | Kparam (* not needed for the evaluation of the primitive when it reduces *)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf. example: [v] in [Array.set t i v] *)

type args_red = arg_kind list

(* Invariant only argument of type int63, array or an inductive can
   have kind Kwhnf *)

let iterator_kind = [Kparam;Kparam;Karg;Kwhnf;Kwhnf;Karg]

let operation_kind = function
  | Int63head0 | Int63tail0 -> [Kwhnf]

  | Int63add | Int63sub | Int63mul
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor
  | Int63addc | Int63subc
  | Int63addCarryC | Int63subCarryC  | Int63mulc | Int63diveucl
  | Int63eq | Int63lt | Int63le | Int63compare -> [Kwhnf; Kwhnf]

  | Int63div21 | Int63addMulDiv -> [Kwhnf; Kwhnf; Kwhnf]
  | Int63eqb_correct -> [Karg;Karg;Kwhnf]

let kind = function
  | Operation op -> operation_kind op
  | Iterator _ -> iterator_kind

let iterator_arity = (2, 4)

let operation_arity = function
  | Int63head0 | Int63tail0 -> (0,1)
  | Int63add | Int63sub | Int63mul
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor
  | Int63addc | Int63subc
  | Int63addCarryC | Int63subCarryC | Int63mulc | Int63diveucl
  | Int63eq | Int63lt | Int63le
  | Int63compare -> (0,2)

  | Int63div21 | Int63addMulDiv -> (0,3)
  | Int63eqb_correct -> (0,3)

let arity = function
  | Operation op -> operation_arity op
  | Iterator _ -> iterator_arity

(** Special Entries for Register **)

type prim_ind =
  | PIT_bool
  | PIT_carry
  | PIT_pair
  | PIT_cmp
  | PIT_eq

type prim_type =
  | PT_int63

type op_or_type =
  | OT_op of t
  | OT_type of prim_type

let prim_ind_to_string = function
  | PIT_bool -> "bool"
  | PIT_carry -> "carry"
  | PIT_pair -> "pair"
  | PIT_cmp -> "cmp"
  | PIT_eq -> "eq"

let prim_type_to_string = function
  | PT_int63 -> "int63"

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t
