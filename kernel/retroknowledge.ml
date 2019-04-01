(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Arnaud Spiwack, May 2007 *)
(* Addition of native Head (nb of heading 0) and Tail (nb of trailing 0) by
   Benjamin Grégoire, Jun 2007 *)

(* This file defines the knowledge that the kernel is able to optimize. *)

open Names

type retroknowledge = {
    retro_int63 : Constant.t option;
    retro_float64 : Constant.t option;
    retro_bool : (constructor * constructor) option; (* true, false *)
    retro_carry : (constructor * constructor) option; (* C0, C1 *)
    retro_pair : constructor option;
    retro_cmp : (constructor * constructor * constructor) option;
                    (* Eq, Lt, Gt *)
    retro_f_cmp : (constructor * constructor * constructor * constructor)
                  option;
                  (* FEq, FLt, FGt, FNotComparable *)
    retro_refl : constructor option;
}

let empty = {
    retro_int63 = None;
    retro_float64 = None;
    retro_bool = None;
    retro_carry = None;
    retro_pair = None;
    retro_cmp = None;
    retro_f_cmp = None;
    retro_refl = None;
}

type action =
  | Register_ind of CPrimitives.prim_ind * inductive
  | Register_type of CPrimitives.prim_type * Constant.t
