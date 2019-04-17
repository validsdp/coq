(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type retroknowledge = {
    retro_int63 : Constant.t option;
    retro_float64 : Constant.t option;
    retro_bool : (constructor * constructor) option; (* true, false *)
    retro_carry : (constructor * constructor) option; (* C0, C1 *)
    retro_pair : constructor option;
    retro_cmp : (constructor * constructor * constructor) option;
                    (* Eq, Lt, Gt *)
    retro_option : (constructor * constructor) option; (* Some, None *)
    retro_refl : constructor option;
}

val empty : retroknowledge

type action =
  | Register_ind : 'a CPrimitives.prim_ind * inductive -> action
  | Register_type : CPrimitives.prim_type * Constant.t -> action
