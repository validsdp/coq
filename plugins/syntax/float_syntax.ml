(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Glob_term

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "float_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(*** Constants for locating float constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

(*** Parsing for float in digital notation ***)

let interp_float ?loc (sign,n) =
  let sign = Constrexpr.(match sign with SPlus -> "" | SMinus -> "-") in
  DAst.make ?loc (GFloat (Float64.of_string (sign ^ NumTok.to_string n)))

(* Pretty prints a float *)

let uninterp_float (AnyGlobConstr i) = None
  (* match DAst.get i with
   * (\* FIXME: first version commented-out for now, to be removed:
   *  | Gfloat f ->
   *    match Float64.classify f with
   *    | NaN | PInf | NInf ->
   *      None (\* cannot produce a raw-numeral *\) *\)
   * | GFloat f when Float64.(is_nan f || is_infinity f || is_neg_infinity f) ->
   *    None (\* cannot produce a raw-numeral *\)
   * | GFloat f ->
   *    (\* same code as in constrextern.ml; could this be factored-out? *\)
   *    let s = Float64.to_string f in
   *    let len = String.length s in
   *    let () = assert (len > 0) in
   *    if s.[0] = '-' then Some (Util.SMinus, String.sub s 1 (len - 1))
   *    else Some (Util.SPlus, s)
   * | _ -> None *)

(* Actually declares the interpreter for float *)

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

(* float stuff *)
let float_module = ["Coq"; "Floats"; "FloatNative"]
let float_path = make_path float_module "float"
let float_scope = "float_scope"

let _ =
  register_rawnumeral_interpretation float_scope (interp_float,uninterp_float);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = float_scope;
      pt_interp_info = Uid float_scope;
      pt_required = (float_path,float_module);
      pt_refs = [];
      pt_in_match = false }
