(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Author: Jean-Christophe Filliâtre as part of the rebuilding of Coq
   around a purely functional abstract type-checker, Aug 1999 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Flag for predicativity of Set by Hugo Herbelin in Oct 2003 *)
(* Support for virtual machine by Benjamin Grégoire in Oct 2004 *)
(* Support for retroknowledge by Arnaud Spiwack in May 2007 *)
(* Support for assumption dependencies by Arnaud Spiwack in May 2007 *)

(* Miscellaneous maintenance by Bruno Barras, Hugo Herbelin, Jean-Marc
   Notin, Matthieu Sozeau *)

(* This file defines the type of environments on which the
   type-checker works, together with simple related functions *)

open CErrors
open Util
open Names
open Constr
open Vars
open Declarations
open Pre_env
open Context.Rel.Declaration

(* The type of environments. *)

type named_context_val = Pre_env.named_context_val

type env = Pre_env.env

let pre_env env = env
let env_of_pre_env env = env
let oracle env = env.env_typing_flags.conv_oracle
let set_oracle env o =
  let env_typing_flags = { env.env_typing_flags with conv_oracle = o } in
  { env with env_typing_flags }

let empty_named_context_val = empty_named_context_val

let empty_env = empty_env

let engagement env = env.env_stratification.env_engagement
let typing_flags env = env.env_typing_flags

let is_impredicative_set env = 
  match engagement env with
  | ImpredicativeSet -> true
  | _ -> false

let type_in_type env = not (typing_flags env).check_universes
let deactivated_guard env = not (typing_flags env).check_guarded

let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context.env_named_ctx
let named_context_val env = env.env_named_context
let rel_context env = env.env_rel_context.env_rel_ctx
let opaque_tables env = env.indirect_pterms
let set_opaque_tables env indirect_pterms = { env with indirect_pterms }

let empty_context env =
  match env.env_rel_context.env_rel_ctx, env.env_named_context.env_named_ctx with
  | [], [] -> true
  | _ -> false

(* Rel context *)
let lookup_rel = lookup_rel

let evaluable_rel n env =
  is_local_def (lookup_rel n env)

let nb_rel env = env.env_nb_rel

let push_rel = push_rel

let push_rel_context ctxt x = Context.Rel.fold_outside push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

let fold_rel_context f env ~init =
  let rec fold_right env =
    match match_rel_context_val env.env_rel_context with
    | None -> init
    | Some (rd, _, rc) ->
	let env =
	  { env with
	    env_rel_context = rc;
	    env_nb_rel = env.env_nb_rel - 1 } in
	f env rd (fold_right env)
  in fold_right env

(* Named context *)

let named_context_of_val c = c.env_named_ctx

let ids_of_named_context_val c = Id.Map.domain c.env_named_map

(* [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)
let map_named_val = map_named_val

let empty_named_context = Context.Named.empty

let push_named = push_named
let push_named_context = List.fold_right push_named
let push_named_context_val = push_named_context_val

let val_of_named_context ctxt =
  List.fold_right push_named_context_val ctxt empty_named_context_val


let lookup_named = lookup_named
let lookup_named_val id ctxt = fst (Id.Map.find id ctxt.env_named_map)

let eq_named_context_val c1 c2 =
   c1 == c2 || Context.Named.equal Constr.equal (named_context_of_val c1) (named_context_of_val c2)

(* A local const is evaluable if it is defined  *)

open Context.Named.Declaration

let named_type id env =
  get_type (lookup_named id env)

let named_body id env =
  get_value (lookup_named id env)

let evaluable_named id env =
  match named_body id env with
  | Some _      -> true
  | _          -> false

let reset_with_named_context ctxt env =
  { env with
    env_named_context = ctxt;
    env_rel_context = empty_rel_context_val;
    env_nb_rel = 0 }

let reset_context = reset_with_named_context empty_named_context_val

let pop_rel_context n env =
  let rec skip n ctx =
    if Int.equal n 0 then ctx
    else match match_rel_context_val ctx with
    | None -> invalid_arg "List.skipn"
    | Some (_, _, ctx) -> skip (pred n) ctx
  in
  let ctxt = env.env_rel_context in
  { env with
    env_rel_context = skip n ctxt;
    env_nb_rel = env.env_nb_rel - n }

let fold_named_context f env ~init =
  let rec fold_right env =
    match match_named_context_val env.env_named_context with
    | None -> init
    | Some (d, v, rem) ->
	let env =
	  reset_with_named_context rem env in
	f env d (fold_right env)
  in fold_right env

let fold_named_context_reverse f ~init env =
  Context.Named.fold_inside f ~init:init (named_context env)


(* Universe constraints *)

let map_universes f env =
  let s = env.env_stratification in
    { env with env_stratification =
	 { s with env_universes = f s.env_universes } }
				     
let add_constraints c env =
  if Univ.Constraint.is_empty c then env
  else map_universes (UGraph.merge_constraints c) env

let check_constraints c env =
  UGraph.check_constraints c env.env_stratification.env_universes

let push_constraints_to_env (_,univs) env =
  add_constraints univs env

let add_universes strict ctx g =
  let g = Array.fold_left
	    (* Be lenient, module typing reintroduces universes and constraints due to includes *)
	    (fun g v -> try UGraph.add_universe v strict g with UGraph.AlreadyDeclared -> g)
	    g (Univ.Instance.to_array (Univ.UContext.instance ctx))
  in
    UGraph.merge_constraints (Univ.UContext.constraints ctx) g
			   
let push_context ?(strict=false) ctx env =
  map_universes (add_universes strict ctx) env

let add_universes_set strict ctx g =
  let g = Univ.LSet.fold
	    (fun v g -> try UGraph.add_universe v strict g with UGraph.AlreadyDeclared -> g)
	    (Univ.ContextSet.levels ctx) g
  in UGraph.merge_constraints (Univ.ContextSet.constraints ctx) g

let push_context_set ?(strict=false) ctx env =
  map_universes (add_universes_set strict ctx) env

let set_engagement c env = (* Unsafe *)
  { env with env_stratification =
    { env.env_stratification with env_engagement = c } }

let set_typing_flags c env = (* Unsafe *)
  { env with env_typing_flags = c }

(* Global constants *)

let lookup_constant = lookup_constant

let no_link_info = NotLinked

let add_constant_key kn cb linkinfo env =
  let new_constants =
    Cmap_env.add kn (cb,(ref linkinfo, ref None)) env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

let add_constant kn cb env =
  add_constant_key kn cb no_link_info env

let constraints_of cb u =
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.Constraint.empty
  | Polymorphic_const ctx -> Univ.AUContext.instantiate u ctx

(* constant_type gives the type of a constant *)
let constant_type env (kn,u) =
  let cb = lookup_constant kn env in
  match cb.const_universes with
  | Monomorphic_const _ -> cb.const_type, Univ.Constraint.empty
  | Polymorphic_const ctx -> 
    let csts = constraints_of cb u in
    (subst_instance_constr u cb.const_type, csts)

let constant_context env kn =
  let cb = lookup_constant kn env in
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.AUContext.empty
  | Polymorphic_const ctx -> ctx

type const_evaluation_result =
  | NoBody
  | Opaque
  | Primitive of CPrimitives.t

exception NotEvaluableConst of const_evaluation_result

let constant_value_and_type env (kn, u) =
  let cb = lookup_constant kn env in
    if Declareops.constant_is_polymorphic cb then
      let cst = constraints_of cb u in
      let b' = match cb.const_body with
	| Def l_body -> Some (subst_instance_constr u (Mod_subst.force_constr l_body))
	| OpaqueDef _ -> None
        | Undef _ | Primitive _ -> None
      in
	b', subst_instance_constr u cb.const_type, cst
    else 
      let b' = match cb.const_body with
	| Def l_body -> Some (Mod_subst.force_constr l_body)
	| OpaqueDef _ -> None
        | Undef _ | Primitive _ -> None
      in b', cb.const_type, Univ.Constraint.empty

(* These functions should be called under the invariant that [env] 
   already contains the constraints corresponding to the constant 
   application. *)

(* constant_type gives the type of a constant *)
let constant_type_in env (kn,u) =
  let cb = lookup_constant kn env in
    if Declareops.constant_is_polymorphic cb then
      subst_instance_constr u cb.const_type
    else cb.const_type

let constant_value_in env (kn,u) =
  let cb = lookup_constant kn env in
  match cb.const_body with
    | Def l_body -> 
      let b = Mod_subst.force_constr l_body in
	subst_instance_constr u b
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)
    | Primitive p -> raise (NotEvaluableConst (Primitive p))

let constant_opt_value_in env cst =
  try Some (constant_value_in env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant kn env =
  let cb = lookup_constant kn env in
    match cb.const_body with
    | Def _ -> true
    | OpaqueDef _ -> false
    | Undef _ | Primitive _ -> false

let polymorphic_constant cst env =
  Declareops.constant_is_polymorphic (lookup_constant cst env)

let polymorphic_pconstant (cst,u) env =
  if Univ.Instance.is_empty u then false
  else polymorphic_constant cst env

let type_in_type_constant cst env =
  not (lookup_constant cst env).const_typing_flags.check_universes

let lookup_projection cst env =
  match (lookup_constant (Projection.constant cst) env).const_proj with 
  | Some pb -> pb
  | None -> anomaly (Pp.str "lookup_projection: constant is not a projection.")

let is_projection cst env =
  match (lookup_constant cst env).const_proj with 
  | Some _ -> true
  | None -> false

(* Mutual Inductives *)
let lookup_mind = lookup_mind

let polymorphic_ind (mind,i) env =
  Declareops.inductive_is_polymorphic (lookup_mind mind env)

let polymorphic_pind (ind,u) env =
  if Univ.Instance.is_empty u then false
  else polymorphic_ind ind env

let type_in_type_ind (mind,i) env =
  not (lookup_mind mind env).mind_typing_flags.check_universes

let template_polymorphic_ind (mind,i) env =
  match (lookup_mind mind env).mind_packets.(i).mind_arity with 
  | TemplateArity _ -> true
  | RegularArity _ -> false

let template_polymorphic_pind (ind,u) env =
  if not (Univ.Instance.is_empty u) then false
  else template_polymorphic_ind ind env
  
let add_mind_key kn mind_key env =
  let new_inds = Mindmap_env.add kn mind_key env.env_globals.env_inductives in
  let new_globals =
    { env.env_globals with
	env_inductives = new_inds } in
  { env with env_globals = new_globals }

let add_mind kn mib env =
  let li = ref no_link_info in add_mind_key kn (mib, li) env

(* Lookup of section variables *)

let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Context.Named.to_vars cmap.const_hyps

let lookup_inductive_variables (kn,i) env =
  let mis = lookup_mind kn env in
  Context.Named.to_vars mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind constr with
      Var id -> Id.Set.singleton id
    | Const (kn, _) -> lookup_constant_variables kn env
    | Ind (ind, _) -> lookup_inductive_variables ind env
    | Construct (cstr, _) -> lookup_constructor_variables cstr env
    (** FIXME: is Proj missing? *)
    | _ -> raise Not_found

let global_vars_set env constr =
  let rec filtrec acc c =
    let acc =
      match kind c with
      | Var _ | Const _ | Ind _ | Construct _ ->
	  Id.Set.union (vars_of_global env c) acc
      | _ ->
	  acc in
    Constr.fold filtrec acc c
  in
    filtrec Id.Set.empty constr


(* [keep_hyps env ids] keeps the part of the section context of [env] which
   contains the variables of the set [ids], and recursively the variables
   contained in the types of the needed variables. *)

let really_needed env needed =
  Context.Named.fold_inside
    (fun need decl ->
      if Id.Set.mem (get_id decl) need then
        let globc =
          match decl with
            | LocalAssum _ -> Id.Set.empty
            | LocalDef (_,c,_) -> global_vars_set env c in
        Id.Set.union
          (global_vars_set env (get_type decl))
          (Id.Set.union globc need)
      else need)
    ~init:needed
    (named_context env)

let keep_hyps env needed =
  let really_needed = really_needed env needed in
  Context.Named.fold_outside
    (fun d nsign ->
      if Id.Set.mem (get_id d) really_needed then Context.Named.add d nsign
      else nsign)
    (named_context env)
    ~init:empty_named_context

(* Modules *)

let add_modtype mtb env =
  let mp = mtb.mod_mp in
  let new_modtypes = MPmap.add mp mtb env.env_globals.env_modtypes in
  let new_globals = { env.env_globals with env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mb env =
  let mp = mb.mod_mp in
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals = { env.env_globals with env_modules = new_mods } in
  { env with env_globals = new_globals }

let lookup_module mp env =
    MPmap.find mp env.env_globals.env_modules


let lookup_modtype mp env = 
  MPmap.find mp env.env_globals.env_modtypes

(*s Judgments. *)

type ('constr, 'types) punsafe_judgment = {
  uj_val : 'constr;
  uj_type : 'types }

type unsafe_judgment = (constr, types) punsafe_judgment

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val j = j.uj_val
let j_type j = j.uj_type

type 'types punsafe_type_judgment = {
  utj_val : 'types;
  utj_type : Sorts.t }

type unsafe_type_judgment = types punsafe_type_judgment

(*s Compilation of global declaration *)

let compile_constant_body = Cbytegen.compile_constant_body ~fail_on_error:false

exception Hyp_not_found

let apply_to_hyp ctxt id f =
  let rec aux rtail ctxt =
    match match_named_context_val ctxt with
    | Some (d, v, ctxt) ->
	if Id.equal (get_id d) id then
          push_named_context_val_val (f ctxt.env_named_ctx d rtail) v ctxt
	else
	  let ctxt' = aux (d::rtail) ctxt in
	  push_named_context_val_val d v ctxt'
    | None -> raise Hyp_not_found
  in aux [] ctxt

(* To be used in Logic.clear_hyps *)
let remove_hyps ids check_context check_value ctxt =
  let rec remove_hyps ctxt = match match_named_context_val ctxt with
  | None -> empty_named_context_val, false
  | Some (d, v, rctxt) ->
    let (ans, seen) = remove_hyps rctxt in
    if Id.Set.mem (get_id d) ids then (ans, true)
    else if not seen then ctxt, false
    else
      let rctxt' = ans in
      let d' = check_context d in
      let v' = check_value v in
      if d == d' && v == v' && rctxt == rctxt' then
        ctxt, true
      else push_named_context_val_val d' v' rctxt', true
  in
  fst (remove_hyps ctxt)

(* Reduction of native operators *)
open CPrimitives
open Retroknowledge

let retroknowledge env = env.retroknowledge

let add_retroknowledge env (pt,c) =
  match pt with
  | Retro_type PT_int63 ->
    let cte = destConst c in
    let retro = retroknowledge env in
    let retro =
      match retro.retro_int63 with
      | None -> { retro with retro_int63 = Some (cte,c) }
      | Some(cte',_) -> assert (cte = cte'); retro in
    { env with retroknowledge = retro }
  | Retro_ind pit ->
    let (ind,u) = destInd c in
    let retro = retroknowledge env in
    let retro =
      match pit with
      | PIT_bool ->
        let r =
          match retro.retro_bool with
          | None -> (((ind,1),u), ((ind,2),u))
          | Some ((((ind',_),_),_) as t) -> assert (eq_ind ind ind'); t in
        { retro with Retroknowledge.retro_bool = Some r }
      | PIT_carry ->
        let r =
          match retro.retro_carry with
          | None -> (((ind,1), u), ((ind,2),u))
          | Some ((((ind',_),_),_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_carry = Some r }
      | PIT_pair ->
        let r =
          match retro.retro_pair with
          | None -> ((ind,1),u)
          | Some (((ind',_),_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_pair = Some r }
      | PIT_cmp ->
        let r =
          match retro.retro_cmp with
          | None -> (((ind,1), u), ((ind,2),u), ((ind,3),u))
          | Some ((((ind',_),_),_,_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_cmp = Some r }
      | PIT_eq ->
        let r =
          match retro.retro_refl with
          | None -> ((ind,1),u)
          | Some (((ind',_),_) as t) -> assert (eq_ind ind ind'); t in
        { retro with retro_refl = Some r }
    in
    { env with retroknowledge = retro }
  | Retro_inline ->
    let (kn, _univs) = destConst c in
    let (cb,r) = Cmap_env.find kn env.env_globals.env_constants in
    let cb = {cb with const_inline_code = true} in
    let new_constants =
      Cmap_env.add kn (cb,r) env.env_globals.env_constants in
    let new_globals =
      { env.env_globals with
        env_constants = new_constants } in
    { env with env_globals = new_globals }

module type RedNativeEntries =
  sig
    type elem
    type args

    val get : args -> int -> elem
    val get_int :  elem -> Uint63.t
    val is_refl : elem -> bool
    val mk_int_refl : env -> elem -> elem
    val mkInt : env -> Uint63.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem
    val mkClos : Name.t -> constr -> constr -> elem array -> elem

  end

module type RedNative =
 sig
   type elem
   type args
   val red_op : env -> CPrimitives.operation -> args -> elem
   val red_iterator : env -> CPrimitives.iterator -> constr -> args -> elem
      (* the constr represents the iterator *)
   val red_prim : env -> CPrimitives.t -> constr -> args -> elem option
 end

module RedNative (E:RedNativeEntries) :
  RedNative with type elem = E.elem
  with type args = E.args =
struct
  type elem = E.elem
  type args = E.args

  let get_int args i = E.get_int (E.get args i)

  let get_int1 args = get_int args 0

  let get_int2 args = get_int args 0, get_int args 1

  let get_int3 args =
    get_int args 0, get_int args 1, get_int args 2

  let red_op env op args =
    let open CPrimitives in
    match op with
    | Int63head0      ->
      let i = get_int1 args in E.mkInt env (Uint63.head0 i)
    | Int63tail0      ->
      let i = get_int1 args in E.mkInt env (Uint63.tail0 i)
    | Int63add        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.add i1 i2)
    | Int63sub        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.sub i1 i2)
    | Int63mul        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.mul i1 i2)
    | Int63div        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.div i1 i2)
    | Int63mod        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.rem i1 i2)
    | Int63lsr        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.l_sr i1 i2)
    | Int63lsl        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.l_sl i1 i2)
    | Int63land       ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.l_and i1 i2)
    | Int63lor        ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.l_or i1 i2)
    | Int63lxor       ->
      let i1, i2 = get_int2 args in E.mkInt env (Uint63.l_xor i1 i2)
    | Int63addc       ->
      let i1, i2 = get_int2 args in
      let s = Uint63.add i1 i2 in
      E.mkCarry env (Uint63.lt s i1) (E.mkInt env s)
    | Int63subc       ->
      let i1, i2 = get_int2 args in
      let s = Uint63.sub i1 i2 in
      E.mkCarry env (Uint63.lt i1 i2) (E.mkInt env s)
    | Int63addCarryC  ->
      let i1, i2 = get_int2 args in
      let s = Uint63.add (Uint63.add i1 i2) (Uint63.of_int 1) in
      E.mkCarry env (Uint63.le s i1) (E.mkInt env s)
    | Int63subCarryC  ->
      let i1, i2 = get_int2 args in
      let s = Uint63.sub (Uint63.sub i1 i2) (Uint63.of_int 1) in
      E.mkCarry env (Uint63.le i1 i2) (E.mkInt env s)
    | Int63mulc       ->
      let i1, i2 = get_int2 args in
      let (h, l) = Uint63.mulc i1 i2 in
      E.mkPair env (E.mkInt env h) (E.mkInt env l)
    | Int63diveucl    ->
      let i1, i2 = get_int2 args in
      let q,r = Uint63.div i1 i2, Uint63.rem i1 i2 in
      E.mkPair env (E.mkInt env q) (E.mkInt env r)
    | Int63div21      ->
      let i1, i2, i3 = get_int3 args in
      let q,r = Uint63.div21 i1 i2 i3 in
      E.mkPair env (E.mkInt env q) (E.mkInt env r)
    | Int63addMulDiv  ->
      let p, i, j = get_int3 args in
      E.mkInt env
        (Uint63.l_or
           (Uint63.l_sl i p)
           (Uint63.l_sr j (Uint63.sub (Uint63.of_int Uint63.uint_size) p)))
    | Int63eq         ->
      let i1, i2 = get_int2 args in
      E.mkBool env (Uint63.equal i1 i2)
    | Int63lt         ->
      let i1, i2 = get_int2 args in
      E.mkBool env (Uint63.lt i1 i2)
    | Int63le         ->
      let i1, i2 = get_int2 args in
      E.mkBool env (Uint63.le i1 i2)
    | Int63compare    ->
      let i1, i2 = get_int2 args in
      begin match Uint63.compare i1 i2 with
        | x when x < 0 ->  E.mkLt env
        | 0 -> E.mkEq env
        | _ -> E.mkGt env
      end
    | Int63eqb_correct ->
      if E.is_refl (E.get args 2) then E.mk_int_refl env (E.get args 0)
      else raise (Invalid_argument "red_prim:eqb_correct:not refl")

  (* Reduction des iterateurs *)
  (* foldi_cont A B f min max cont
   *     ---> min < max
   *       lam a. f min (foldi A B f (min + 1) max cont) a
   *    ---> min = max
   *       lam a. f min cont a
   *    ---> min > max
   *       lam a. cont a
  *)


  let red_iterator env op it args =
    match op with
    | Int63foldi ->
      let _A = E.get args 0 in
      let _B = E.get args 1 in
      let f = E.get args 2 in
      let min = get_int args 3 in
      let max = get_int args 4 in
      let cont = E.get args 5 in
      let subst = (*[|_A;_B;f;E.get args 3 (* min *);
                    E.get args 4 (* max *);cont|] *)
        [|cont; E.get args 4 (* max *);
          E.get args 3;f;_B;_A|] in
      (* _A->#1;_B->#2;f->#3;min->#4;max ->#5;cont->#6 *)
      let name = Name (Id.of_string "a") in
      let typ =  mkRel 1 (*_A*) in
      (* a->#1;_A->#2;_B->#3;f->#4;min->#5;max ->#6;cont->#7 *)
      let body =
        if Uint63.lt min max then
          begin
            let minp1 = Uint63.add min (Uint63.of_int 1) in
            mkApp (mkRel 4(*f*),
                   [|mkRel 5 (* min *);
                     mkApp (it,
                            [|mkRel 2 (* _A *);
                              mkRel 3 (* _B *);
                              mkRel 4 (* f *);
                              Constr.mkInt minp1; (* min + 1 *)
                              mkRel 6 (* max *);
                              mkRel 7 (* cont *)
                            |]);
                     mkRel 1 (* a*)
                   |])
          end
        else
        if Uint63.equal min max then
          mkApp(mkRel 4(*f *),
                [| mkRel 5; (* min *)
                   mkRel 7; (* cont *)
                   mkRel 1  (* a *)
                |])
        else
          mkApp(mkRel 7,[|mkRel 1|])
      in
      E.mkClos name typ body subst
    | Int63foldi_down ->
      let _A = E.get args 0 in
      let _B = E.get args 1 in
      let f = E.get args 2 in
      let min = get_int args 4 in
      let max = get_int args 3 in
      let cont = E.get args 5 in
      let subst = [|cont; E.get args 3 (* max *);
                    E.get args 4;f;_B;_A|] in
      (* _A->#1;_B->#2;f->#3;min->#4;max ->#5;cont->#6 *)
      let name = Name (Id.of_string "a") in
      let typ =  mkRel 1 (*_A*) in
      (* a->#1;_A->#2;_B->#3;f->#4;min->#5;max ->#6;cont->#7 *)
      let body =
        if Uint63.lt min max then
          begin
            let maxp1 = Uint63.sub max (Uint63.of_int 1) in
            mkApp (mkRel 4(*f*),
                   [|mkRel 6 (* max *);
                     mkApp (it,
                            [|mkRel 2 (* _A *);
                              mkRel 3 (* _B *);
                              mkRel 4 (* f *);
                              Constr.mkInt maxp1; (* max + 1 *)
                              mkRel 5 (* min *);
                              mkRel 7 (* cont *)
                                                    |]);
                                       mkRel 1 (* a*)
                               |])
                end
              else
              if Uint63.equal min max then
                      mkApp(mkRel 4(*f *),
                            [| mkRel 5; (* min *)
                                     mkRel 7; (* cont *)
                                     mkRel 1  (* a *)
                            |])
              else
                      mkApp(mkRel 7,[|mkRel 1|])
            in
            E.mkClos name typ body subst

  let red_prim env p f args =
    let r =
      match p with
      | Iterator it -> red_iterator env it f args
      | Operation op -> red_op env op args
    in Some r

end

