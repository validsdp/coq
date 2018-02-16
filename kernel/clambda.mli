open Names
open Constr
open Vmvalues

type lambda =
  | Lrel          of Name.t * int
  | Lvar          of Id.t
  | Levar         of Evar.t * lambda array
  | Lprod         of lambda * lambda
  | Llam          of Name.t array * lambda
  | Lrec          of Name.t * lambda
  | Llet          of Name.t * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of pconstant
  | Lprim         of pconstant option * CPrimitives.operation * lambda array
        (* No check if None *)
  | Lcase         of case_info * reloc_table * lambda * lambda * lam_branches
  | Lareint       of lambda array
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * int) * fix_decl
  | Lcofix        of int * fix_decl
  | Lint          of int
  | Lmakeblock    of int * lambda array
  | Luint         of Uint63.t
  | Lval          of structured_values
  | Lsort         of Sorts.t
  | Lind          of pinductive
  | Lproj         of int * Constant.t * lambda

and lam_branches =
  { constant_branches : lambda array;
    nonconstant_branches : (Name.t array * lambda) array }

and fix_decl =  Name.t array * lambda array * lambda array

exception TooLargeInductive of Pp.t

val lambda_of_constr : optimize:bool -> Pre_env.env -> Constr.t -> lambda

val decompose_Llam : lambda -> Name.t array * lambda

val get_alias : Pre_env.env -> Constant.t -> Constant.t
