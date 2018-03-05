(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)
Require Import Bvector.
Require Import ZArith.
Require Export Int63Native.
Require Export Int63Op.

Definition wB := (2^(Z.of_nat size))%Z.

Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99) : int63_scope.

Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99) : int63_scope.

Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99) : int63_scope.

Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99) : int63_scope.

Local Open Scope int63_scope.
Local Open Scope Z_scope.

(* Bijection : int63 <-> Bvector size *)

Axiom to_Z_inj : forall x y, [|x|] = [|y|] -> x = y.

Axiom of_to_Z : forall x, of_Z ([|x|]) = x.

(** Specification of logical operations *)
Axiom lsl_spec : forall x p, [| x << p |] = [|x|] * 2^[|p|] mod wB.

Axiom lsr_spec : forall x p, [|x >> p|] = [|x|] / 2 ^ [|p|].

Axiom land_spec: forall x y i , bit (x land y) i = bit x i && bit y i.

Axiom lor_spec: forall x y i, bit (x lor y) i = bit x i || bit y i.

Axiom lxor_spec: forall  x y i, bit (x lxor y) i = xorb (bit x i) (bit y i).

(** Specification of basic opetations *)

(* Arithmetic modulo operations *)

(* Remarque : les axiomes seraient plus simple si on utilise of_Z a la place :
   exemple : add_spec : forall x y, of_Z (x + y) = of_Z x + of_Z y. *)

Axiom add_spec : forall x y, [|x + y|] = ([|x|] + [|y|]) mod wB.

Axiom sub_spec : forall x y, [|x - y|] = ([|x|] - [|y|]) mod wB.

Axiom mul_spec : forall x y, [| x * y |]  = [|x|] * [|y|] mod wB.

Axiom mulc_spec : forall x y, [|x|] * [|y|] = [|fst (mulc x y)|] * wB + [|snd (mulc x y)|].

Axiom div_spec : forall x y, [|x / y|] = [|x|] / [|y|].

Axiom mod_spec : forall x y, [|x \% y|] = [|x|] mod [|y|].

(* Comparisons *)
Axiom eqb_refl : forall x, (x == x)%int63 = true.

Axiom ltb_spec : forall x y, (x < y)%int63 = true <-> [|x|] < [|y|].

Axiom leb_spec : forall x y, (x <= y)%int63 = true <-> [|x|] <= [|y|].

(** Iterators *)

Axiom foldi_cont_gt : forall A B f from to cont,
  (to < from)%int63 = true -> foldi_cont (A:=A) (B:=B) f from to cont = cont.

Axiom foldi_cont_eq : forall A B f from to cont,
  from = to -> foldi_cont (A:=A) (B:=B) f from to cont = f from cont.

Axiom foldi_cont_lt : forall A B f from to cont,
  (from < to)%int63 = true->
  foldi_cont (A:=A) (B:=B) f from to cont =
  f from (fun a' => foldi_cont f (from+1) to cont a').

Axiom foldi_down_cont_lt : forall A B f from downto cont,
  (from < downto)%int63 = true -> foldi_down_cont (A:=A) (B:=B) f from downto cont = cont.

Axiom foldi_down_cont_eq : forall A B f from downto cont,
  from = downto -> foldi_down_cont (A:=A) (B:=B) f from downto cont = f from cont.

Axiom foldi_down_cont_gt : forall A B f from downto cont,
  (downto < from)%int63 = true->
  foldi_down_cont (A:=A) (B:=B) f from downto cont =
  f from (fun a' => foldi_down_cont f (from-1) downto cont a').

(** Axioms on operations which are just short cut *)

Axiom compare_def_spec : forall x y, compare x y = compare_def x y.

Axiom head0_spec  : forall x,  0 < [|x|] ->
         wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB.

Axiom tail0_spec  : forall x, 0 < [|x|] ->
         (exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]))%Z.

Axiom addc_def_spec : forall x y, (x +c y)%int63 = addc_def x y.

Axiom addcarryc_def_spec : forall x y, addcarryc x y = addcarryc_def x y.

Axiom subc_def_spec : forall x y, (x -c y)%int63 = subc_def x y.

Axiom subcarryc_def_spec : forall x y, subcarryc x y = subcarryc_def x y.

Axiom diveucl_def_spec : forall x y, diveucl x y = diveucl_def x y.

Axiom diveucl_21_spec :  forall a1 a2 b,
   let (q,r) := diveucl_21 a1 a2 b in
   ([|q|],[|r|]) = Zdiv_eucl ([|a1|] * wB + [|a2|]) [|b|].

Axiom addmuldiv_def_spec : forall p x y,
  addmuldiv p x y = addmuldiv_def p x y.
