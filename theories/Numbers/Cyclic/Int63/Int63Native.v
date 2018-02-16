
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Export DoubleType.

Register Inductive bool as ind_bool.
Register Inductive prod as ind_pair.
Register Inductive carry as ind_carry.
Register Inductive comparison as ind_cmp.
Register Inductive eq as ind_eq.

Definition size := 63%nat.

Register Primitive int : Set as int63_type.
Declare ML Module "int63_syntax_plugin".

Delimit Scope int63_scope with int63.
Bind Scope int63_scope with int.

(* Logical operations *)
Register Primitive lsl  : int -> int -> int as int63_lsl.
Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Register Primitive lsr  : int -> int -> int as int63_lsr.
Infix ">>" := lsr (at level 30, no associativity) : int63_scope.

Register Primitive land : int -> int -> int as int63_land.
Infix "land" := land (at level 40, left associativity) : int63_scope.

Register Primitive lor  : int -> int -> int as int63_lor.
Infix "lor" := lor (at level 40, left associativity) : int63_scope.

Register Primitive lxor : int -> int -> int as int63_lxor.
Infix "lxor" := lxor (at level 40, left associativity) : int63_scope.

(* Arithmetic modulo operations *)
Register Primitive add : int -> int -> int as int63_add.
Notation "n + m" := (add n m) : int63_scope.

Register Primitive sub : int -> int -> int as int63_sub.
Notation "n - m" := (sub n m) : int63_scope.

Register Primitive mul : int -> int -> int as int63_mul.
Notation "n * m" := (mul n m) : int63_scope.

Register Primitive mulc : int -> int -> int * int as int63_mulc.

Register Primitive div : int -> int -> int as int63_div.
Notation "n / m" := (div n m) : int63_scope.

Register Primitive mod : int -> int -> int as int63_mod.
Notation "n '\%' m" := (mod n m) (at level 40, left associativity) : int63_scope.

(* Comparisons *)
Register Primitive eqb : int -> int -> bool as int63_eq.
Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

Register Primitive ltb : int -> int -> bool as int63_lt.
Notation "m < n" := (ltb m n) : int63_scope.

Register Primitive leb : int -> int -> bool as int63_le.
Notation "m <= n" := (leb m n) : int63_scope.

(* This operator has the following reduction rule
     eqb_correct i i (eq_refl true) ---> (eq_refl i) *)
Register Primitive eqb_correct : forall i j, (i==j)%int63 = true -> i = j as int63_eqb_correct.

(* Iterators *)
Register Primitive foldi_cont :
   forall
     {A B     : Type}
     (f       : int -> (A -> B) -> A -> B)
     (from to : int)
     (cont    : A -> B),
     A -> B
     as int63_foldi.

Register Primitive foldi_down_cont :
  forall
    {A B         : Type}
    (f           : int -> (A -> B) -> A -> B)
    (from downto : int)
    (cont        : A -> B),
    A -> B
    as int63_foldi_down.

(* Print *)

(*
Register Primitive print_int : int -> int assumption int63_print.
*)
