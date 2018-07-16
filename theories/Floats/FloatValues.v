Require Import Int63 FloatNative.

Local Open Scope float_scope.

(* Special values *)
Definition zero := Eval compute in (of_int63 0).
Definition neg_zero := Eval compute in (-zero).
Definition one := Eval compute in (of_int63 1).
Definition infinity := Eval compute in (one / zero).
Definition neg_infinity := Eval compute in (-infinity).
Definition nan := Eval compute in (zero / zero).
Definition two := Eval compute in (of_int63 2).

Definition is_nan f :=
  match f ?= f with
  | None => true
  | _ => false
  end.

Definition is_zero f :=
  match f ?= zero with
  | Some Eq => true (* note: 0 == -0 with floats *)
  | _ => false
  end.

Definition is_infinity f :=
  match f ?= infinity with
  | Some Eq => true
  | Some Lt => match f ?= neg_infinity with
              | Some Eq => true
              | _ => false
              end
  | _ => false
  end.

Definition get_sign f := (* + => false, - => true *)
  let f := if is_zero f then one / f else f in
  match f ?= zero with
  | Some Gt => false
  | _ => true
  end.

Definition is_finite (x : float) := negb (is_nan x || is_infinity x).
