Require Import ZArith Rdefinitions Raxioms.

Inductive emulated_float :=
  | E754_zero : bool -> emulated_float
  | E754_infinity : bool -> emulated_float
  | E754_nan : emulated_float
  | E754_finite : bool -> positive -> Z -> emulated_float.

Section FloatOps.
  Variable prec emax : Z.

  Definition emin := (3-emax-prec)%Z.
  Definition fexp e := Z.max (e - prec) emin.

  Section Zdigits2.
    Fixpoint digits2_pos (n : positive) : positive :=
      match n with
      | xH => xH
      | xO p => Pos.succ (digits2_pos p)
      | xI p => Pos.succ (digits2_pos p)
      end.

    Definition Zdigits2 n :=
      match n with
      | Z0 => n
      | Zpos p => Zpos (digits2_pos p)
      | Zneg p => Zpos (digits2_pos p)
      end.
  End Zdigits2.

  Section ValidBinary.
    Definition canonical_mantissa m e :=
      Zeq_bool (fexp (Zpos (digits2_pos m) + e)) e.

    Definition bounded m e :=
      andb (canonical_mantissa m e) (Zle_bool e (emax - prec)).

    Definition valid_binary x :=
      match x with
      | E754_finite _ m e => bounded m e
      | _ => true
      end.
  End ValidBinary.

  Section Iter.
    Context {A : Type}.
    Variable (f : A -> A).

    Fixpoint iter_pos (n : positive) (x : A) {struct n} : A :=
      match n with
      | xI n' => iter_pos n' (iter_pos n' (f x))
      | xO n' => iter_pos n' (iter_pos n' x)
      | xH => f x
      end.
  End Iter.

  Section Rounding.
    Inductive location := loc_Exact | loc_Inexact : comparison -> location.

    Record shr_record := { shr_m : Z ; shr_r : bool ; shr_s : bool }.

    Definition shr_1 mrs :=
      let '(Build_shr_record m r s) := mrs in
      let s := orb r s in
      match m with
      | Z0 => Build_shr_record Z0 false s
      | Zpos xH => Build_shr_record Z0 true s
      | Zpos (xO p) => Build_shr_record (Zpos p) false s
      | Zpos (xI p) => Build_shr_record (Zpos p) true s
      | Zneg xH => Build_shr_record Z0 true s
      | Zneg (xO p) => Build_shr_record (Zneg p) false s
      | Zneg (xI p) => Build_shr_record (Zneg p) true s
      end.

    Definition loc_of_shr_record mrs :=
      match mrs with
      | Build_shr_record _ false false => loc_Exact
      | Build_shr_record _ false true => loc_Inexact Lt
      | Build_shr_record _ true false => loc_Inexact Eq
      | Build_shr_record _ true true => loc_Inexact Gt
      end.

    Definition shr_record_of_loc m l :=
      match l with
      | loc_Exact => Build_shr_record m false false
      | loc_Inexact Lt => Build_shr_record m false true
      | loc_Inexact Eq => Build_shr_record m true false
      | loc_Inexact Gt => Build_shr_record m true true
      end.

    Definition shr mrs e n :=
      match n with
      | Zpos p => (iter_pos shr_1 p mrs, (e + n)%Z)
      | _ => (mrs, e)
      end.

    Definition shr_fexp m e l :=
      shr (shr_record_of_loc m l) e (fexp (Zdigits2 m + e) - e).

    Definition Rcompare x y :=
      match total_order_T x y with
      | inleft (left _) => Lt
      | inleft (right _) => Eq
      | inright _ => Gt
      end.

    Definition Zfloor (x : R) := (up x - 1)%Z.
    Definition Zceil (x : R) := (- Zfloor (- x))%Z.

    Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

    Definition round_N (p : bool) l :=
      match l with
      | loc_Exact => false
      | loc_Inexact Lt => false
      | loc_Inexact Eq => p
      | loc_Inexact Gt => true
      end.

    Definition round_nearest_even mx lx := cond_incr (round_N (negb (Z.even mx)) lx) mx.

    Definition binary_round_aux sx mx ex lx :=
      let '(mrs', e') := shr_fexp mx ex lx in
      let '(mrs'', e'') := shr_fexp (round_nearest_even (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
      match shr_m mrs'' with
      | Z0 => E754_zero sx
      | Zpos m => if Zle_bool e'' (emax - prec) then E754_finite sx m e'' else E754_infinity sx
      | _ => E754_nan
      end.

    Definition shl_align mx ex ex' :=
      match (ex' - ex)%Z with
      | Zneg d => (shift_pos d mx, ex')
      | _ => (mx, ex)
      end.

    Definition shl_align_fexp mx ex :=
      shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

    Definition binary_round sx mx ex :=
      let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux sx (Zpos mz) ez loc_Exact.

    Definition binary_normalize m e szero :=
      match m with
      | Z0 => E754_zero szero
      | Zpos m => binary_round false m e
      | Zneg m => binary_round true m e
      end.
  End Rounding.

  (* Define operations *)
  Definition EFopp x :=
    match x with
    | E754_nan => E754_nan
    | E754_infinity sx => E754_infinity (negb sx)
    | E754_finite sx mx ex => E754_finite (negb sx) mx ex
    | E754_zero sx => E754_zero (negb sx)
    end.

  Definition EFabs x :=
    match x with
    | E754_nan => E754_nan
    | E754_infinity sx => E754_infinity false
    | E754_finite sx mx ex => E754_finite false mx ex
    | E754_zero sx => E754_zero false
    end.

  Definition EFcompare f1 f2 :=
    match f1, f2 with
    | E754_nan , _ | _, E754_nan => None
    | E754_infinity true, E754_infinity true
    | E754_infinity false, E754_infinity false => Some Eq
    | E754_infinity true, _ => Some Lt
    | E754_infinity false, _ => Some Gt
    | _, E754_infinity true => Some Gt
    | _, E754_infinity false => Some Lt
    | E754_finite true _ _, E754_zero _ => Some Lt
    | E754_finite false _ _, E754_zero _ => Some Gt
    | E754_zero _, E754_finite true _ _ => Some Gt
    | E754_zero _, E754_finite false _ _ => Some Lt
    | E754_zero _, E754_zero _ => Some Eq
    | E754_finite s1 m1 e1, E754_finite s2 m2 e2 =>
      match s1, s2 with
      | true, false => Some Lt
      | false, true => Some Gt
      | false, false =>
        match Z.compare e1 e2 with
        | Lt => Some Lt
        | Gt => Some Gt
        | Eq => Some (Pcompare m1 m2 Eq)
        end
      | true, true =>
        match Z.compare e1 e2 with
        | Lt => Some Gt
        | Gt => Some Lt
        | Eq => Some (CompOpp (Pcompare m1 m2 Eq))
        end
      end
    end.

  Definition EFmult x y :=
    match x, y with
    | E754_nan, _ | _, E754_nan => E754_nan
    | E754_infinity sx, E754_infinity sy => E754_infinity (xorb sx sy)
    | E754_infinity sx, E754_finite sy _ _ => E754_infinity (xorb sx sy)
    | E754_finite sx _ _, E754_infinity sy => E754_infinity (xorb sx sy)
    | E754_infinity _, E754_zero _ => E754_nan
    | E754_zero _, E754_infinity _ => E754_nan
    | E754_finite sx _ _, E754_zero sy => E754_zero (xorb sx sy)
    | E754_zero sx, E754_finite sy _ _ => E754_zero (xorb sx sy)
    | E754_zero sx, E754_zero sy => E754_zero (xorb sx sy)
    | E754_finite sx mx ex, E754_finite sy my ey =>
      binary_round_aux (xorb sx sy) (Zpos (mx * my)) (ex + ey) loc_Exact
    end.

  Definition cond_Zopp (b : bool) m := if b then Z.opp m else m.

  Definition EFplus x y :=
    match x, y with
    | E754_nan, _ | _, E754_nan => E754_nan
    | E754_infinity sx, E754_infinity sy =>
      if Bool.eqb sx sy then x else E754_nan
    | E754_infinity _, _ => x
    | _, E754_infinity _ => y
    | E754_zero sx, E754_zero sy =>
      if Bool.eqb sx sy then x else
      E754_zero false
    | E754_zero _, _ => y
    | _, E754_zero _ => x
    | E754_finite sx mx ex, E754_finite sy my ey =>
      let ez := Z.min ex ey in
      binary_normalize (Zplus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez)))))
        ez false
    end.

  Definition EFminus x y :=
    match x, y with
    | E754_nan, _ | _, E754_nan => E754_nan
    | E754_infinity sx, E754_infinity sy =>
      if Bool.eqb sx (negb sy) then x else E754_nan
    | E754_infinity _, _ => x
    | _, E754_infinity sy => E754_infinity (negb sy)
    | E754_zero sx, E754_zero sy =>
      if Bool.eqb sx (negb sy) then x else
      E754_zero false
    | E754_zero _, E754_finite sy my ey => E754_finite (negb sy) my ey
    | _, E754_zero _ => x
    | E754_finite sx mx ex, E754_finite sy my ey =>
      let ez := Z.min ex ey in
      binary_normalize (Zminus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez)))))
        ez false
    end.

  Definition new_location_even nb_steps k l :=
    if Zeq_bool k 0 then
      match l with loc_Exact => l | _ => loc_Inexact Lt end
    else
      loc_Inexact
      match Z.compare (2 * k) nb_steps with
      | Lt => Lt
      | Eq => match l with loc_Exact => Eq | _ => Gt end
      | Gt => Gt
      end.

  Definition new_location_odd nb_steps k l :=
    if Zeq_bool k 0 then
      match l with loc_Exact => l | _ => loc_Inexact Lt end
    else
      loc_Inexact
      match Z.compare (2 * k + 1) nb_steps with
      | Lt => Lt
      | Eq => match l with loc_Inexact l => l | loc_Exact => Lt end
      | Gt => Gt
      end.

  Definition new_location nb_steps :=
    if Z.even nb_steps then new_location_even nb_steps else new_location_odd nb_steps.

  Definition EFdiv_core_binary m1 e1 m2 e2 :=
    let d1 := Zdigits2 m1 in
    let d2 := Zdigits2 m2 in
    let e' := Z.min (fexp (d1 + e1 - (d2 + e2))) (e1 - e2) in
    let s := (e1 - e2 - e')%Z in
    let m' :=
      match s with
      | Zpos _ => Z.shiftl m1 s
      | Z0 => m1
      | Zneg _ => Z0
      end in
    let '(q, r) := Z.div_eucl m' m2 in
    (q, e', new_location m2 r loc_Exact).

  Definition EFdiv x y :=
    match x, y with
    | E754_nan, _ | _, E754_nan => E754_nan
    | E754_infinity sx, E754_infinity sy => E754_nan
    | E754_infinity sx, E754_finite sy _ _ => E754_infinity (xorb sx sy)
    | E754_finite sx _ _, E754_infinity sy => E754_zero (xorb sx sy)
    | E754_infinity sx, E754_zero sy => E754_infinity (xorb sx sy)
    | E754_zero sx, E754_infinity sy => E754_zero (xorb sx sy)
    | E754_finite sx _ _, E754_zero sy => E754_infinity (xorb sx sy)
    | E754_zero sx, E754_finite sy _ _ => E754_zero (xorb sx sy)
    | E754_zero sx, E754_zero sy => E754_nan
    | E754_finite sx mx ex, E754_finite sy my ey =>
      let '(mz, ez, lz) := EFdiv_core_binary (Zpos mx) ex (Zpos my) ey in
      binary_round_aux (xorb sx sy) mz ez lz
    end.

  Definition EFsqrt_core_binary m e :=
    let d := Zdigits2 m in
    let e' := Z.min (fexp (Z.div2 (d + e + 1))) (Z.div2 e) in
    let s := (e - 2 * e')%Z in
    let m' :=
      match s with
      | Zpos p => Z.shiftl m s
      | Z0 => m
      | Zneg _ => Z0
      end in
    let (q, r) := Z.sqrtrem m' in
    let l :=
      if Zeq_bool r 0 then loc_Exact
      else loc_Inexact (if Zle_bool r q then Lt else Gt) in
    (q, e', l).

  Definition EFsqrt x :=
    match x with
    | E754_nan => E754_nan
    | E754_infinity false => x
    | E754_infinity true => E754_nan
    | E754_finite true _ _ => E754_nan
    | E754_zero _ => x
    | E754_finite sx mx ex =>
      let '(mz, ez, lz) := EFsqrt_core_binary (Zpos mx) ex in
      binary_round_aux false mz ez lz
    end.
End FloatOps.
