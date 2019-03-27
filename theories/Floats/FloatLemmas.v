Require Import ZArith Int63 SpecFloat FloatNative FloatOps FloatAxioms FloatValues.

Lemma shift_value : [|shift|]%int63 = (2*emax + prec)%Z.
  reflexivity.
Qed.

Theorem frexp_spec : forall f, let (m,e) := frexp f in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF f).
  intro.
  unfold frexp.
  case_eq (frshiftexp f).
  intros.
  assert (H' := frshiftexp_spec f).
  now rewrite H in H'.
Qed.

Require Import Psatz.

Theorem ldexp_spec : forall f e, Prim2SF (ldexp f e) = SFldexp prec emax (Prim2SF f) e.
  intros.
  unfold ldexp.
  rewrite (ldshiftexp_spec f _).
  assert (Hv := Prim2SF_valid f).
  destruct (Prim2SF f); auto.
  unfold SFldexp.
  unfold binary_round.
  assert (Hmod_elim :  forall e, ([| of_Z (Z.max (Z.min e (emax - emin)) (emin - emax - 1)) + shift |]%int63 - [|shift|]%int63 = Z.max (Z.min e (emax - emin)) (emin - emax - 1))%Z).
  {
    intro.
    rewrite add_spec.
    rewrite of_Z_spec.
    rewrite shift_value.
    simpl.
    unfold wB.
    unfold size.
    simpl.
    unfold Z.pow_pos.
    simpl.
    set (n := Z.max (Z.min _ _) _).
    set (wB := 9223372036854775808%Z).
    assert (-2099 <= n <= 2098)%Z by (unfold n; lia).
    rewrite Z.add_mod_idemp_l by (unfold wB; lia).
    destruct H as (H1, H2).
    rewrite Z.mod_small by (unfold wB; lia).
    now rewrite Z.add_simpl_r.
  }
  rewrite Hmod_elim.
  clear Hmod_elim.
  revert Hv.
  unfold valid_binary, bounded, canonical_mantissa.
  unfold shl_align_fexp.
  unfold fexp.
  rewrite Bool.andb_true_iff.
  intro H'.
  destruct H' as (H1,H2).
  apply Zeq_bool_eq in H1.
  apply Z.max_case_strong.
  apply Z.min_case_strong.
  - reflexivity.
  - intros He _.
    destruct (Z.max_spec (Z.pos (digits2_pos p) + z - prec) emin) as [ (H, Hm) | (H, Hm) ].
    + rewrite Hm in H1.
      rewrite <- H1.
      rewrite !Z.max_l by (revert He; unfold emax, emin, prec; lia).
      replace (emin + _)%Z with emax by ring.
      unfold shl_align.
      rewrite <- H1 in H.
      replace (Z.pos _ + _ - _ - _)%Z with (Z.pos (digits2_pos p) - prec)%Z by ring.
      remember (Zpos _ - _)%Z as z'.
      destruct z' ; [ lia | lia | ].
      unfold binary_round_aux.
      unfold shr_fexp.
      unfold fexp.
      unfold Zdigits2.
      unfold shr_record_of_loc, shr.
      rewrite !Z.max_l by (revert H He; unfold emax, emin, prec; lia).
      replace (_ - _)%Z with (Z.pos (digits2_pos (shift_pos p0 p)) - prec)%Z by ring.
      assert (Hs : (Z.pos (digits2_pos (shift_pos p0 p)) <= prec)%Z).
      {
        assert (H' : forall p p', digits2_pos (shift_pos p p') = (digits2_pos p' + p)%positive).
        {
          induction p1.
          intro.
          simpl.
          rewrite IHp1.
          rewrite IHp1.
          lia.
          intro.
          simpl.
          rewrite IHp1.
          rewrite IHp1.
          lia.
          intro.
          simpl.
          lia.
        }
        rewrite H'.
        lia.
      }
      replace (Z.pos (digits2_pos p) + (emin + e) - prec - (emin + e))%Z with (Z.neg p0) by lia.
      unfold shr_m, loc_of_shr_record.
      unfold round_nearest_even.
      unfold round_N, cond_incr.
      remember (Z.pos (digits2_pos (shift_pos p0 p)) - prec)%Z as ds.
      destruct ds.
      * rewrite Z.max_l by (revert He; unfold emax, emin, prec; lia).
        replace (_ - _)%Z with Z0 by lia.
        replace (_ <=? _)%Z with false by (symmetry; rewrite Z.leb_gt; lia).
        rewrite Z.max_l by (revert He; unfold emax, emin, prec; lia).
        replace (_ - _)%Z with Z0 by lia.
        rewrite Z.max_l by (revert He; unfold emax, emin, prec; lia).
        replace (_ - _)%Z with Z0 by lia.
        replace (_ <=? _)%Z with false by (symmetry; rewrite Z.leb_gt; lia).
        reflexivity.
      * exfalso; lia.
      * rewrite Z.max_l by (revert He; unfold emax, emin, prec; lia).
        replace (_ - _)%Z with (Zneg p1) by lia.
        replace (_ <=? _)%Z with false by (symmetry; rewrite Z.leb_gt; lia).
        rewrite Z.max_l by (revert He; unfold emax, emin, prec; lia).
        replace (_ - _)%Z with (Zneg p1) by lia.
        rewrite Z.max_l by (revert He; unfold emax, emin, prec; lia).
        replace (_ - _)%Z with (Zneg p1) by lia.
        replace (_ <=? _)%Z with false by (symmetry; rewrite Z.leb_gt; lia).
        reflexivity.
    + rewrite !Z.max_l by (revert H He; unfold emax, emin, prec; lia).
      rewrite Hm in H1.
      clear Hm.
      replace (Zpos _ + _ - _)%Z with (z + (emax - emin))%Z by (rewrite <- H1 at 1; ring).
      replace (Zpos _ + _ - _)%Z with (z + e)%Z by (rewrite <- H1 at 1; ring).
      unfold shl_align.
      replace (_ - _)%Z with Z0 by ring.
      replace (z + e - _)%Z with Z0 by ring.
      unfold binary_round_aux.
      unfold shr_fexp.
      unfold fexp.
      unfold Zdigits2.
      rewrite !Z.max_l by (revert H He; unfold emax, emin, prec; lia).
      unfold shr_record_of_loc.
      unfold shr.
      unfold Zdigits2.
      replace (Zpos _ + _ - _ - _)%Z with Z0 by lia.
      unfold shr_m.
      unfold loc_of_shr_record.
      unfold round_nearest_even, cond_incr, round_N.
      rewrite Z.max_l by (revert H He; unfold emax, emin, prec; lia).
      replace (Zpos _ + _ - _ - _)%Z with Z0 by lia.
      replace (_ <=? _)%Z with false by (symmetry; rewrite Z.leb_gt; lia).
      replace (Zpos _ + _ - _ - _)%Z with Z0 by lia.
      rewrite Z.max_l by (revert H He; unfold emax, emin, prec; lia).
      replace (Zpos _ + _ - _ - _)%Z with Z0 by lia.
      replace (_ <=? _)%Z with false by (symmetry; rewrite Z.leb_gt; lia).
      reflexivity.
  - rewrite Z.min_le_iff.
    intro H.
    destruct H as [ He | Habs ]; [ | revert Habs; now unfold emin, emax ].
    unfold shl_align_fexp.
    unfold shl_align.
    assert (Hprec : (Z.pos (digits2_pos p) <= prec)%Z).
    {
      destruct (Z.max_spec (Z.pos (digits2_pos p) + z - prec) emin) as [ (Hpi, Hpe) | (Hpi, Hpe) ]; rewrite Hpe in H1; lia.
    }

    assert (Hshr : forall p s, Zdigits2 (shr_m (iter_pos shr_1 p s)) = Z.max Z0 (Zdigits2 (shr_m s) - Z.pos p)%Z).
    {
      assert (Hshr1 : forall s, Zdigits2 (shr_m (shr_1 s)) = Z.max 0 (Zdigits2 (shr_m s) - 1)%Z).
      {
        intro.
        destruct s.
        unfold shr_1.
        destruct shr_m; try (simpl; lia).
        - destruct p0; unfold Zdigits2, shr_m, digits2_pos; lia.
        - destruct p0; unfold Zdigits2, shr_m, digits2_pos; lia.
      }
      induction p0.
      simpl.
      intro.
      do 2 rewrite IHp0.
      rewrite Hshr1.
      lia.
      intros.
      simpl.
      do 2 rewrite IHp0.
      lia.
      apply Hshr1.
    }

    assert (Hd0 : forall z, Zdigits2 z = 0%Z -> z = 0%Z).
    {
      intro.
      unfold Zdigits2.
      now destruct z0.
    }

    assert (Hshr_p0 : forall p0, (prec < Z.pos p0)%Z -> shr_m (iter_pos shr_1 p0 {| shr_m := Z.pos p; shr_r := false; shr_s := false |}) = Z0).
    {
      intros p0 Hp0.
      apply Hd0.
      rewrite Hshr.
      rewrite Z.max_l; [ reflexivity | ].
      unfold shr_m.
      unfold Zdigits2.
      lia.
    }

    assert (Hshr_p0_r : forall p0, (prec < Z.pos p0)%Z -> shr_r (iter_pos shr_1 p0 {| shr_m := Z.pos p; shr_r := false; shr_s := false |}) = false).
    {
      intros p0 Hp0.

      assert (Hshr_p0m1 : shr_m (iter_pos shr_1 (p0-1) {| shr_m := Z.pos p; shr_r := false; shr_s := false |}) = Z0).
      {
        apply Hd0.
        rewrite Hshr.
        rewrite Z.max_l; [ reflexivity | ].
        unfold shr_m.
        unfold Zdigits2.
        lia.
      }

      assert (Hiter_pos : forall A (f : A -> A) p e, iter_pos f (p + 1) e = f (iter_pos f p e)).
      {
        assert (Hiter_pos' : forall A (f : A -> A) p e, iter_pos f p (f e) = f (iter_pos f p e)).
        {
          intros A f'.
          induction p1.
          intro e'.
          simpl.
          now do 2 rewrite IHp1.
          intro e'.
          simpl.
          now do 2 rewrite IHp1.
          intro e'.
          now simpl.
        }
        intros A f'.
        induction p1.
        intros.
        simpl.
        rewrite <- Pos.add_1_r.
        do 2 rewrite IHp1.
        now do 3 rewrite Hiter_pos'.
        intros.
        simpl.
        now do 2 rewrite Hiter_pos'.
        intros.
        now simpl.
      }
      replace p0 with (p0 - 1 + 1)%positive.
      rewrite Hiter_pos.
      unfold shr_1 at 1.
      remember (iter_pos _ _ _) as shr_p0m1.
      destruct shr_p0m1.
      unfold SpecFloat.shr_m in Hshr_p0m1.
      now rewrite Hshr_p0m1.
      rewrite Pos.add_1_r.
      rewrite Pos.sub_1_r.
      apply Pos.succ_pred.
      lia.
    }

    rewrite Z.leb_le in H2.

    destruct (Z.max_spec (Z.pos (digits2_pos p) + (z + (emin - emax - 1)) - prec) emin) as [ (H, Hm) | (H, Hm) ].
    + rewrite Hm.
      replace (_ - _)%Z with (emax - z + 1)%Z by ring.
      remember (emax - z + 1)%Z as z'.
      destruct z'; [ exfalso; lia | | exfalso; lia ].
      unfold binary_round_aux.
      unfold shr_fexp, fexp.
      unfold shr, shr_record_of_loc.
      unfold Zdigits2.
      rewrite Hm.
      replace (_ - _)%Z with (Z.pos p0) by (rewrite Heqz'; ring).
      set (rne := round_nearest_even _ _).
      assert (rne = 0%Z).
      {
        unfold rne.
        unfold round_nearest_even.
        unfold cond_incr.
        unfold round_N.

        assert (Hp0 : (prec < Z.pos p0)%Z) by lia.

        unfold loc_of_shr_record.
        specialize (Hshr_p0_r _ Hp0).
        specialize (Hshr_p0 _ Hp0).
        revert Hshr_p0_r Hshr_p0.
        set (shr_p0 := iter_pos shr_1 _ _).
        destruct shr_p0.
        unfold SpecFloat.shr_r, SpecFloat.shr_m.
        intros Hshr_r Hshr_m.
        rewrite Hshr_r, Hshr_m.
        now destruct shr_s.
      }

      rewrite H0.
      rewrite Z.max_r by (rewrite Heqz'; unfold prec; lia).
      replace (_ - _)%Z with 0%Z by lia.
      unfold shr_m.

      rewrite Z.max_r by lia.
      remember (emin - (z + e))%Z as eminmze.
      destruct eminmze; [ exfalso; lia | | exfalso; lia ].

      rewrite Z.max_r by lia.
      rewrite <- Heqeminmze.

      set (rne' := round_nearest_even _ _).
      assert (Hrne'0 : rne' = 0%Z).
      {
        unfold rne'.
        unfold round_nearest_even.
        unfold cond_incr.
        unfold round_N.

        assert (Hp1 : (prec < Z.pos p1)%Z) by lia.

        unfold loc_of_shr_record.
        specialize (Hshr_p0_r _ Hp1).
        specialize (Hshr_p0 _ Hp1).
        revert Hshr_p0_r Hshr_p0.
        set (shr_p1 := iter_pos shr_1 _ _).
        destruct shr_p1.
        unfold SpecFloat.shr_r, SpecFloat.shr_m.
        intros Hshr_r Hshr_m.
        rewrite Hshr_r, Hshr_m.
        now destruct shr_s.
      }

      rewrite Hrne'0.
      rewrite Z.max_r by (rewrite Heqeminmze; unfold prec; lia).
      replace (_ - _)%Z with 0%Z by lia.
      reflexivity.
    + exfalso; lia.
Qed.
