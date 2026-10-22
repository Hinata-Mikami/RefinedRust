From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.enum Require Import def subltype unfold place.
From refinedrust Require Import options.

(** ** Stratification instances for enums *)

Section stratify.
  Context `{!typeGS Σ}.

  Lemma stratify_ltype_enum_owned_some π E L mdu ma {M} (m : M) l
      {rt rte} (en : enum rt) tag (lte : ltype rte) (re : rte) r T :
    (⌜enum_tag en r = Some tag⌝ ∗
      ∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      stratify_ltype π E L mdu ma m
        (GetEnumDataLocSt l en.(enum_els)) lte (#re) Owned
        (λ L2 R2 rte' lte' re',
          ∃ re'', ⌜re' = #re''⌝ ∗
          find_tc_inst
            (TCOrT (TCDone (sem.(enum_tag_sem_rt) = rte')) TCTrue)
            (λ normalize,
              match normalize with
              | TCOrT_l _ _ Heq' =>
                  T L2 R2 rt
                    (EnumLtype en
                      (Some (mk_enum_ltype_variant tag rte' lte' None)))
                    (#(sem.(enum_tag_rt_inj)
                      (eq_rect _ RT_rt re'' _
                        (eq_sym (@done_proof _ Heq')))))
              | TCOrT_r _ _ _ =>
                  T L2 R2 rt
                    (EnumLtype en
                      (Some (mk_enum_ltype_variant tag rte' lte' (Some re''))))
                    (#r)
              end)))
    ⊢ stratify_ltype π E L mdu ma m l
        (EnumLtype en
          (Some (mk_enum_ltype_variant tag rte lte (Some re))))
        (#r) Owned T.
  Proof.
    iIntros "(%Htagcur & %sem & %Hsem & HT)".
    iIntros (F HF1 HF2 HF3) "#CTX #HE HL Hl".
    iPoseProof (enum_ltype_acc_owned with "Hl") as
      "(%el & %Halg & %Hly & #Hlb & >(%variant_ly & %Htag & %Hvariant & %Hst & Htagown & Hpayload & Hclose))";
      first done.
    rewrite interp_enum_ltype_variant_Some_match in Hst; last done.
    iEval (rewrite /interp_enum_ltype_variant decide_True //) in "Htagown Hpayload Hclose".
    iDestruct "Hpayload" as "(%rv & %Hrfn & Hpayload)".
    change (rv = re) in Hrfn. subst rv.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "HT".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hpayload") as
      "(%L2 & %R2 & %rte' & %lte' & %re' & HL & %Hstcompat & Hstep & %re'' & %Hre' & %normalize & HT)".
    subst re'. destruct normalize as [Hnormalize | _].
    - unfold TCDone in Hnormalize. subst rte'. simpl in *.
      pose proof (Hstcompat _ Hst) as Hstnew.
      pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
      pose proof (enum_tag_inj_roundtrip en tag sem Hel re'') as
        [Htagnew Hrtnew Hrnew].
      assert (enum_ltype_variant_rfn en (sem.(enum_tag_rt_inj) re'')
        (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte' None) re'') as Hrfnnew.
      { simpl. exists (f_equal RT_rt (eq_sym Hrtnew)).
        erewrite Hrnew. generalize Hrtnew. intros []. done. }
      iModIntro. iExists L2, R2, _,
        (EnumLtype en
          (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte' None))),
        (#(sem.(enum_tag_rt_inj) re'')).
      iFrame "HL HT". iSplitR; first done.
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hpayload & HR)".
      iMod ("Hclose" $! sem.(enum_tag_sem_rt) lte' None re''
        (sem.(enum_tag_rt_inj) re'') with "[] [] [] Htagown Hpayload") as "Hl".
      { done. }
      { done. }
      { done. }
      iFrame. done.
    - pose proof (Hstcompat _ Hst) as Hstnew.
      iModIntro. iExists L2, R2, _,
        (EnumLtype en
          (Some (mk_enum_ltype_variant tag rte' lte' (Some re'')))), (#r).
      iFrame "HL HT". iSplitR; first done.
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hpayload & HR)".
      iMod ("Hclose" $! rte' lte' (Some re'') re'' r with
        "[] [] [] Htagown Hpayload") as "Hl".
      { done. }
      { done. }
      { done. }
      iFrame. done.
  Qed.
  Definition stratify_ltype_enum_owned_some_inst :=
    [instance @stratify_ltype_enum_owned_some].
  Global Existing Instance stratify_ltype_enum_owned_some_inst | 10.

  Lemma stratify_ltype_enum_owned_none π E L mdu ma {M} (m : M) l
      {rt rte} (en : enum rt) tag (lte : ltype rte) r T :
    (∃ (Htagcur : enum_tag en r = Some tag) sem,
        (* to instantiate tag *)
        ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ (Hsem : enum_tag_ty_inj en tag = Some sem)
        (Heq : sem.(enum_tag_sem_rt) = rte),
      let Hrt := enum_tag_rt_eq en r tag sem Htagcur Hsem in
      let rv := eq_rect _ id (enum_r en r) _
        (f_equal RT_rt (eq_trans (eq_sym Hrt) Heq)) in
        stratify_ltype π E L mdu ma m
          (GetEnumDataLocSt l en.(enum_els)) lte (#rv) Owned
          (λ L2 R2 rte' lte' re',
            ∃ Heq' : sem.(enum_tag_sem_rt) = rte',
            ∃ re'', ⌜re' = #re''⌝ ∗
            T L2 R2 rt
              (EnumLtype en
                (Some (mk_enum_ltype_variant tag rte' lte' None)))
              (#(sem.(enum_tag_rt_inj)
                (eq_rect _ RT_rt re'' _ (eq_sym Heq'))))))
    ⊢ stratify_ltype π E L mdu ma m l
        (EnumLtype en
          (Some (mk_enum_ltype_variant tag rte lte None)))
        (#r) Owned T.
  Proof.
    iIntros "(%Htagcur & %sem & _ & %Hsem & %Heq & HT)". destruct Heq. simpl in *.
    iIntros (F HF1 HF2 HF3) "#CTX #HE HL Hl".
    iPoseProof (enum_ltype_acc_owned with "Hl") as
      "(%el & %Halg & %Hly & #Hlb & >(%variant_ly & %Htag & %Hvariant & %Hst & Htagown & Hpayload & Hclose))";
      first done.
    rewrite interp_enum_ltype_variant_Some_match in Hst; last done.
    iEval (rewrite /interp_enum_ltype_variant decide_True //) in "Htagown Hpayload Hclose".
    iDestruct "Hpayload" as "(%rv' & %Hrfn & Hpayload)".
    set (Hrt := enum_tag_rt_eq en r tag sem Htagcur Hsem).
    set (rv := eq_rect _ id (enum_r en r) _
      (f_equal RT_rt (eq_trans (eq_sym Hrt) eq_refl))).
    assert (enum_ltype_variant_rfn en r
      (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte None) rv) as Hrfn_expected.
    { simpl. exists (f_equal RT_rt (eq_sym Hrt)). done. }
    pose proof (enum_ltype_variant_rfn_unique _ _ _ _ _ Hrfn Hrfn_expected).
    subst rv'.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "HT".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hpayload") as
      "(%L2 & %R2 & %rte' & %lte' & %re' & HL & %Hstcompat & Hstep & %Heq' & %re'' & %Hre' & HT)".
    subst re'. destruct Heq'. simpl in *.
    pose proof (Hstcompat _ Hst) as Hstnew.
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    pose proof (enum_tag_inj_roundtrip en tag sem Hel re'') as
      [Htagnew Hrtnew Hrnew].
    assert (enum_ltype_variant_rfn en (sem.(enum_tag_rt_inj) re'')
      (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte' None) re'') as Hrfnnew.
    { simpl. exists (f_equal RT_rt (eq_sym Hrtnew)).
      erewrite Hrnew. generalize Hrtnew. intros []. done. }
    iModIntro. iExists L2, R2, _,
      (EnumLtype en
        (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte' None))),
      (#(sem.(enum_tag_rt_inj) re'')).
    iFrame "HL HT". iSplitR; first done.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply logical_step_intro. iIntros "(Hpayload & HR)".
    iMod ("Hclose" $! sem.(enum_tag_sem_rt) lte' None re''
      (sem.(enum_tag_rt_inj) re'') with "[] [] [] Htagown Hpayload") as "Hl".
    { done. }
    { done. }
    { done. }
    iFrame. done.
  Qed.
  Definition stratify_ltype_enum_owned_none_inst :=
    [instance @stratify_ltype_enum_owned_none].
  Global Existing Instance stratify_ltype_enum_owned_none_inst | 10.

  Lemma stratify_ltype_enum_owned_canonical π E L mdu ma {M} (m : M) l
      {rt} (en : enum rt) r T :
    (∃ (tag : string) sem,
      (* to instantiate tag *)
      ⌜enum_tag en r = Some tag⌝ ∗
      ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ (Htagcur : enum_tag en r = Some tag)
        (Hsem : enum_tag_ty_inj en tag = Some sem),
      let Hrt := enum_tag_rt_eq en r tag sem Htagcur Hsem in
      let rv := eq_rect _ id (enum_r en r) _ (f_equal RT_rt (eq_sym Hrt)) in
      stratify_ltype π E L mdu ma m (GetEnumDataLocSt l en.(enum_els))
        (OfTy sem.(enum_tag_sem_ty)) (#rv) Owned
        (λ L2 R2 rte' lte' re',
          ∃ Heq' : sem.(enum_tag_sem_rt) = rte',
          ∃ re'', ⌜re' = #re''⌝ ∗
          T L2 R2 rt
            (EnumLtype en
              (Some (mk_enum_ltype_variant tag rte' lte' None)))
            (#(sem.(enum_tag_rt_inj)
              (eq_rect _ RT_rt re'' _ (eq_sym Heq'))))))
    ⊢ stratify_ltype π E L mdu ma m l (EnumLtype en None) (#r) Owned T.
  Proof.
    iIntros "(%tag & %sem & _ & _ & %Htag & %Hsem & HT)".
    iApply stratify_ltype_eqltype.
    iSplitR "HT".
    { iPureIntro. apply eqltype_symm. apply full_eqltype_alt.
      eapply enum_ltype_some_none_full_eqltype with (Heq := eq_refl);
        first done.
      reflexivity. }
    iApply stratify_ltype_enum_owned_none.
    iExists Htag, sem. iR. iExists Hsem, eq_refl. iExact "HT".
  Qed.
  Definition stratify_ltype_enum_owned_canonical_inst :=
    [instance @stratify_ltype_enum_owned_canonical].
  Global Existing Instance stratify_ltype_enum_owned_canonical_inst | 10.

  Definition stratify_ltype_enum_uniq_none_body π E L mdu ma {M} (m : M) l
      {rt rte} (en : enum rt) tag (sem : enum_tag_sem rt)
      (r : rt)
      (Htagcur : enum_tag en r = Some tag)
      (Hsem : enum_tag_ty_inj en tag = Some sem)
      (Hrt : sem.(enum_tag_sem_rt) = enum_rt en r)
      (Heq : sem.(enum_tag_sem_rt) = rte) (lte : ltype rte) κ
      (T : stratify_ltype_cont_t) : iProp Σ :=
    (li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L1),
        let rv := eq_rect _ id (enum_r en r) _
          (f_equal RT_rt (eq_trans (eq_sym Hrt) Heq)) in
        stratify_ltype π E L1 mdu ma m
          (GetEnumDataLocSt l en.(enum_els)) lte (#rv) Owned
          (λ L2 R rte' lte' re',
            ∃ re'', ⌜#re'' = re'⌝ ∗
            prove_place_cond E L2 UpdStrong lte lte' (λ upd,
              li_tactic (check_llctx_place_update_kind_incl_goal E L2 upd
                (UpdUniq [κ])) (λ b,
                if b then
                  ∃ Hrte : rte' = rte, ⌜fast_eq_hint (rte' = rte)⌝ ∗
                  match ma with
                  | StratRefoldFull =>
                      cast_ltype_to_type E L2
                        (EnumLtype en (Some (mk_enum_ltype_variant tag rte'
                          lte' None))) (λ ty',
                        T L2 (llft_elt_toks κs ∗ R) rt (OfTy ty')
                          (#(sem.(enum_tag_rt_inj)
                            (eq_rect _ RT_rt re'' _
                              (eq_trans Hrte (eq_sym Heq))))))
                  | _ =>
                      T L2 (llft_elt_toks κs ∗ R) rt
                        (EnumLtype en (Some (mk_enum_ltype_variant tag rte'
                          lte' None)))
                        (#(sem.(enum_tag_rt_inj)
                          (eq_rect _ RT_rt re'' _
                            (eq_trans Hrte (eq_sym Heq)))))
                  end
                else
                  ⌜fast_eq_hint (ma = StratNoRefold)⌝ ∗
                  T L2 R rt
                    (OpenedLtype
                      (EnumLtype en (Some (mk_enum_ltype_variant tag rte'
                        lte' (Some re''))))
                      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte None)))
                      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte None)))
                      (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs))
                    (#r))))))%I.

  Lemma stratify_ltype_enum_uniq_none π E L mdu ma {M} (m : M) l
      {rt rte} (en : enum rt) tag (lte : ltype rte) r κ γ T :
    (⌜enum_tag en r = Some tag⌝ ∗
      ∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ (Htagcur : enum_tag en r = Some tag)
        (Hsem : enum_tag_ty_inj en tag = Some sem)
        (Hrt : sem.(enum_tag_sem_rt) = enum_rt en r)
        (Heq : sem.(enum_tag_sem_rt) = rte),
        stratify_ltype_enum_uniq_none_body π E L mdu ma m l en tag sem
          r Htagcur Hsem Hrt Heq lte κ T)
    ⊢ stratify_ltype π E L mdu ma m l
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte None)))
        (#r) (Uniq κ γ) T.
  Proof.
    rewrite /stratify_ltype_enum_uniq_none_body.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(_ & %sem & _ & %Htagcur & %Hsem & %Hrt & %Heq & %κs & %L1 & %Hal & HT)".
    destruct Heq. simpl in *.
    iIntros (F HF1 HF2 HF3) "#CTX #HE HL Hl".
    iMod (fupd_mask_subseteq lftE) as "Hm"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as
      "(%q & Htok & Hcltok & HL)"; [done.. |].
    iMod "Hm" as "_".
    iPoseProof (enum_ltype_acc_uniq_update F with
      "CTX Htok Hcltok Hl") as
      "(%el & %Halg & %Hly & #Hlb & Hb)"; first done.
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iEval (rewrite interp_enum_ltype_variant_Some_match; last done) in "Hb".
    iDestruct "Hb" as
      "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htagown & %rv & %Hrfn & Hpayload & Hclose)".
    set (rv_expected := eq_rect _ id (enum_r en r) _
      (f_equal RT_rt (eq_sym Hrt))).
    assert (enum_ltype_variant_rfn en r
      (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte None)
      rv_expected) as Hrfn_expected.
    { simpl. exists (f_equal RT_rt (eq_sym Hrt)). done. }
    pose proof (enum_ltype_variant_rfn_unique _ _ _ _ _ Hrfn Hrfn_expected).
    subst rv.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "HT".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hpayload") as
      "(%L2 & %R & %rte' & %lte' & %re' & HL & %Hstcompat & Hstep & %re'' & %Hre' & HT)".
    subst re'.
    iMod ("HT" with "[//] CTX HE HL") as
      "(HL & %upd & #Hupd_incl & #Hcond & %Hst_eq & HT)".
    unfold check_llctx_place_update_kind_incl_goal.
    iDestruct "HT" as "(%b & %Hb & HT)". destruct b.
    - iDestruct "HT" as "(%Hrte & _ & HT)". subst rte'.
      iPoseProof (lctx_place_update_kind_incl_acc with "HE HL") as "#Hincl";
        first apply Hb.
      iPoseProof (typed_place_cond_incl with "Hincl Hcond") as "#Hconduniq".
      iPoseProof (enum_place_cond_uniq_none en tag sem eq_refl lte lte' [κ]
        Hsem with "Hconduniq") as "#Henumcond".
      pose proof (Hstcompat _ Hst) as Hstnew.
      pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
      pose proof (enum_tag_inj_roundtrip en tag sem Hel re'') as
        [Htagnew Hrtnew Hrnew].
      assert (enum_ltype_variant_rfn en (sem.(enum_tag_rt_inj) re'')
        (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte' None) re'') as Hrfnnew.
      { simpl. exists (f_equal RT_rt (eq_sym Hrtnew)).
        erewrite Hrnew. generalize Hrtnew. intros []. done. }
      assert (enum_ltype_variant_compat en (sem.(enum_tag_rt_inj) re'')
        (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte' None)) as Hcompatnew.
      { split; first done. pose proof Hrfnnew as [He Hr]. exists re'', He.
        split; first exact Hrfnnew. symmetry. exact Hr. }
      iAssert (∃ lt',
        ⌜full_eqltype E L2
          (EnumLtype en (Some (mk_enum_ltype_variant tag
            sem.(enum_tag_sem_rt) lte' None))) lt'⌝ ∗
        T L2 (llft_elt_toks κs ∗ R) _ lt'
          (#(sem.(enum_tag_rt_inj) re'')))%I with "[HT]" as
          "(%lt' & %Heqt & HT)".
      { destruct ma; [ | iFrame; iPureIntro; reflexivity.. ].
        iDestruct "HT" as "(%ty & %Heqt & HT)". by iFrame. }
      iPoseProof (full_eqltype_acc with "CTX HE HL") as "(%Hstout & #Heqout)";
        first apply Heqt.
      iModIntro. iExists L2, (llft_elt_toks κs ∗ R)%I, _, lt',
        (#(sem.(enum_tag_rt_inj) re'')).
      iFrame "HL HT". iSplitR.
      { iPureIntro. rewrite -Hstout. reflexivity. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hclose").
      iApply logical_step_intro. iIntros "Hclose (Hpayload & HR)".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" $! (UpdUniq [κ]) _ lte' None
        (sem.(enum_tag_rt_inj) re'') with
        "[] [] [] [] [] [] Htagown Hpayload Henumcond") as
        "(Hl & Htoks & _)".
      { iApply place_update_kind_incl_refl. }
      { done. }
      { done. }
      { done. }
      { done. }
      { iPureIntro. intros r0. unfold interp_enum_ltype_variant; simpl.
        destruct (decide (enum_tag en r0 = Some tag)); done. }
      iDestruct ("Heqout" $! (Uniq κ γ)
        (#(sem.(enum_tag_rt_inj) re''))) as "((#Hinclout & _) & _)".
      iPoseProof ("Hinclout" with "Hl") as "Hl".
      iModIntro. iFrame.
    - iDestruct "HT" as "(%Hma & HT)".
      unfold fast_eq_hint in Hma. subst ma.
      pose proof (Hstcompat _ Hst) as Hstnew.
      assert (Hcompat_orig : ∀ r0,
        enum_ltype_variant_tag_compat en r0
          (interp_enum_ltype_variant en
            (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte None)) r0) →
        enum_ltype_variant_compat en r0
          (interp_enum_ltype_variant en
            (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte None)) r0)).
      { intros r0 Htagcompat.
        destruct (decide (enum_tag en r0 = Some tag)) as [Htag0 | Htag0].
        - rewrite interp_enum_ltype_variant_Some_match; last done.
          pose proof (enum_tag_rt_eq en r0 tag sem Htag0 Hsem) as Hrt0.
          set (rv0 := eq_rect _ id (enum_r en r0) _
            (f_equal RT_rt (eq_sym Hrt0))).
          split; first done. exists rv0, (f_equal RT_rt (eq_sym Hrt0)).
          split; last done. simpl. exists (f_equal RT_rt (eq_sym Hrt0)). done.
        - rewrite interp_enum_ltype_variant_Some_mismatch; last done.
          rewrite interp_enum_ltype_variant_Some_mismatch in Htagcompat; last done.
          split; first done. exists (enum_r en r0), eq_refl. split; done. }
      iModIntro. iExists L2, R, _,
        (OpenedLtype
          (EnumLtype en (Some (mk_enum_ltype_variant tag rte' lte' (Some re''))))
          (EnumLtype en (Some (mk_enum_ltype_variant tag _ lte None)))
          (EnumLtype en (Some (mk_enum_ltype_variant tag _ lte None)))
          (λ r1 r2, ⌜r1 = r2⌝)%I (λ _ _, llft_elt_toks κs)), (#r).
      iFrame "HL HT". iSplitR; first (simp_ltypes; done).
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hclose").
      iApply logical_step_intro. iIntros "Hclose (Hpayload & HR)".
      iDestruct "Hclose" as "[_ Hclose]".
      iPoseProof ("Hclose" $! rte' lte' re'' with "[] [] Htagown Hpayload") as "Hl".
      { done. }
      { iPureIntro. exact Hcompat_orig. }
      iFrame. done.
  Qed.
  Definition stratify_ltype_enum_uniq_none_inst :=
    [instance @stratify_ltype_enum_uniq_none].
  Global Existing Instance stratify_ltype_enum_uniq_none_inst | 10.

  Lemma stratify_ltype_enum_uniq_canonical π E L mdu ma {M} (m : M) l
      {rt} (en : enum rt) r κ γ T :
    (∃ (tag : string) sem,
      (* instantiate evars *)
      ⌜enum_tag en r = Some tag⌝ ∗
      ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ (Htagcur : enum_tag en r = Some tag)
        (Hsem : enum_tag_ty_inj en tag = Some sem)
        (Hrt : sem.(enum_tag_sem_rt) = enum_rt en r),
      stratify_ltype_enum_uniq_none_body π E L mdu ma m l en tag sem
        r Htagcur Hsem Hrt eq_refl (OfTy sem.(enum_tag_sem_ty)) κ T)
    ⊢ stratify_ltype π E L mdu ma m l (EnumLtype en None) (#r) (Uniq κ γ) T.
  Proof.
    iIntros "(%tag & %sem & _ & _ & %Htagcur & %Hsem & %Hrt & HT)".
    iApply stratify_ltype_eqltype.
    iSplitR "HT".
    { iPureIntro. apply eqltype_symm.
      apply (proj1 (full_eqltype_alt _ _ _ _)).
      eapply enum_ltype_some_none_full_eqltype with (Heq := eq_refl);
        first done.
      reflexivity. }
    iApply stratify_ltype_enum_uniq_none.
    iSplit; first done. iExists sem. iSplit; first done.
    iExists Htagcur, Hsem, Hrt, eq_refl. simpl. iExact "HT".
  Qed.
  Definition stratify_ltype_enum_uniq_canonical_inst :=
    [instance @stratify_ltype_enum_uniq_canonical].
  Global Existing Instance stratify_ltype_enum_uniq_canonical_inst | 10.
End stratify.

(* we should unfold this *)
Global Arguments stratify_ltype_enum_uniq_none_body {Σ typeGS0} π E L mdu ma
  {M} m l {rt rte} en tag sem r Htagcur Hsem Hrt Heq lte κ T /.
