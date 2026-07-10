From refinedrust Require Export type ltypes.
From refinedrust Require Import int int_rules.
From refinedrust Require Import programs struct.def.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section init.
  Context `{!typeGS Σ}.

  Import EqNotations.

  Lemma type_enum_init E L f (els : enum_layout_spec) (variant : string) (rsen : rust_enum_def) (e : expr) (T : typed_val_expr_cont_t) :
    li_tactic (compute_enum_layout_goal els) (λ el,
    ∃ tag st,
    ⌜(list_to_map els.(els_tag_int) : gmap _ _) !! variant = Some tag⌝ ∗
    ⌜(list_to_map els.(els_variants) : gmap _ _) !! variant = Some st⌝ ∗
    typed_val_expr E L f e (λ L2 v m rti tyi ri,
      ∃ M, named_lfts M ∗ (named_lfts M -∗
      (* get the desired enum type *)
      li_tactic (interpret_rust_enum_def_goal M rsen) (λ '(existT rto e),
        ⌜e.(enum_els) = els⌝ ∗
        ⌜m = MetaNone⌝ ∗
        ∃ sem, ⌜enum_tag_ty_inj e variant = Some sem⌝ ∗
        ⌜(lookup_iml (els_variants els) variant) = Some (st_of sem.(enum_tag_sem_ty) MetaNone)⌝ ∗
          ∃ ri', owned_subtype f.1 E L2 false ri ri' tyi sem.(enum_tag_sem_ty) (λ L3,
            ⌜ty_has_op_type sem.(enum_tag_sem_ty) (use_op_alg' (st_of (sem.(enum_tag_sem_ty)) MetaNone))⌝ ∗
            (* could try to remove this by strengthening enum *)
            ⌜e.(enum_tag) (sem.(enum_tag_rt_inj) ri') = Some variant⌝ ∗
            ∃ (Heq : enum_tag_sem_rt sem = enum_rt e (enum_tag_rt_inj sem ri')),
            ⌜e.(enum_r) (sem.(enum_tag_rt_inj) ri') = (rew [RT_rt] Heq in ri')⌝ ∗
              ∀ v', T L3 v' MetaNone _ (enum_t e) (sem.(enum_tag_rt_inj) ri'))))))
    ⊢ typed_val_expr E L f (EnumInit els variant rsen e) T.
  Proof.
    rewrite /compute_enum_layout_goal.
    iIntros "(%el & %Hly & %tag & %st & %Htag_lookup & %Hvariant & HT)".
    iIntros (?) "#CTX #HE HL Hf Hc".
    iApply wpe_fupd.
    iApply wp_enum_init; [done | done | done |].
    iApply ("HT" with "CTX HE HL Hf [Hc]").
    iIntros (L2 v rt ty r m) "HL Hf Hv HT".
    iDestruct "HT" as "(%M & Hlfts & HT)".
    iPoseProof ("HT" with "Hlfts") as "HT".
    rewrite /interpret_rust_enum_def_goal.
    iDestruct "HT" as "(%rto &  %en & <- & -> & %sem & %Hinj & %Hlook_st & %ri' & Hsubt)".
    apply lookup_iml_list_to_map in Hlook_st; last apply els_variants_nodup.
    rewrite Hvariant in Hlook_st. injection Hlook_st as ->.
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L3 & Hincl & HL & HT)"; [done.. | ].
    iDestruct "Hincl" as "(%Hst_eq & Hsc & Hincl)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    iDestruct "HT" as "(%Hty_ot & %Htagr & %Heq & %Htag_rfn & HT)".

    iPoseProof (ty_decodable _ _ _ inhabitant with "Hv") as "(%payload & %Hdecode)"; first done.
    iModIntro. iExists payload. iSplitR.
    { iPureIntro. intros hst.
      rewrite (decode_op_val_stable v _ hst inhabitant). done. }
    iApply physical_step_intro; iNext.
    iApply ("Hc" with "HL Hf [Hv] HT").

    set (ro := (enum_tag_rt_inj sem ri')).
    pose proof Hly as Hly'.
    apply use_enum_layout_alg_inv in Hly' as (variant_lys & Halg & Hf).
    specialize (elem_of_list_to_map_2 _ _ _ Hvariant) as Hel.
    apply list_elem_of_lookup_1 in Hel as (i & Hlook).
    specialize (Forall2_lookup_l _ _ _ _ _ Hf Hlook) as ([name2 ly] & Hlook_ly & <- & Hst_ly).
    pose proof (enum_layout_alg_has_variants _ _ _ _ _ Halg) as (Hel_tag_it & Hel_variants).
    assert (enum_variant_lookup (el_variants el) variant = Some ly) as Hvariant_ly.
    { apply enum_variant_lookup_is_Some. rewrite -Hel_variants. by eapply list_elem_of_lookup_2. }
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv_ly"; first done.
    assert (length v = ly_size ly) as Hv_len.
    { by rewrite /has_layout_val in Hv_ly. }
    assert (length (i2v tag (el_tag_it el) ++
      replicate (el_data_offset el - ly_size (el_tag_it el)) MPoison) =
      el_data_offset el) as Htag_prefix_len.
    { rewrite length_app i2v_length length_replicate /it_layout /ly_size /bytes_per_int /=.
      pose proof (el_tag_before_data el). rewrite /it_layout /ly_size /bytes_per_int /= in H. lia. }

    iEval (rewrite /ty_own_val/= enum_own_val_unfold /enum_own_val_def).
    iExists el, variant, ly.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR.
    { iPureIntro.
      enough ((st_of (enum_ty en ro)) = (st_of (enum_tag_sem_ty sem))) as -> by done.
      subst ro.
      rewrite -(enum_tag_type_eq' _ _ variant _ Htagr Hinj).
      clear -Hinj.
      generalize ((enum_tag_rt_eq en _ variant sem Htagr Hinj)).
      intros []. done. }
    iSplitR.
    { rewrite -Hel_tag_it.
      rewrite take_app_length'; last by rewrite i2v_length.
      rewrite /enum_lookup_tag /els_lookup_tag Htag_lookup /=.
      iApply type_int_val.
      specialize (els_tag_int_wf3 (enum_els en)) as Hels.
      eapply Forall_forall in Hels.
      2: { apply elem_of_list_to_map_2. done. }
      rewrite Hel_tag_it. done. }
    iSplitR.
    { rewrite -Hel_tag_it.
      rewrite drop_app_length'; last by rewrite i2v_length.
      rewrite take_app_length'; last by rewrite length_replicate.
      iApply uninit_own_spec. iR.
      iExists _. iSplitR.
      { iPureIntro. by apply enum_tag_padding_syn_type_has_layout with variant ly. }
      iPureIntro. rewrite /has_layout_val length_replicate /enum_tag_padding_ly /=. done. }
    iSplitL "Hv".
    - rewrite -Hel_tag_it.
      replace (take (ly_size ly)
        (drop (el_data_offset el)
          (i2v tag (el_tag_it el) ++
           replicate (el_data_offset el - ly_size (el_tag_it el)) MPoison ++
           v ++ replicate (el_size el - el_data_offset el - length v) MPoison))) with v.
      2: { symmetry. rewrite app_assoc.
        rewrite drop_app_length'; last by rewrite Htag_prefix_len.
        rewrite take_app_length'; last done. done. }
      rewrite Htag_rfn.
      rewrite -(enum_tag_type_eq' _ _ variant _ Htagr Hinj).
      unfold ro.
      generalize (enum_tag_rt_eq en (enum_tag_rt_inj sem ri') _ _ Htagr Hinj) as Heq2 => Heq2.
      clear.
      move: Heq2 Heq.
      intros <- Heq.
      rewrite (UIP_refl _ _ Heq).
      done.
    - rewrite -Hel_tag_it.
      replace (drop (el_data_offset el + ly_size ly)
        (i2v tag (el_tag_it el) ++
         replicate (el_data_offset el - ly_size (el_tag_it el)) MPoison ++
         v ++ replicate (el_size el - el_data_offset el - length v) MPoison)) with
        (replicate (el_size el - el_data_offset el - length v) MPoison).
      2: { symmetry. rewrite !app_assoc.
        rewrite drop_app_length'; last by rewrite length_app Htag_prefix_len Hv_len.
        done. }
      rewrite Hv_len.
      iApply uninit_own_spec. iR.
      iExists _. iSplitR.
      { iPureIntro. by apply enum_tail_padding_syn_type_has_layout with variant. }
      iPureIntro. rewrite /has_layout_val length_replicate /enum_tail_padding_ly /=. done.
  Qed.
End init.
