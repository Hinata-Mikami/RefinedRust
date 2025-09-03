From refinedrust Require Export type ltypes.
From refinedrust Require Import int int_rules.
From refinedrust Require Import programs struct.def.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section init.
  Context `{!typeGS Σ}.

  Import EqNotations.

  Lemma type_enum_init E L (els : enum_layout_spec) (variant : string) (rsen : rust_enum_def) (e : expr) (T : typed_val_expr_cont_t) :
    li_tactic (compute_enum_layout_goal els) (λ _,
    typed_val_expr E L e (λ L2 π v rti tyi ri,
      ∃ M, named_lfts M ∗ (named_lfts M -∗
      (* get the desired enum type *)
      li_tactic (interpret_rust_enum_def_goal M rsen) (λ '(existT rto e),
        ⌜e.(enum_els) = els⌝ ∗
        ∃ sem, ⌜e.(enum_tag_ty_inj) variant = Some sem⌝ ∗
        ⌜(lookup_iml (els_variants els) variant) = Some (st_of sem.(enum_tag_sem_ty))⌝ ∗
          ∃ ri', owned_subtype π E L2 false ri ri' tyi sem.(enum_tag_sem_ty) (λ L3,
            (* could try to remove this by strengthening enum *)
            ⌜e.(enum_tag) (sem.(enum_tag_rt_inj) ri') = Some variant⌝ ∗
            ∃ (Heq : enum_tag_sem_rt sem = enum_rt e (enum_tag_rt_inj sem ri')),
            ⌜e.(enum_r) (sem.(enum_tag_rt_inj) ri') = (rew [RT_rt] Heq in ri')⌝ ∗
              ∀ v', T L3 π v' _ (enum_t e) (sem.(enum_tag_rt_inj) ri'))))))
    ⊢ typed_val_expr E L (EnumInit els variant rsen e) T.
  Proof.
    rewrite /compute_enum_layout_goal.
    iIntros "(%el & %Hly & HT)".
    iIntros (?) "#CTX #HE HL Hc".
    iApply wp_fupd.
    iApply wp_enum_init; first done.
    iApply ("HT" with "CTX HE HL [Hc]").
    iIntros (L2 π v rt ty r) "HL Hv HT".
    iDestruct "HT" as "(%M & Hlfts & HT)".
    iPoseProof ("HT" with "Hlfts") as "HT".
    rewrite /interpret_rust_enum_def_goal.
    iDestruct "HT" as "(%rto &  %en & <- & %sem & %Hinj & %Hlook_st & %ri' & Hsubt)".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L3 & Hincl & HL & HT)"; [done.. | ].
    iDestruct "Hincl" as "(%Hst_eq & Hsc & Hincl)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    iDestruct "HT" as "(%Htagr & %Heq & %Htag_rfn & HT)".
    iApply ("Hc" with "HL [Hv] HT").

    iEval (rewrite /ty_own_val/=).
    iExists _, variant.
    iR. iR.
    iApply (struct_init_val _ _ _ _ +[_; _] -[_; _]).
    { done. }
    { done. }
    simpl.

    set (ro := (enum_tag_rt_inj sem ri')).

    apply lookup_iml_list_to_map in Hlook_st; first last.
    { apply els_variants_nodup. }
    assert (∃ tag : Z, list_to_map (M := gmap _ _) (els_tag_int (enum_els en)) !! variant = Some tag) as (tag & Htag_lookup).
    { apply list_to_map_lookup_fst.
      - rewrite els_tag_int_agree.
        apply list_elem_of_fmap. exists (variant, ty_syn_type (enum_tag_sem_ty sem)).
        split; first done. apply elem_of_list_to_map; last done.
        apply els_variants_nodup.
      - rewrite els_tag_int_agree. apply els_variants_nodup. }
    apply use_enum_layout_alg_inv in Hly as (ul & variant_lys & Hul & Hsl & Hf).

    iSplitR.
    { iExists _, _, (els_tag_it (enum_els en)). iR. simpl.
      iSplitR. { iPureIntro. apply syn_type_has_layout_int; done. }
      iSplitR. { iPureIntro. apply syn_type_has_layout_int; done. }
      rewrite Htag_lookup/=.
      rewrite /enum_lookup_tag.
      rewrite /els_lookup_tag.
      rewrite Htag_lookup /=.
      iApply type_int_val.
      specialize (els_tag_int_wf3 (enum_els en)) as Hels.
      eapply Forall_forall in Hels.
      2: { apply elem_of_list_to_map_2. done. }
      done.
    }
    iSplitL; last done.
    iExists _, _, ul. iR.
    assert (use_union_layout_alg (uls_of_els (enum_els en)) = Some ul) as Hul'.
    { eapply use_union_layout_alg_Some; first done. done. }
    assert (syn_type_has_layout (uls_of_els (enum_els en)) ul).
    { eapply syn_type_has_layout_union; first done. done. }
    iR. iR.

    iEval (rewrite /ty_own_val) => /=.
    iExists ul.
    specialize (elem_of_list_to_map_2 _ _ _ Hlook_st) as Hel.
    apply list_elem_of_lookup_1 in Hel as (i & Hlook).
    specialize (Forall2_lookup_l _ _ _ _ _ Hf Hlook) as ([name2 ly] & Hlook_ly & <- & Halg).
    iExists ly. iR.
    iSplitR. { iPureIntro.
      rewrite /layout_of_union_member.
      specialize (union_layout_alg_has_variants _ _ _ _ Hul) as Hul_variants.
      rewrite (index_of_union_lookup _ i _ ly).
      2: { rewrite -Hul_variants. done. }
      simpl. rewrite -Hul_variants. rewrite Hlook_ly. done. }

    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    iSplitR. {
      iPureIntro.
      enough ((st_of (enum_ty en ro)) = (st_of (enum_tag_sem_ty sem))) as -> by done.
      subst ro.
      rewrite -(enum_tag_type_eq' _ _ variant _ Htagr Hinj).
      clear -Hinj.
      (*unfold enum_tag_rt_eq.*)
      generalize ((enum_tag_rt_eq en _ variant sem Htagr Hinj)).
      intros []. done.
    }
    iSplitL "Hv".
    - rewrite take_app_length'; last done.
      rewrite Htag_rfn.
      rewrite -(enum_tag_type_eq' _ _ variant _ Htagr Hinj).
      unfold ro.
      generalize (enum_tag_rt_eq en (enum_tag_rt_inj sem ri') _ _ Htagr Hinj) as Heq2 => Heq2.
      clear.
      move: Heq2 Heq.
      intros <- Heq.
      rewrite (UIP_refl _ _ Heq).
      done.
    - rewrite drop_app_length'; last done.
      iApply uninit_own_spec.
      iExists _. iSplitR. { iPureIntro. apply syn_type_has_layout_untyped; first done.
        - by apply layout_wf_align_log_0.
        - rewrite ly_size_active_union_rest_ly. apply use_union_layout_alg_size in Hul'. lia.
        - by apply ly_align_in_bounds_1. }
      iPureIntro. rewrite /has_layout_val.
      rewrite length_replicate. rewrite /use_layout_alg'.
      erewrite elem_of_list_to_map_1; first last.
      { eapply list_elem_of_lookup_2. done. }
      { apply els_variants_nodup. }
      simpl. rewrite Halg. simpl.
      rewrite /use_union_layout_alg' Hul'/=.
      done.
  Qed.
End init.
