From refinedrust Require Export type ltypes.
From refinedrust Require Import int int_rules.
From refinedrust Require Import programs struct.def.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section init.
  Context `{!typeGS Σ}.

  Lemma type_enum_init E L (els : enum_layout_spec) (variant : string) (rsty : rust_type) (e : expr) (T : typed_val_expr_cont_t) :
    ⌜enum_layout_spec_is_layoutable els⌝ ∗
    typed_val_expr E L e (λ L2 π v rti tyi ri,
      ⌜((list_to_map (els_variants els) : gmap _ _) !! variant) = Some (ty_syn_type tyi)⌝ ∗
      ∃ M, named_lfts M ∗ (named_lfts M -∗
      (* get the desired enum type *)
      li_tactic (interpret_rust_type_goal M rsty) (λ '(existT rto tyo),
        ∃ (e : enum rto), ⌜tyo = enum_t e⌝ ∗ ⌜e.(enum_els) = els⌝ ∗
        trigger_tc (ConstructEnum e variant tyi ri) (λ ro,
          (*⌜construct_enum_sc⌝ ∗*)
          ∀ v', T L2 π v' _ (enum_t e) ro))))
    ⊢ typed_val_expr E L (EnumInit els variant rsty e) T.
  Proof.
    iIntros "(%Hly & HT)". destruct Hly as [el Hly].
    iIntros (?) "#CTX #HE HL Hc".
    iApply wp_enum_init; first done.
    iApply ("HT" with "CTX HE HL [Hc]").
    iIntros (L2 π v rt ty r) "HL Hv HT".
    iDestruct "HT" as "(%Hlook_st & %M & Hlfts & HT)".
    iPoseProof ("HT" with "Hlfts") as "HT".
    rewrite /interpret_rust_type_goal.
    iDestruct "HT" as "(%rto &  %tyo & %en & -> & <- & HT)".
    rewrite /trigger_tc. iDestruct "HT" as "(%ro & %Hc & HT)".
    iApply ("Hc" with "HL [Hv] HT").
    iEval (rewrite /ty_own_val/=).
    destruct Hc as [Heq1 Heq2 Heq3 Htag].
    subst.
    iExists _, variant.
    iR. iR.
    iApply (struct_init_val _ _ _ _ +[_; _] -[_; _]).
    { done. }
    { done. }
    simpl.

    assert (∃ tag : Z, list_to_map (M := gmap _ _) (els_tag_int (enum_els en)) !! variant = Some tag) as (tag & Htag_lookup).
    { apply list_to_map_lookup_fst.
      - rewrite els_tag_int_agree.
        apply elem_of_list_fmap. exists (variant, ty_syn_type (enum_ty en ro)).
        split; first done. apply elem_of_list_to_map; last done.
        apply els_variants_nodup.
      - rewrite els_tag_int_agree. apply els_variants_nodup. }
    apply use_enum_layout_alg_inv in Hly as (ul & variant_lys & Hul & Hsl & Hf).

    iSplitR.
    { iExists _, _, (els_tag_it (enum_els en)). iR. simpl.
      iSplitR. { iPureIntro. apply syn_type_has_layout_int; first done. apply els_tag_it_size. }
      iSplitR. { iPureIntro. apply syn_type_has_layout_int; first done. apply els_tag_it_size. }
      rewrite Htag_lookup/=.
      rewrite /enum_lookup_tag.
      rewrite /els_lookup_tag.
      rewrite Htag_lookup /=.
      iApply type_int_val.
      - rewrite -MaxInt_eq. apply els_tag_it_size.
      - specialize (els_tag_int_wf3 (enum_els en)) as Hels.
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
    apply elem_of_list_lookup_1 in Hel as (i & Hlook).
    specialize (Forall2_lookup_l _ _ _ _ _ Hf Hlook) as ([name2 ly] & Hlook_ly & <- & Halg).
    iExists ly. iR.
    iSplitR. { iPureIntro.
      rewrite /layout_of_union_member.
      specialize (union_layout_alg_has_variants _ _ _ _ Hul) as Hul_variants.
      rewrite (index_of_union_lookup _ i _ ly).
      2: { rewrite -Hul_variants. done. }
      simpl. rewrite -Hul_variants. rewrite Hlook_ly. done. }
    simpl.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    iR.
    iSplitL "Hv".
    - rewrite take_app_length'; first done. done.
    - rewrite drop_app_length'; last done.
      iApply uninit_own_spec.
      iExists _. iSplitR. { iPureIntro. apply syn_type_has_layout_untyped; first done.
        - by apply layout_wf_align_log_0.
        - rewrite ly_size_active_union_rest_ly. apply use_union_layout_alg_size in Hul'. lia.
        - by apply ly_align_in_bounds_1. }
      iPureIntro. rewrite /has_layout_val.
      rewrite length_replicate. rewrite /use_layout_alg'.
      erewrite elem_of_list_to_map_1; first last.
      { eapply elem_of_list_lookup_2. done. }
      { apply els_variants_nodup. }
      simpl. rewrite Halg. simpl.
      rewrite /use_union_layout_alg' Hul'/=.
      done.
  Qed.

  (* TODO: would really like to have this lemma instead, but the dependent typing for the evars is trouble *)
  (*
  Lemma type_enum_init π E L (els : enum_layout_spec) (variant : string) (rsty : rust_type) (e : expr) (T : typed_val_expr_cont_t) :
    ⌜enum_layout_spec_is_layoutable els⌝ ∗
    typed_val_expr π E L e (λ L2 v rti tyi ri,
      ⌜((list_to_map (els_variants els) : gmap _ _) !! variant) = Some (ty_syn_type tyi)⌝ ∗
      ∃ M, named_lfts M ∗ (named_lfts M -∗
      (* get the desired enum type *)
      li_tactic (interpret_rust_type_goal M rsty) (λ '(existT rto tyo),
        ∃ (e : enum rto), ⌜tyo = enum_t e⌝ ∗ ⌜e.(enum_els) = els⌝ ∗
        ∃ rti' tyi', ⌜e.(enum_variant_ty) variant = Some (existT rti' tyi')⌝ ∗
        (* TODO also need syntypes to be compatible *)
        ∃ ri' : rti', owned_subtype π E L2 false ri ri' tyi tyi' (λ L3,
        trigger_tc (ConstructEnum e variant tyi' ri') (λ ro,
          (*⌜construct_enum_sc⌝ ∗*)
          ∀ v', T L3 v' _ (enum_t e) ro))))) -∗
    typed_val_expr π E L (EnumInit els variant rsty e) T.
  Proof.
  Admitted.
   *)
End init.


