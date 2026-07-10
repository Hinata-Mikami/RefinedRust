From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules base.value.
From refinedrust Require Import programs ltypes.
From refinedrust Require Import options.
From refinedrust.enum Require Import def subltype.

Section deinit.
  Context `{!typeGS Σ}.

  Local Lemma ofty_owned_to_pointsto_val {rt} (ty : type rt) π r l :
    lty_of_ty_own ty Owned π #r l ={lftE}=∗
    ∃ v, l ↦ v ∗ v ◁ᵥ{π, MetaNone} r @ ty.
  Proof.
    rewrite /lty_of_ty_own.
    iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & %r' & %Hrfn & Hv)".
    subst r'. done.
  Qed.

  Lemma ltype_deinit_enum F π {rt} (en : enum rt) r tag variant_st l :
    lftE ⊆ F →
    enum_tag en r = Some tag →
    ((list_to_map (en.(enum_els).(els_variants)) : gmap _ _)) !! tag = Some variant_st →
    l ◁ₗ[π, Owned] #r @
      EnumLtype en (Some (mk_enum_ltype_variant tag unitRT
        (◁ typed_value_t variant_st) ())) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ typed_value_t en.(enum_els)).
  Proof.
    iIntros (Hincl Htag Hlookup) "Hl".
    rewrite ltype_own_enum_unfold /enum_ltype_own.
    iDestruct "Hl" as "(%el & %Halg & %Hly & Hlb & %r' & Hrfn & Hl)".
    iDestruct "Hrfn" as %<-.
    iMod (fupd_mask_subseteq lftE) as "Hcl"; first done.
    iMod "Hl" as "(%variant_ly & %Htagcompat & %Hvariant & %Hst & Htag & Htag_pad & Hpayload & Htail)".
    assert (interp_enum_ltype_variant en
      (Some (mk_enum_ltype_variant tag unitRT (◁ typed_value_t variant_st)%I ())) r =
      mk_enum_ltype_variant tag unitRT (◁ typed_value_t variant_st)%I ()) as Hinterp.
    { apply interp_enum_ltype_variant_Some_match. done. }
    rewrite Hinterp in Hvariant, Hst |-*.
    iMod (ofty_owned_to_pointsto_val with "Htag") as "(%vtag & Hl_tag & Htag)".
    iMod (ofty_owned_to_pointsto_val with "Htag_pad") as "(%vtag_pad & Hl_tag_pad & Htag_pad)".
    iEval (rewrite /interp_enum_ltype_variant /OfTy /= ltype_own_ofty_unfold) in "Hpayload".
    iMod (ofty_owned_to_pointsto_val with "Hpayload") as "(%vpayload & Hl_payload & Hpayload)".
    iMod (ofty_owned_to_pointsto_val with "Htail") as "(%vtail & Hl_tail & Htail)".
    iPoseProof (ty_own_val_has_layout _ (it_layout el.(el_tag_it)) with "Htag") as "%Hvtag".
    { simpl. apply syn_type_has_layout_int. done. }
    iPoseProof (ty_own_val_has_layout _ (enum_tag_padding_ly el) with "Htag_pad") as "%Hvtag_pad".
    { by apply enum_tag_padding_uninit_syn_type_has_layout with tag variant_ly. }
    iPoseProof (ty_own_val_has_layout _ variant_ly with "Hpayload") as "%Hvpayload".
    { exact Hst. }
    iPoseProof (ty_own_val_has_layout _ (enum_tail_padding_ly el variant_ly) with "Htail") as "%Hvtail".
    { by apply enum_tail_padding_uninit_syn_type_has_layout with tag. }
    iMod "Hcl" as "_".
    iAssert (∃ v : val, ⌜v = vtag ++ vtag_pad ++ vpayload ++ vtail⌝ ∗
        l ↦ v ∗ ⌜v `has_layout_val` layout_of_enum el⌝)%I
      with "[Hl_tag Hl_tag_pad Hl_payload Hl_tail]" as "(%v & -> & Hl & %Hv)".
    { iExists (vtag ++ vtag_pad ++ vpayload ++ vtail).
      iSplitR; first done.
      rewrite !heap_pointsto_app.
      rewrite /has_layout_val in Hvtag, Hvtag_pad, Hvpayload, Hvtail.
      rewrite Hvtag Hvtag_pad Hvpayload /enum_tag_padding_ly /ly_size /=.
      cbn.
      have Heq : bytes_per_int (el_tag_it el) +
          (el_data_offset el - bytes_per_int (el_tag_it el)) = el_data_offset el.
      { pose proof (el_tag_before_data el). rewrite /it_layout /ly_size /bytes_per_int in H |-*; lia. }
      rewrite !shift_loc_assoc_nat.
      rewrite Heq.
      iFrame. iPureIntro.
      rewrite /has_layout_val !length_app Hvtag Hvtag_pad Hvpayload Hvtail
        /enum_tag_padding_ly /enum_tail_padding_ly /layout_of_enum /ly_size /=.
      pose proof (enum_variant_lookup_in_bounds _ _ _ Hvariant).
      rewrite Nat.add_assoc Heq.
      change (el_data_offset el + (ly_size variant_ly +
        (el_size el - el_data_offset el - ly_size variant_ly)) = el_size el).
      nia. }
    iModIntro.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (layout_of_enum el).
    iSplitR. { iPureIntro. simpl. by eapply use_enum_layout_alg_Some_inv. }
    iSplitR; first done.
    iSplitR; first done.
    iSplitL "Hlb"; first iFrame "Hlb".
    iExists (). iR. iModIntro.
    iExists (vtag ++ vtag_pad ++ vpayload ++ vtail). iFrame "Hl".
    rewrite /ty_own_val /=.
    iR.
    iExists (vtag ++ vtag_pad ++ vpayload ++ vtail).
    iDestruct "Hpayload" as "(_ & %payload_vs & Hpayload)".
    iEval (rewrite /ty_own_val /=) in "Hpayload".
    iDestruct "Hpayload" as "(%payload_ot & %Hpayload_alg & %Hpayload_same & %Hpayload_ly & %Hpayload_st)".
    iEval (rewrite int_own_val_unfold) in "Htag".
    iDestruct "Htag" as "(_ & %Htag_val)".
    rewrite /ty_own_val /=.
    iPureIntro.
    split; first done.
    pose proof (use_enum_layout_alg_Some_inv _ _ Halg) as Henum_st.
    destruct (syn_type_has_layout_op_alg _ _ Henum_st) as (ot & Hot & Hotly).
    exists ot. split; first done. split_and!; [ | by rewrite Hotly | by rewrite Hotly].
    apply is_same_decoded_val_refl. intros hs.
    destruct (use_enum_layout_alg_inv _ _ Halg) as (variant_lys & Hel & Hvariant_lys).
    assert (list_map_option
      (λ '(name, st), ly ← use_layout_alg st; Some (name, ly))
      en.(enum_els).(els_variants) = Some variant_lys) as Hvariant_lys'.
    { apply list_map_option_alt. eapply Forall2_impl; first done.
      intros [] [] [-> Hst']. rewrite /syn_type_has_layout in Hst'. by rewrite Hst'. }
    rewrite /syn_type_of_els /enum_layout_spec_raw /use_op_alg Hvariant_lys' /= Hel /= in Hot.
    apply bind_Some in Hot as (variant_ots & Hvariant_ots & Hot).
    rewrite decide_True in Hot; last first.
    { rewrite /enum_tag_int_wf. split_and!.
      - apply els_tag_int_agree.
      - rewrite els_tag_int_agree. apply els_variants_nodup.
      - apply els_tag_int_nodup.
      - apply els_tag_int_wf3. }
    injection Hot as <-. simpl in Hotly.
    apply lookup_iml_list_to_map in Hlookup; last apply els_variants_nodup.
    apply lookup_iml_Some_iff in Hlookup as (idx & Hidx & Hidx_first).
    pose proof Hvariant_ots as Hvariant_ots_rel.
    apply list_map_option_alt in Hvariant_ots_rel.
    destruct (list_map_option_lookup _ _ _ _ _ Hvariant_ots Hidx) as
      ([tag' variant_ot] & Hidx_ot & Hot_variant).
    symmetry in Hot_variant.
    apply bind_Some in Hot_variant as (variant_ot' & Hot_variant & [= <- <-]).
    change (use_op_alg variant_st = Some variant_ot') in Hot_variant.
    rewrite Hpayload_same in Hot_variant. injection Hot_variant as <-.
    assert (enum_variant_ot_lookup variant_ots tag = Some Hpayload_alg) as Hlookup_ot.
    { rewrite /enum_variant_ot_lookup fmap_Some.
      exists (idx, (tag, Hpayload_alg)). split; last done.
      apply list_find_Some. split_and!; [done | done | ].
      intros j [name ot'] Hj Hji Heq. simpl in Heq. subst name.
      destruct (Forall2_lookup_r _ _ _ _ _ Hvariant_ots_rel Hj) as
        ([name st] & Hj' & Hrel).
      have Hne := Hidx_first j name st Hji Hj'.
      simpl in Hrel. apply bind_Some in Hrel as (? & ? & [= <- <-]).
      naive_solver. }
    simp decode_op_val.
    rewrite bool_decide_true; last exact Hv.
    change (length vtag = ly_size (it_layout el.(el_tag_it))) in Hvtag.
    replace (take (ly_size (it_layout (el_tag_it el)))
      (vtag ++ vtag_pad ++ vpayload ++ vtail)) with vtag.
    2: { rewrite -Hvtag. symmetry. apply take_app_length'. done. }
    rewrite Htag_val /=.
    rewrite enum_tag_lookup_els_lookup_tag /=.
    2: { apply list_elem_of_lookup_2 with idx.
         rewrite list_lookup_fmap Hidx //. }
    rewrite Hvariant /lookup_enum_variant_ot Hlookup_ot /=.
    have Hprefix : length (vtag ++ vtag_pad) = el.(el_data_offset).
    { rewrite length_app Hvtag Hvtag_pad /enum_tag_padding_ly /=.
      pose proof (el_tag_before_data el).
      rewrite /it_layout /ly_size /bytes_per_int in H |-*; lia. }
    replace (drop (el_data_offset el) (vtag ++ vtag_pad ++ vpayload ++ vtail))
      with (vpayload ++ vtail).
    2: { rewrite -Hprefix app_assoc drop_app_length' //. }
    rewrite -Hvpayload take_app_length'; last done.
    destruct (is_same_decoded_val_decodable_r _ _ _ hs Hpayload_ly) as
      (payload_ov & Hpayload_dec).
    rewrite Hpayload_dec /=. eauto.
  Qed.

End deinit.

Section rules.
  Context `{!typeGS Σ}.

  Lemma owned_subltype_step_enum_uninit π E L step l {rt rte} (en : enum rt) (lte : ltype rte) rs tag re st T  :
    owned_subltype_step π E L step l #rs #()
      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte re)))
      (◁ typed_value_t st) T :-
    exhale (⌜st = en.(enum_els)⌝);
    exhale (⌜enum_tag en rs = Some tag⌝);
    variant_st ← tactic (compute_map_lookup_nofail_goal
      (list_to_map (en.(enum_els).(els_variants))) tag);
    exhale (⌜ltype_st lte = variant_st⌝);
    ∀ le,
      return owned_subltype_step π E L step le #re #() lte (◁ typed_value_t (ltype_st lte)) T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(-> & %Htag & %variant_st & %Hlookup & %Hst_eq & Hsub)".
    subst variant_st.
    iIntros (????) "#CTX #HE HL Hl". simp_ltypes; simpl.
    iPoseProof (enum_ltype_acc_owned F with "Hl") as
      "(%el & %Halg & %Hly & #Hlb & >(%variant_ly & %Htagcompat & %Hvariant & %Hst & Htag & Hpayload & Hclose))"; first done.
    assert (interp_enum_ltype_variant en
      (Some (mk_enum_ltype_variant tag rte lte re)) rs =
      mk_enum_ltype_variant tag rte lte re) as Hinterp.
    { apply interp_enum_ltype_variant_Some_match. done. }
    rewrite Hinterp /= in Htagcompat, Hvariant, Hst |-*.
    iSpecialize ("Hsub" $! (l +ₗ el.(el_data_offset))).
    iMod ("Hsub" with "[] [] [] CTX HE HL Hpayload") as
      "(%L2 & %R2 & Hstep & HL & HT)"; [done.. | ].
    iExists L2, R2. iFrame "HL HT".
    iModIntro.
    iApply maybe_logical_step_fupd.
    iApply (maybe_logical_step_compose with "Hstep").
    iApply maybe_logical_step_intro.
    iIntros "(Hpayload & HR)".
    iMod ("Hclose" $! unitRT (◁ typed_value_t (ltype_st lte))%I () rs with
      "[] [] Htag Hpayload") as "Hl"; [done.. | ].
    iMod (ltype_deinit_enum F π en rs tag (ltype_st lte) l with "Hl") as "Hl"; [done.. | ].
    iModIntro. iFrame.
  Qed.
  Definition owned_subltype_step_enum_uninit_inst := [instance owned_subltype_step_enum_uninit].
  Global Existing Instance owned_subltype_step_enum_uninit_inst | 20.

End rules.
