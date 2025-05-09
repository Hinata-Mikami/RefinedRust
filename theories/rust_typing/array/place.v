From refinedrust Require Export type ltypes.
From refinedrust Require Import int programs.
From refinedrust.array Require Import def subltype.
From refinedrust Require Import options.

Section place.
  Context `{!typeGS Σ}.

  Local Lemma typed_place_cond_ty_array_lift {rt} (def : type rt) len bmin i lts (lt1 lt2 : ltype rt) :
    interpret_iml (◁ def)%I len lts !! i = Some lt1 →
    ([∗ list] κ ∈ concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> lts), bor_kind_outlives bmin κ) -∗
    typed_place_cond_ty bmin lt1 lt2 -∗
    [∗ list] lt1;lt2 ∈ interpret_iml (◁ def) len lts;<[i:= lt2]> (interpret_iml (◁ def) len lts), typed_place_cond_ty bmin lt1 lt2.
  Proof.
    iIntros (Hlook) "#Houtl Hcond".
    rewrite -{1}(list_insert_id (interpret_iml _ _ _) i lt1); last done.
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ lt1 lt2, typed_place_cond_ty bmin lt1 lt2) 0); cycle 1.
    { by eapply lookup_lt_Some. }
    { by eapply lookup_lt_Some. }
    iFrame. iApply big_sepL2_intro; first done.
    iModIntro. iIntros (k lt1' lt2' Hlook' ?). case_decide; first done.
    assert (lt1' = lt2') as -> by congruence.
    apply lookup_interpret_iml_Some_inv in Hlook' as (? & [-> | Hel]).
    { iApply typed_place_cond_ty_refl_ofty. }
    apply elem_of_list_lookup_1 in Hel as (k' & Hlook2).
    iApply typed_place_cond_ty_refl.
    iPoseProof (big_sepL_concat_lookup _ _ k' with "Houtl") as "Ha".
    { rewrite list_lookup_fmap Hlook2. done. }
    done.
  Qed.
  Local Lemma typed_place_cond_rfn_array_lift {rt} (rs : list (place_rfn rt)) ri1 ri2 i bmin :
    rs !! i = Some ri1 → ⊢@{iProp Σ}
    typed_place_cond_rfn bmin ri1 ri2 -∗
    [∗ list] r1;r2 ∈ rs;<[i:=ri2]> rs, typed_place_cond_rfn bmin r1 r2.
  Proof.
    iIntros (Hlook) "Hcond".
    specialize (lookup_lt_Some _ _ _ Hlook) as Hlt.
    rewrite -{1}(list_insert_id rs i ri1); last done.
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ r1 r2, _) 0); [ | lia..].
    iSplitL; first done.
    iApply big_sepL2_intro; first done. iModIntro.
    iIntros (? r1 r2 ??). case_decide; first done.
    assert (r1 = r2) as -> by congruence. destruct bmin; done.
  Qed.

  (** ** typed_place *)
  Lemma typed_place_array_owned π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) wl bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜Forall (lctx_bor_kind_outlives E L1 bmin) (concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> (lts)))⌝ ∗
        typed_place π E L1 (l offsetst{ty_syn_type def}ₗ i') lt r bmin (Owned false) P (λ L2 κs li bi bmin2 rti ltyi ri mstrong,
          T L2 κs li bi bmin2 rti ltyi ri
          (mk_mstrong None
            (fmap (λ weak, mk_weak
              (λ lti2 ri2, ArrayLtype def len ((Z.to_nat i', weak.(weak_lt) lti2 ri2) :: lts))
              (λ ri, #(<[Z.to_nat i' := weak.(weak_rfn) ri]> rs))
              (weak.(weak_R))
              ) mstrong.(mstrong_weak))
          ))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Owned wl) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) T.
  Proof.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (array_ltype_acc_owned with "Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & >(Hb & Hcl))"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "%Hi".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { split; last nia.
      specialize (MinInt_le_0 ISize). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred Hcl".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite interpret_iml_length in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite interpret_iml_length. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & HT)".
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[] [Hb]").
    { destruct bmin; done. }
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs l2 b2 bmin0 rti ltyi ri' [strong weak]) "#Hincl1 Hi Hc".
    iApply ("Hcont" with "[//] Hi").
    iSplitR; first done.
    destruct weak as [ weak | ]; last done.
    simpl. iIntros (ltyi2 ri2 bmin') "#Hincl2 Hi Hcond".
    iDestruct "Hc" as "(_ & Hc)".
    iMod ("Hc" with "[//] Hi Hcond") as "(Hi & Hcond & Htoks & HR)".
    iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hsteq".
    iPoseProof ("Hcl_b" with "[Hi]") as "Hb".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" with "[//] Hb") as "(Hb & Hcondv)".
    (*{ iPureIntro. rewrite Forall_cons. split; first lia. done. }*)
    iFrame.
    iModIntro.
    iDestruct "Hcond" as "(Hcond & Hcond_rfn)".
    iApply ("Hcondv" with "[Hcond] [Hcond_rfn] []").
    - iApply typed_place_cond_ty_array_lift; done.
    - iApply typed_place_cond_rfn_array_lift; done.
    - iPureIntro. apply place_access_rt_rel_refl.
  Qed.
  Global Instance typed_place_array_owned_inst π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) wl bmin ly l it v (tyv : type rtv) (i : rtv) P :
    TypedPlace E L π l (ArrayLtype def len lts) (#rs) bmin (Owned wl) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) | 30 :=
    λ T, i2p (typed_place_array_owned π E L def lts len rs wl bmin ly l it v tyv i P T).

  Lemma typed_place_array_uniq π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ γ bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      (* get lifetime token *)
      li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜Forall (lctx_bor_kind_outlives E L2 bmin) (concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> (lts)))⌝ ∗
        typed_place π E L2 (l offsetst{ty_syn_type def}ₗ i') lt r bmin (Owned false) P (λ L3 κs' li bi bmin2 rti ltyi ri mstrong,
        T L3 (κs ++ κs') li bi bmin2 rti ltyi ri
          (mk_mstrong None
            (fmap (λ weak, mk_weak
              (λ lti2 ri2, ArrayLtype def len ((Z.to_nat i', weak.(weak_lt) lti2 ri2) :: lts))
              (λ ri, #(<[Z.to_nat i' := weak.(weak_rfn) ri]> rs))
              (weak.(weak_R))
              ) mstrong.(mstrong_weak))
          )))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Uniq κ γ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iDestruct "HT" as "(%κs & %L1 & %Hal & HT)".
    iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcltok & HL)"; [done.. | ].
    iPoseProof (array_ltype_acc_uniq with "CTX Htok Hcltok Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & Hb)"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "%Hi".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { split; last nia.
      specialize (MinInt_le_0 ISize). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred Hcl".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite interpret_iml_length in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite interpret_iml_length. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & HT)".
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[] [Hb]").
    { destruct bmin; done. }
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs' l2 b2 bmin0 rti ltyi ri' [strong weak]) "#Hincl1 Hi Hc".
    iApply ("Hcont" with "[//] Hi").
    iSplitR; first done.
    destruct weak as [ weak | ]; last done.
    simpl. iIntros (ltyi2 ri2 bmin') "#Hincl2 Hi Hcond".
    iDestruct "Hc" as "(_ & Hc)".
    iMod ("Hc" with "[//] Hi Hcond") as "(Hi & #Hcond & Htoks & HR)".
    iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hsteq".
    iPoseProof ("Hcl_b" with "[Hi]") as "Hb".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" with "[//] [] [] [] [] Hb") as "(Hb & ? & Hcondv)".
    { rewrite length_insert //. }
    { iApply "Hincl". }
    { iApply typed_place_cond_ty_array_lift; [done.. | ].
      iDestruct "Hcond" as "($ & _)". }
    { iApply typed_place_cond_rfn_array_lift; first done.
      iDestruct "Hcond" as "(_ & $)". }
    { rewrite llft_elt_toks_app. iFrame.
      iApply typed_place_cond_incl; last done.
      iApply bor_kind_min_incl_r. }
  Qed.
  Global Instance typed_place_array_uniq_inst π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ γ bmin ly l it v (tyv : type rtv) (i : rtv) P :
    TypedPlace E L π l (ArrayLtype def len lts) (#rs) bmin (Uniq κ γ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) | 30 :=
    λ T, i2p (typed_place_array_uniq π E L def lts len rs κ γ bmin ly l it v tyv i P T).

  (* TODO this is a problem, because we can only get strong below OpenedLtype etc. *)
  Lemma typed_place_array_shared π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      (* get lifetime token *)
      (*li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),*)
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜Forall (lctx_bor_kind_outlives E L1 bmin) (concat ((λ '(_, lt), ltype_blocked_lfts lt) <$> (lts)))⌝ ∗
        typed_place π E L1 (l offsetst{ty_syn_type def}ₗ i') lt r bmin (Shared κ) P (λ L3 κs' li bi bmin2 rti ltyi ri mstrong,
        T L3 (κs') li bi bmin2 rti ltyi ri
          (mk_mstrong None
            (fmap (λ weak, mk_weak
              (λ lti2 ri2, ArrayLtype def len ((Z.to_nat i', weak.(weak_lt) lti2 ri2) :: lts))
              (λ ri, #(<[Z.to_nat i' := weak.(weak_rfn) ri]> rs))
              (weak.(weak_R))
              ) mstrong.(mstrong_weak))
          ))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Shared κ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) T.
  Proof.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL #Hincl Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (array_ltype_acc_shared with "Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & >(Hb & Hcl))"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "%Hi".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply wp_fupd.
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { split; last nia.
      specialize (MinInt_le_0 ISize). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite interpret_iml_length in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite interpret_iml_length. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & HT)".
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[] [Hb]").
    { destruct bmin; done. }
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs l2 b2 bmin0 rti ltyi ri' [strong weak]) "#Hincl1 Hi Hc".
    iApply ("Hcont" with "[//] Hi").
    iSplitR; first done.
    destruct weak as [ weak | ]; last done.
    simpl. iIntros (ltyi2 ri2 bmin') "#Hincl2 Hi Hcond".
    iDestruct "Hc" as "(_ & Hc)".
    iMod ("Hc" with "[//] Hi Hcond") as "(Hi & Hcond & Htoks & HR)".
    iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "%Hsteq".
    iPoseProof ("Hcl_b" with "[Hi]") as "Hb".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" with "[] [] Hb") as "(Hb & Hcondv)".
    { done. }
    { rewrite length_insert //. }
    (*{ iPureIntro. rewrite Forall_cons. split; first lia. done. }*)
    iFrame.
    iModIntro.
    iDestruct "Hcond" as "(Hcond & Hcond_rfn)".
    iApply "Hcondv".
    simpl.

    rewrite -{1}(list_insert_id (interpret_iml _ _ _) i lti); last done.
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ lt1 lt2, typed_place_cond_ty bmin lt1 lt2) 0); cycle 1.
    { rewrite interpret_iml_length. lia. }
    { rewrite interpret_iml_length. lia. }
    iFrame. iApply big_sepL2_intro; first done.
    iModIntro. iIntros (k lt1 lt2 Hlook ?). case_decide; first done.
    assert (lt1 = lt2) as -> by congruence.
    apply lookup_interpret_iml_Some_inv in Hlook as (? & [-> | Hel]).
    { iApply typed_place_cond_ty_refl_ofty. }
    apply elem_of_list_lookup_1 in Hel as (k' & Hlook).
    iApply typed_place_cond_ty_refl.
    iPoseProof (big_sepL_concat_lookup _ _ k' with "Houtl") as "Ha".
    { rewrite list_lookup_fmap Hlook. done. }
    done.
  Qed.
  Global Instance typed_place_array_shared_inst π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ bmin ly l it v (tyv : type rtv) (i : rtv) P :
    TypedPlace E L π l (ArrayLtype def len lts) (#rs) bmin (Shared κ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) | 30 :=
    λ T, i2p (typed_place_array_shared π E L def lts len rs κ bmin ly l it v tyv i P T).

End place.

Section place_cond.
  Context `{!typeGS Σ}.

  (** ** prove_place_cond instances *)
  (* TODO: should probably augment FoldableRelation to be able to pass something to the continuation. *)
  (*
  Program Definition prove_place_cond_list_interp {rt1 rt2} (k : bor_kind) (len : nat) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2)) (T : iProp Σ) :=
        (prove_place_cond E L k lt1 lt2 (λ upd, T))%I;
      fr_cap := len;
      fr_inv := True;
      fr_core_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2))  :=
        (∃ upd : access_result rt1 rt2,
          match upd with
          | ResultWeak _ => typed_place_cond_ty k lt1 lt2
          | ResultStrong => ⌜ltype_st lt1 = ltype_st lt2⌝%I
          end)%I
    |}.
  Next Obligation.
    iIntros (???? ? E L i a b T ?) "#CTX #HE HL Hcond".
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hincl)".
    iDestruct "Hincl" as "(%upd & ? & $)".
    iModIntro. eauto with iFrame.
  Qed.
  Global Typeclasses Opaque prove_place_cond_list_interp.
   *)

  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  (* TODO: similar unfolding for array
  Lemma prove_place_cond_unfold_mut_l E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (MutLtype (◁ ty) κ) lt T -∗
    prove_place_cond E L k (◁ (mut_ref ty κ)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_l_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k (◁ (mut_ref ty κ))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_mut_l E L ty lt κ k T).
  Lemma prove_place_cond_unfold_mut_r E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (MutLtype (◁ ty) κ) T -∗
    prove_place_cond E L k lt (◁ (mut_ref ty κ)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_r_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k lt (◁ (mut_ref ty κ))%I | 10 := λ T, i2p (prove_place_cond_unfold_mut_r E L ty lt κ k T).
   *)
  (*
  Lemma prove_place_cond_array_ltype E L {rt} (def1 def2 : type rt) (lts1 : ltype rt) (lts2 : ltype rt) len1 len2 κ1 κ2 k T :
    ⌜len1 = len2⌝ ∗ ⌜def1 = def2⌝ ∗
    (*prove_place_cond E L k lt1 lt2 (λ upd, T $ access_result_lift (λ rt, (place_rfn rt * gname)%type) upd) -∗*)
    prove_place_cond E L k (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
  Abort.
   *)
  (*Global Instance prove_place_cond_mut_ltype_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 k :*)
    (*ProvePlaceCond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 5 := λ T, i2p (prove_place_cond_mut_ltype E L lt1 lt2 κ1 κ2 k T).*)
End place_cond.
