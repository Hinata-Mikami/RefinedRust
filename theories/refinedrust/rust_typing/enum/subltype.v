From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import ltypes.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.



Section accessors.
  Context `{!typeGS Σ}.

  Lemma enum_ltype_acc_owned {rt} F π
      (en : enum rt) (variant : option enum_ltype_variant) r l :
      lftE ⊆ F →
      l ◁ₗ[π, Owned] #r @ EnumLtype en variant -∗
    ∃ el,
      ⌜use_enum_layout_alg en.(enum_els) = Some el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(el_size) ∗
      let tag_ly := it_layout el.(el_tag_it) in
      let tag_size := ly_size tag_ly in
      let data_offset := el.(el_data_offset) in
      |={F}=>
        ∃ variant_ly,
         let v := interp_enum_ltype_variant en variant r in
         ⌜enum_ltype_variant_tag_compat en r v⌝ ∗
         ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
         ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
         lty_of_ty_own (int el.(el_tag_it)) Owned π
           (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
         (l +ₗ data_offset) ◁ₗ[π, Owned] #v.(eltv_rfn) @ v.(eltv_ltype) ∗
         (∀ rte' (lte' : ltype rte') (re' : rte') r',
           ⌜enum_tag en r' = Some v.(eltv_tag)⌝ -∗
           ⌜syn_type_has_layout (ltype_st lte') variant_ly⌝ -∗
           lty_of_ty_own (int el.(el_tag_it)) Owned π
             (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
           (l +ₗ data_offset) ◁ₗ[π, Owned] #re' @ lte' ={F}=∗
           l ◁ₗ[π, Owned] #r' @
             EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag) rte' lte' re'))).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_enum_unfold /enum_ltype_own.
    iDestruct "Hb" as "(%el & %Halg & %Hly & #Hlb & %r' & -> & Hb)".
    iExists el. do 2 (iSplitR; first done). iSplitR "Hb"; first iFrame "Hlb".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iModIntro.
    iDestruct "Hb" as "(%variant_ly & %Hvariant & %Hst & %Htag & Htag & Htag_pad & Hpayload & Htail)".
    iExists variant_ly. do 3 (iSplitR; first done).
    iSplitL "Htag"; first iExact "Htag".
    iSplitL "Hpayload"; first iExact "Hpayload".
    iIntros (rte' lte' re' rnew) "%Htag_new %Hst_new Htag Hpayload".
    iModIntro.
    rewrite ltype_own_enum_unfold /enum_ltype_own.
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iExists rnew. iSplitR; first done.
    iModIntro.
    iEval (rewrite /interp_enum_ltype_variant decide_True //).
    iExists variant_ly. do 3 (iSplitR; first done). iFrame.
  Qed.

  Lemma enum_ltype_acc_shared {rt} F π
      (en : enum rt) (variant : option enum_ltype_variant) r l κ :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] #r @ EnumLtype en variant -∗
    ∃ el,
      ⌜use_enum_layout_alg en.(enum_els) = Some el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(el_size) ∗
      let tag_ly := it_layout el.(el_tag_it) in
      let tag_size := ly_size tag_ly in
      let data_offset := el.(el_data_offset) in
      |={F}=>
        ∃ variant_ly,
        let v := interp_enum_ltype_variant en variant r in
        ⌜enum_ltype_variant_tag_compat en r v⌝ ∗
        ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
        ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
        lty_of_ty_own (int el.(el_tag_it)) (Shared κ) π
          (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
        (l +ₗ data_offset) ◁ₗ[π, Shared κ] #v.(eltv_rfn) @ v.(eltv_ltype) ∗
        (∀ rte' (lte' : ltype rte') (re' : rte') r',
          ⌜enum_tag en r' = Some v.(eltv_tag)⌝ -∗
          ⌜syn_type_has_layout (ltype_st lte') variant_ly⌝ -∗
          lty_of_ty_own (int el.(el_tag_it)) (Shared κ) π
            (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
          (l +ₗ data_offset) ◁ₗ[π, Shared κ] #re' @ lte' ={F}=∗
          l ◁ₗ[π, Shared κ] #r' @
            EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag) rte' lte' re'))).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_enum_unfold /enum_ltype_own.
    iDestruct "Hb" as "(%el & %Halg & %Hly & #Hlb & %r' & -> & #Hb)".
    iExists el. do 2 (iSplitR; first done). iSplitR ""; first iFrame "Hlb".
    iMod (fupd_mask_mono with "Hb") as "Hb'"; first done.
    iModIntro.
    iDestruct "Hb'" as "(%variant_ly & %Hvariant & %Hst & %Htag & #Htag & #Htag_pad & #Hpayload & #Htail)".
    iExists variant_ly. do 3 (iSplitR; first done).
    iSplitR; first iFrame "Htag".
    iSplitR; first iFrame "Hpayload".
    iIntros (rte' lte' re' rnew) "%Htag_new %Hst_new #Htag' #Hpayload'".
    iModIntro.
    rewrite ltype_own_enum_unfold /enum_ltype_own.
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iExists rnew. iSplitR; first done.
    iModIntro. iModIntro.
    iEval (rewrite /interp_enum_ltype_variant decide_True //).
    iExists variant_ly. do 3 (iSplitR; first done). iFrame "#".
  Qed.

  Lemma enum_ltype_acc_uniq {rt} F π
      (en : enum rt) (variant : option enum_ltype_variant) r l κ γ R q :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #r @ EnumLtype en variant -∗
    ∃ el,
      ⌜use_enum_layout_alg en.(enum_els) = Some el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(el_size) ∗
      let data_offset := el.(el_data_offset) in
      |={F}=>
        ∃ variant_ly,
        let v := interp_enum_ltype_variant en variant r in
        ⌜enum_ltype_variant_compat en r v⌝ ∗
        ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
        ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
        lty_of_ty_own (int el.(el_tag_it)) Owned π
          (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
        (l +ₗ data_offset) ◁ₗ[π, Owned] #v.(eltv_rfn) @ v.(eltv_ltype) ∗
        logical_step F
        (lty_of_ty_own (int el.(el_tag_it)) Owned π
            (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
          (l +ₗ data_offset) ◁ₗ[π, Owned] #v.(eltv_rfn) @ v.(eltv_ltype) ={F}=∗
          l ◁ₗ[π, Uniq κ γ] #r @ EnumLtype en variant ∗ R).
  Proof.
    iIntros (?) "#(LFT & LLCTX) Htok HclR Hb".
    iEval (rewrite ltype_own_enum_unfold /enum_ltype_own) in "Hb".
    iDestruct "Hb" as "(%el & %Halg & %Hly & #Hlb & Hcred & Hrfn & Hb)".
    iExists el. do 2 (iSplitR; first done). iSplitR "Hcred Hrfn Hb Htok HclR"; first iFrame "Hlb".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod "Hb" as "Hb".
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ' & #Hincl & Hb & Hb_back & Hb_cl)"; first done.
    iMod "HF_cl" as "_".
    iDestruct "Hcred" as "([Hcred1 Hcred] & Hat)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iModIntro.
    iDestruct "Hb" as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Htag_pad & Hpayload & Htail)".
    iExists variant_ly. do 3 (iSplitR; first done).
    iFrame "Htag Hpayload".
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hcred' !> Htag Hpayload".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (fupd_mask_mono with "(Hb_cl Hb_back Hcred1 [Hauth Htag Htag_pad Hpayload Htail])") as "(Hb & Htok)"; first done.
    { iNext. iExists r. iFrame. iModIntro. do 2 iR. done. }
    iMod (fupd_mask_mono with "(HclR Htok)") as "$"; first done.
    iModIntro.
    rewrite ltype_own_enum_unfold /enum_ltype_own.
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iFrame "Hrfn".
    iSplitL "Hat Hcred Hcred'".
    { unfold have_creds; simpl. iFrame.
      iApply tr_weaken; last done. unfold num_laters_per_step; lia. }
    iApply pinned_bor_shorten; done.
  Qed.

End accessors.

Section subltype.
  Context `{!typeGS Σ}.

  Local Lemma enum_ltype_incl'_owned_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_tag_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    ltype_incl' Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype) -∗
    ltype_incl' Owned (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst. iIntros "#Hincl !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %r & -> & Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iExists r2. iR.
    iMod "Hb" as "(%ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb & Htail)".
    fold v1 in Hlook, Hst1 |- *. fold v2.
    iMod ("Hincl" with "Hb") as "Hb". iModIntro. iModIntro.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame.
  Qed.

  Local Lemma interp_enum_ltype_variant_core {rt} (en : enum rt) variant r :
    interp_enum_ltype_variant en (enum_ltype_variant_core <$> variant) r =
    enum_ltype_variant_core (interp_enum_ltype_variant en variant r).
  Proof.
    destruct variant as [v|]; simpl; unfold interp_enum_ltype_variant; simpl.
    - destruct (decide (enum_tag en r = Some (eltv_tag v))); first done.
      unfold canonical_enum_ltype_variant, enum_ltype_variant_core. f_equal. simp_ltypes. done.
    - unfold canonical_enum_ltype_variant, enum_ltype_variant_core. f_equal. simp_ltypes. done.
  Qed.

  Lemma enum_ltype_incl_owned_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_tag_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    ltype_incl Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype) -∗
    ltype_incl Owned (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst. iIntros "#Hincl".
    iDestruct "Hincl" as "[Hincl Hcore]". iModIntro. iSplit.
    - by iApply enum_ltype_incl'_owned_in.
    - rewrite !ltype_core_enum.
      iApply enum_ltype_incl'_owned_in; first done;
        rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      + done.
      + done.
      + rewrite !ltype_core_syn_type_eq. done.
      + done.
  Qed.
  Lemma enum_ltype_incl_owned_in_inj {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem rp :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    enum_els en1 = enum_els en2 →
    enum_tag_ty_inj en2 v1.(eltv_tag) = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st (OfTy sem.(enum_tag_sem_ty)) →
    ltype_incl Owned (#v1.(eltv_rfn)) (#rp) v1.(eltv_ltype) (OfTy sem.(enum_tag_sem_ty)) -∗
    ltype_incl Owned (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1) (EnumLtype en2 None).
  Proof.
    intros v1 Hels Hsem Hst. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 v1.(eltv_tag) sem Hel rp) as [Htag Heq Hr].
    pose proof (enum_tag_type_eq' en2 _ _ _ Htag Hsem) as Hty.
    iApply enum_ltype_incl_owned_in; first done.
    - simpl. rewrite /canonical_enum_ltype_variant /= (enum_tag'_Some _ _ _ Htag). done.
    - rewrite /enum_ltype_variant_tag_compat /= (enum_tag'_Some _ _ _ Htag). exact Htag.
    - simpl. rewrite -Hty. generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem).
      intros Heq'. destruct Heq'. done.
    - simpl. rewrite Hr -Hty.
      generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem) as Heq'.
      intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
      rewrite (UIP_refl _ _ Heq0). done.
  Qed.
End subltype.

Section uniform_subltype.
  Context `{!typeGS Σ}.

  Local Lemma enum_ltype_incl'_owned {rt} (en1 en2 : enum rt) variant1 variant2 r :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_tag_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_incl' Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)) -∗
    ltype_incl' Owned r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %r' & Hr & Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iExists r'. iFrame "Hr".
    iDestruct ("Hincl" $! r') as "(%Hcompat & %Hst & Hincl')".
    iMod "Hb" as "(%ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb & Htail)".
    destruct (Hcompat Hcompat1) as [Htag Hcompat2].
    iMod ("Hincl'" with "Hb") as "Hb". iModIntro. iModIntro.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame.
  Qed.

  Lemma enum_ltype_incl_owned {rt} (en1 en2 : enum rt) variant1 variant2 r :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_tag_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_incl Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)) -∗
    ltype_incl Owned r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl". iModIntro. iSplit.
    - iApply enum_ltype_incl'_owned; first done.
      iIntros (r'). iDestruct ("Hincl" $! r') as "($ & $ & Hincl' & _)". done.
    - rewrite !ltype_core_enum. iApply enum_ltype_incl'_owned; first done.
      iIntros (r'). rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      rewrite !ltype_core_syn_type_eq.
      iDestruct ("Hincl" $! r') as "($ & $ & _ & Hcore)". done.
  Qed.
End uniform_subltype.

Section shared_subltype.
  Context `{!typeGS Σ}.

  Local Lemma enum_ltype_incl'_shared_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 κ :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_tag_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    ltype_incl' (Shared κ) (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype) -∗
    ltype_incl' (Shared κ) (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst. iIntros "#Hincl !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %r & -> & #Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iExists r2. iR. iModIntro.
    iMod "Hb" as "(%ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb' & Htail)".
    fold v1 in Hlook, Hst1 |- *. fold v2.
    iPoseProof ("Hincl" with "Hb'") as "Hb'". iModIntro.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame.
  Qed.

  Lemma enum_ltype_incl_shared_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 κ :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_tag_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    ltype_incl (Shared κ) (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype) -∗
    ltype_incl (Shared κ) (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst. iIntros "#Hincl".
    iDestruct "Hincl" as "[Hincl Hcore]". iModIntro. iSplit.
    - by iApply enum_ltype_incl'_shared_in.
    - rewrite !ltype_core_enum.
      iApply enum_ltype_incl'_shared_in; first done;
        rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      + done.
      + done.
      + rewrite !ltype_core_syn_type_eq. done.
      + done.
  Qed.

  Lemma enum_ltype_incl_shared_in_inj {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem rp κ :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    enum_els en1 = enum_els en2 →
    enum_tag_ty_inj en2 v1.(eltv_tag) = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st (OfTy sem.(enum_tag_sem_ty)) →
    ltype_incl (Shared κ) (#v1.(eltv_rfn)) (#rp) v1.(eltv_ltype) (OfTy sem.(enum_tag_sem_ty)) -∗
    ltype_incl (Shared κ) (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1) (EnumLtype en2 None).
  Proof.
    intros v1 Hels Hsem Hst. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 v1.(eltv_tag) sem Hel rp) as [Htag Heq Hr].
    pose proof (enum_tag_type_eq' en2 _ _ _ Htag Hsem) as Hty.
    iApply enum_ltype_incl_shared_in; first done.
    - simpl. rewrite /canonical_enum_ltype_variant /= (enum_tag'_Some _ _ _ Htag). done.
    - rewrite /enum_ltype_variant_tag_compat /= (enum_tag'_Some _ _ _ Htag). exact Htag.
    - simpl. rewrite -Hty. generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem).
      intros Heq'. destruct Heq'. done.
    - simpl. rewrite Hr -Hty.
      generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem) as Heq'.
      intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
      rewrite (UIP_refl _ _ Heq0). done.
  Qed.

  Local Lemma enum_ltype_incl'_shared {rt} (en1 en2 : enum rt) variant1 variant2 r κ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_tag_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_incl' (Shared κ) (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)) -∗
    ltype_incl' (Shared κ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %r' & Hr & #Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iExists r'. iFrame "Hr". iModIntro.
    iDestruct ("Hincl" $! r') as "(%Hcompat & %Hst & Hincl')".
    iMod "Hb" as "(%ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb' & Htail)".
    destruct (Hcompat Hcompat1) as [Htag Hcompat2].
    iPoseProof ("Hincl'" with "Hb'") as "Hb'". iModIntro.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame.
  Qed.

  Lemma enum_ltype_incl_shared {rt} (en1 en2 : enum rt) variant1 variant2 r κ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_tag_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_incl (Shared κ) (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)) -∗
    ltype_incl (Shared κ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl". iModIntro. iSplit.
    - iApply enum_ltype_incl'_shared; first done.
      iIntros (r'). iDestruct ("Hincl" $! r') as "($ & $ & Hincl' & _)". done.
    - rewrite !ltype_core_enum. iApply enum_ltype_incl'_shared; first done.
      iIntros (r'). rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      rewrite !ltype_core_syn_type_eq.
      iDestruct ("Hincl" $! r') as "($ & $ & _ & Hcore)". done.
  Qed.
End shared_subltype.

Section uniq_subltype.
  Context `{!typeGS Σ}.

  (* The invariant must be convertible for every future refinement, in both
     directions, including the core body used when the borrow is closed. *)
  Local Lemma enum_ltype_incl'_uniq {rt} (en1 en2 : enum rt)
      variant1 variant2 r κ γ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
      ⌜enum_ltype_variant_compat en1 r' v1 ↔ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_eq Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)) -∗
    ltype_incl' (Uniq κ γ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Heq !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hloc & Hlb & Hcred & Hrfn & Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & (Hincl & _) & _)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first naive_solver). iFrame.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & _ & Hincl & _)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite Htag Hst. do 3 (iSplitR; first naive_solver). iFrame.
    - iNext. iModIntro. iSplit.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & (_ & Hincl) & _)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        rewrite !ltype_own_core_equiv.
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite -Htag -Hst !ltype_own_core_equiv. do 3 (iSplitR; first naive_solver). iFrame.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & _ & _ & Hincl)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        rewrite !ltype_own_core_equiv.
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite Htag Hst !ltype_own_core_equiv. do 3 (iSplitR; first naive_solver). iFrame.
  Qed.

  Lemma enum_ltype_incl_uniq {rt} (en1 en2 : enum rt)
      variant1 variant2 r κ γ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
      ⌜enum_ltype_variant_compat en1 r' v1 ↔ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_eq Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)) -∗
    ltype_incl (Uniq κ γ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Heq". iModIntro. iSplit.
    - by iApply enum_ltype_incl'_uniq.
    - rewrite !ltype_core_enum. iApply enum_ltype_incl'_uniq; first done.
      iIntros (r'). rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      rewrite !ltype_core_syn_type_eq.
      iDestruct ("Heq" $! r') as "($ & %Hcompat & $ & Heq')".
      iSplitR; first done. by iApply ltype_eq_core.
  Qed.
End uniq_subltype.
