From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import ltypes.
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

  (* How do we formulate ltype_eq compatibility? 

  *)

  (*
  Definition enum_ltype_variant_incl (v1 v2 : enum_ltype_variant) :=
    v1.(eltv_tag) = v2.(eltv_tag) ∗ 
    ∃ (Heq : v1.(eltv_rt) = v2.(eltv_rt)), 
      ltype_incl 

  Lemma array_ltype_incl'_shared : 
    
    ltype_incl' (Shared κ) r r (EnumLtype en variant1) (EnumLtype en variant2).
    *)


End subltype.
