From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules programs.
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
         (∃ rv, ⌜enum_ltype_variant_rfn en r v rv⌝ ∗
           (l +ₗ data_offset) ◁ₗ[π, Owned] #rv @ v.(eltv_ltype)) ∗
          (∀ rte' (lte' : ltype rte') (rfn' : option rte') (re' : rte') r',
            ⌜enum_tag en r' = Some v.(eltv_tag)⌝ -∗
            ⌜enum_ltype_variant_rfn en r'
              (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn') re'⌝ -∗
           ⌜syn_type_has_layout (ltype_st lte') variant_ly⌝ -∗
           lty_of_ty_own (int el.(el_tag_it)) Owned π
             (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
           (l +ₗ data_offset) ◁ₗ[π, Owned] #re' @ lte' ={F}=∗
           l ◁ₗ[π, Owned] #r' @
               EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn'))).
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
    iIntros (rte' lte' rfn' re' rnew) "%Htag_new %Hrfn_new %Hst_new Htag Hpayload".
    iModIntro.
    rewrite ltype_own_enum_unfold /enum_ltype_own.
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iExists rnew. iSplitR; first done.
    iModIntro.
    iEval (rewrite /interp_enum_ltype_variant decide_True //).
    iExists variant_ly. do 3 (iSplitR; first done). iFrame. done.
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
        ⌜is_xrfn r⌝ ∗
        ⌜enum_ltype_variant_tag_compat en r v⌝ ∗
        ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
        ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
        lty_of_ty_own (int el.(el_tag_it)) (Shared κ) π
          (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
         (∃ rv, ⌜enum_ltype_variant_rfn en r v rv⌝ ∗
           (l +ₗ data_offset) ◁ₗ[π, Shared κ] #rv @ v.(eltv_ltype)) ∗
         (∀ rte' (lte' : ltype rte') (rfn' : option rte') (re' : rte') r',
          ⌜is_xrfn r'⌝ -∗
          ⌜enum_tag en r' = Some v.(eltv_tag)⌝ -∗
          ⌜enum_ltype_variant_rfn en r'
            (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn') re'⌝ -∗
          ⌜syn_type_has_layout (ltype_st lte') variant_ly⌝ -∗
          lty_of_ty_own (int el.(el_tag_it)) (Shared κ) π
            (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
          (l +ₗ data_offset) ◁ₗ[π, Shared κ] #re' @ lte' ={F}=∗
          l ◁ₗ[π, Shared κ] #r' @
             EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn'))).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_enum_unfold /enum_ltype_own.
    iDestruct "Hb" as "(%el & %Halg & %Hly & #Hlb & %Hconc & %r' & -> & #Hb)".
    iExists el. do 2 (iSplitR; first done). iSplitR ""; first iFrame "Hlb".
    iMod (fupd_mask_mono with "Hb") as "Hb'"; first done.
    iModIntro.
    iDestruct "Hb'" as "(%Hxrfn & %variant_ly & %Hvariant & %Hst & %Htag & #Htag & #Htag_pad & #Hpayload & #Htail)".
    iExists variant_ly. do 4 (iSplitR; first done).
    iSplitR; first iFrame "Htag".
    iSplitR; first iFrame "Hpayload".
    iIntros (rte' lte' rfn' re' rnew) "%Hxrfn_new %Htag_new %Hrfn_new %Hst_new #Htag' #Hpayload'".
    iModIntro.
    rewrite ltype_own_enum_unfold /enum_ltype_own.
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iSplitR. { iPureIntro. apply place_rfn_is_concrete_in. }
    iExists rnew. iSplitR; first done.
    iModIntro. iModIntro.
    iSplitR; first done.
    iEval (rewrite /interp_enum_ltype_variant decide_True //).
    iExists variant_ly. do 3 (iSplitR; first done). iFrame "#". done.
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
        ∃ rv, ⌜enum_ltype_variant_rfn en r v rv⌝ ∗
          (l +ₗ data_offset) ◁ₗ[π, Owned] #rv @ v.(eltv_ltype) ∗
          logical_step F
          (lty_of_ty_own (int el.(el_tag_it)) Owned π
              (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
            (l +ₗ data_offset) ◁ₗ[π, Owned] #rv @ v.(eltv_ltype) ={F}=∗
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
    iDestruct "Hpayload" as "(%rv & %Hrfn_payload & Hpayload)".
    iSplitL "Htag"; first iExact "Htag".
    iExists rv. iSplit; first done. iFrame "Hpayload".
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hcred' !> Htag Hpayload".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (fupd_mask_mono with "(Hb_cl Hb_back Hcred1 [Hauth Htag Htag_pad Hpayload Htail])") as "(Hb & Htok)"; first done.
    { iNext. iExists r. iFrame. iModIntro. do 3 (iSplit; first done). done. }
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

  Definition enum_ltype_uniq_core_body {rt} (en : enum rt)
      (variant : option enum_ltype_variant) (el : enum_layout) π r l : iProp Σ :=
    ∃ variant_ly,
      let v := interp_enum_ltype_variant en variant r in
      ⌜enum_ltype_variant_compat en r v⌝ ∗
      ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
      ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
      lty_of_ty_own (int el.(el_tag_it)) Owned π
        (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
      lty_of_ty_own (uninit (LiteralSynType
        (Layout (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it))) 0))) Owned π
        (PlaceIn ()) (l +ₗ ly_size (it_layout el.(el_tag_it))) ∗
      (∃ rv : v.(eltv_rt), ⌜enum_ltype_variant_rfn en r v rv⌝ ∗
        ltype_own_core v.(eltv_ltype) Owned π (PlaceIn rv) (l +ₗ el.(el_data_offset))) ∗
      lty_of_ty_own (uninit (LiteralSynType
        (Layout (el.(el_size) - el.(el_data_offset) - ly_size variant_ly) 0))) Owned π
        (PlaceIn ()) (l +ₗ el.(el_data_offset) +ₗ ly_size variant_ly).

  Definition enum_ltype_uniq_core_bor_body {rt} (en : enum rt)
      (variant : option enum_ltype_variant) (el : enum_layout) γ π l : iProp Σ :=
    ∃ r, gvar_auth γ r ∗ |={lftE}=> enum_ltype_uniq_core_body en variant el π r l.

  Definition enum_ltype_uniq_normal_body {rt} (en : enum rt)
      (variant : option enum_ltype_variant) (el : enum_layout) π r l : iProp Σ :=
    ∃ variant_ly,
      let v := interp_enum_ltype_variant en variant r in
      ⌜enum_ltype_variant_compat en r v⌝ ∗
      ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
      ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
      lty_of_ty_own (int el.(el_tag_it)) Owned π
        (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
      lty_of_ty_own (uninit (LiteralSynType
        (Layout (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it))) 0))) Owned π
        (PlaceIn ()) (l +ₗ ly_size (it_layout el.(el_tag_it))) ∗
      (∃ rv : v.(eltv_rt), ⌜enum_ltype_variant_rfn en r v rv⌝ ∗
        (l +ₗ el.(el_data_offset)) ◁ₗ[π, Owned] #rv @ v.(eltv_ltype)) ∗
      lty_of_ty_own (uninit (LiteralSynType
        (Layout (el.(el_size) - el.(el_data_offset) - ly_size variant_ly) 0))) Owned π
        (PlaceIn ()) (l +ₗ el.(el_data_offset) +ₗ ly_size variant_ly).

  Lemma enum_ltype_uniq_core_body_core {rt} (en : enum rt) variant el π r l :
    enum_ltype_uniq_core_body en (enum_ltype_variant_core <$> variant) el π r l ⊣⊢
    enum_ltype_uniq_core_body en variant el π r l.
  Proof.
    rewrite /enum_ltype_uniq_core_body interp_enum_ltype_variant_core
      /enum_ltype_variant_core /= ltype_core_syn_type_eq.
    iSplit; iIntros "Hb";
      iDestruct "Hb" as "(%ly & %Hcompat & %Hlook & %Hst & Htag & Hpad & Hpayload & Htail)";
      iExists ly; do 3 (iSplit; first done); iFrame "Htag Hpad Htail";
      iDestruct "Hpayload" as "(%rv & %Hrfn & Hpayload)"; iExists rv.
    - change (enum_ltype_variant_rfn en r
        (interp_enum_ltype_variant en variant r) rv) in Hrfn.
      iSplit; first done.
      iEval (rewrite ltype_own_core_equiv ltype_core_idemp) in "Hpayload".
      iEval (rewrite ltype_own_core_equiv). done.
    - iSplit.
      { iPureIntro. change (enum_ltype_variant_rfn en r
          (interp_enum_ltype_variant en variant r) rv). exact Hrfn. }
      iEval (rewrite ltype_own_core_equiv) in "Hpayload".
      iEval (rewrite ltype_own_core_equiv ltype_core_idemp). done.
  Qed.

  Lemma enum_ltype_uniq_normal_body_core {rt} (en : enum rt) variant el π r l :
    enum_ltype_uniq_normal_body en (enum_ltype_variant_core <$> variant) el π r l ⊣⊢
    enum_ltype_uniq_core_body en variant el π r l.
  Proof.
    rewrite /enum_ltype_uniq_normal_body /enum_ltype_uniq_core_body
      interp_enum_ltype_variant_core /enum_ltype_variant_core /= ltype_core_syn_type_eq.
    iSplit; iIntros "Hb";
      iDestruct "Hb" as "(%ly & %Hcompat & %Hlook & %Hst & Htag & Hpad & Hpayload & Htail)";
      iExists ly; do 3 (iSplit; first done); iFrame "Htag Hpad Htail";
      iDestruct "Hpayload" as "(%rv & %Hrfn & Hpayload)"; iExists rv.
    - change (enum_ltype_variant_rfn en r
        (interp_enum_ltype_variant en variant r) rv) in Hrfn.
      iSplit; first done. iEval (rewrite ltype_own_core_equiv). done.
    - iSplit.
      { iPureIntro. change (enum_ltype_variant_rfn en r
          (interp_enum_ltype_variant en variant r) rv). exact Hrfn. }
      iEval (rewrite ltype_own_core_equiv) in "Hpayload". done.
  Qed.

  Lemma enum_ltype_uniq_core_body_to_owned {rt} (en : enum rt) variant el π r l :
    use_enum_layout_alg en.(enum_els) = Some el →
    l `has_layout_loc` el →
    loc_in_bounds l 0 el.(el_size) -∗
    enum_ltype_uniq_core_body en variant el π r l -∗
    l ◁ₗ[π, Owned] #r @ ltype_core (EnumLtype en variant).
  Proof.
    iIntros (Halg Hly) "#Hlb Hb".
    iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own).
    iExists el. do 2 (iSplitR; first done). iSplitR; first done.
    iExists r. iSplit; first done. iModIntro.
    iDestruct "Hb" as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Hpad & Hpayload & Htail)".
    iExists variant_ly.
    rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /= ltype_core_syn_type_eq.
    iSplit; first (iPureIntro; exact (proj1 Hcompat)).
    do 2 (iSplit; first done). iFrame "Htag Hpad Htail".
    iDestruct "Hpayload" as "(%rv & %Hrfn & Hpayload)".
    iExists rv. iSplit; first done. iEval (rewrite ltype_own_core_equiv) in "Hpayload". done.
  Qed.

  Lemma enum_ltype_owned_to_uniq_core_body_with_compat {rt} (en : enum rt) variant el π r l :
    use_enum_layout_alg en.(enum_els) = Some el →
    enum_ltype_variant_compat en r (interp_enum_ltype_variant en variant r) →
    l ◁ₗ[π, Owned] #r @ ltype_core (EnumLtype en variant) -∗
    |={lftE}=> enum_ltype_uniq_core_body en variant el π r l.
  Proof.
    iIntros (Halg Hcompat) "Hb".
    iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own) in "Hb".
    iDestruct "Hb" as "(%el' & %Halg' & _ & _ & %r' & -> & Hb)".
    assert (el' = el) as -> by congruence.
    iEval (rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /=
      ltype_core_syn_type_eq) in "Hb".
    iMod "Hb" as "(%variant_ly & %Htag & %Hvariant & %Hst & Htag & Hpad & Hpayload & Htail)".
    iModIntro. iExists variant_ly.
    iSplit; first done.
    do 2 (iSplit; first done). iFrame "Htag Hpad Htail".
    iDestruct "Hpayload" as "(%rv & %Hrfn & Hpayload)".
    iExists rv. iSplit; first done. iEval (rewrite ltype_own_core_equiv). done.
  Qed.

  Lemma enum_ltype_owned_to_uniq_core_body {rt} (en : enum rt) variant el π r l :
    use_enum_layout_alg en.(enum_els) = Some el →
    (enum_ltype_variant_tag_compat en r (interp_enum_ltype_variant en variant r) →
      enum_ltype_variant_compat en r (interp_enum_ltype_variant en variant r)) →
    l ◁ₗ[π, Owned] #r @ ltype_core (EnumLtype en variant) -∗
    |={lftE}=> enum_ltype_uniq_core_body en variant el π r l.
  Proof.
    iIntros (Halg Hcompat) "Hb".
    iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own) in "Hb".
    iDestruct "Hb" as "(%el' & %Halg' & _ & _ & %r' & -> & Hb)".
    assert (el' = el) as -> by congruence.
    iEval (rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /=
      ltype_core_syn_type_eq) in "Hb".
    iMod "Hb" as "(%variant_ly & %Htag & %Hvariant & %Hst & Htag & Hpad & Hpayload & Htail)".
    iModIntro. iExists variant_ly.
    iSplit; first (iPureIntro; exact (Hcompat Htag)).
    do 2 (iSplit; first done). iFrame "Htag Hpad Htail".
    iDestruct "Hpayload" as "(%rv & %Hrfn & Hpayload)".
    iExists rv. iSplit; first done. iEval (rewrite ltype_own_core_equiv). done.
  Qed.

  (* Close an updated payload while retaining the unique borrow contract.
     Core equality converts ownership; compatibility equivalence separately
     preserves the pure validity condition in the pinned borrow body. *)
  Lemma enum_ltype_acc_uniq_update {rt} F π
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
        ∃ rv, ⌜enum_ltype_variant_rfn en r v rv⌝ ∗
          (l +ₗ data_offset) ◁ₗ[π, Owned] #rv @ v.(eltv_ltype) ∗
          logical_step F
          ((∀ bmin rte' (lte' : ltype rte') (rfn' : option rte') rnew,
            place_update_kind_incl bmin (UpdUniq [κ]) -∗
            let variant' := Some (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn') in
            ∀ re' : rte',
            ⌜enum_tag en rnew = Some v.(eltv_tag)⌝ -∗
            ⌜enum_ltype_variant_compat en rnew
              (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn')⌝ -∗
            ⌜enum_ltype_variant_rfn en rnew
              (mk_enum_ltype_variant v.(eltv_tag) rte' lte' rfn') re'⌝ -∗
            ⌜syn_type_has_layout (ltype_st lte') variant_ly⌝ -∗
            ⌜∀ r0,
              enum_ltype_variant_compat en r0
                 (interp_enum_ltype_variant en variant' r0) ↔
              enum_ltype_variant_compat en r0
                (interp_enum_ltype_variant en variant r0)⌝ -∗
            lty_of_ty_own (int el.(el_tag_it)) Owned π
              (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
            (l +ₗ data_offset) ◁ₗ[π, Owned] #re' @ lte' -∗
            typed_place_cond bmin (EnumLtype en variant) (EnumLtype en variant') ={F}=∗
            l ◁ₗ[π, Uniq κ γ] #rnew @ EnumLtype en variant' ∗ R ∗
            typed_place_cond bmin (EnumLtype en variant) (EnumLtype en variant')) ∧
          (∀ rte' (lte' : ltype rte') (re' : rte'),
            ⌜syn_type_has_layout (ltype_st lte') variant_ly⌝ -∗
            ⌜∀ r0,
              enum_ltype_variant_tag_compat en r0
                (interp_enum_ltype_variant en variant r0) →
              enum_ltype_variant_compat en r0
                (interp_enum_ltype_variant en variant r0)⌝ -∗
            lty_of_ty_own (int el.(el_tag_it)) Owned π
              (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l -∗
            (l +ₗ data_offset) ◁ₗ[π, Owned] #re' @ lte' -∗
            l ◁ₗ[π, Uniq κ γ] #r @
              OpenedLtype
                (EnumLtype en (Some (mk_enum_ltype_variant
                  v.(eltv_tag) rte' lte' (Some re'))))
                (EnumLtype en variant) (EnumLtype en variant)
                (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#(LFT & LLCTX) Htok HclR Hb".
    iEval (rewrite ltype_own_enum_unfold /enum_ltype_own) in "Hb".
    iDestruct "Hb" as "(%el & %Halg & %Hly & #Hlb & Hcred & Hrfn & Hb)".
    iPoseProof "Hlb" as "#Hlb2".
    iExists el. do 2 (iSplitR; first done). iSplitR "Hlb2 Hcred Hrfn Hb Htok HclR"; first iFrame "Hlb".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod "Hb" as "Hb".
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ' & #Hincl & Hb & _ & Hb_cl)"; first done.
    iMod "HF_cl" as "_".
    iDestruct "Hcred" as "([Hcred1 Hcred] & Hat)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iModIntro.
    iDestruct "Hb" as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Htag_pad & Hpayload & Htail)".
    iDestruct "Hpayload" as "(%rv & %Hrfn_payload & Hpayload)".
    iExists variant_ly. do 3 (iSplitR; first done).
    iSplitL "Htag"; first iExact "Htag".
    iExists rv. iSplit; first done. iFrame "Hpayload".
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hcred' !>". iSplit.
    - iIntros (bmin rte' lte' rfn' rnew) "#Hincl_k".
    iIntros (re') "%Htag' %Hcompat' %Hrfn' %Hst' %Hcompat_back Htag Hpayload #Hcond".
    set (variant' := Some (mk_enum_ltype_variant
      (interp_enum_ltype_variant en variant r).(eltv_tag) rte' lte' rfn')).
    iPoseProof (typed_place_cond_incl with "Hincl_k Hcond") as "#Hcond_uniq".
    iPoseProof (typed_place_cond_uniq_core_eq with "Hcond_uniq") as "#Heq".
    iMod (gvar_update rnew with "Hauth Hrfn") as "(Hauth & Hrfn)".
    set (V := (∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=>
      ∃ variant_ly',
      let v'' := interp_enum_ltype_variant en variant' r' in
      ⌜enum_ltype_variant_compat en r' v''⌝ ∗
      ⌜enum_variant_lookup el.(el_variants) v''.(eltv_tag) = Some variant_ly'⌝ ∗
      ⌜syn_type_has_layout (ltype_st v''.(eltv_ltype)) variant_ly'⌝ ∗
      lty_of_ty_own (int el.(el_tag_it)) Owned π
        (PlaceIn (els_lookup_tag en.(enum_els) v''.(eltv_tag))) l ∗
      lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it))) 0))) Owned π
        (PlaceIn ()) (l +ₗ ly_size (it_layout el.(el_tag_it))) ∗
      (∃ rv' : v''.(eltv_rt), ⌜enum_ltype_variant_rfn en r' v'' rv'⌝ ∗
        (l +ₗ el.(el_data_offset)) ◁ₗ[π, Owned] #rv' @ v''.(eltv_ltype)) ∗
      lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - el.(el_data_offset) - ly_size variant_ly') 0))) Owned π
        (PlaceIn ()) (l +ₗ el.(el_data_offset) +ₗ ly_size variant_ly'))%I).
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Htag Htag_pad Hpayload Htail]") as "(Hb & Htok)".
    { iNext. iIntros "(%r0 & Hauth & Hb) Hdead".
      iModIntro. iNext. iExists r0. iFrame "Hauth".
      iMod "Hb" as "(%variant_ly0 & %Hcompat0 & %Hvariant0 & %Hst0 & Htag0 & Htag_pad0 & Hpayload0 & Htail0)".
      iPoseProof (typed_place_cond_uniq_core_eq with "Hcond_uniq") as "#Heq_cb".
      iPoseProof (typed_place_cond_uniq_unblockable with "Hcond_uniq") as "#Hub_cb".
      iDestruct "Hub_cb" as "[_ Hub_owned]".
      pose proof Hcompat0 as [Htagcompat0 _].
      iDestruct ("Heq_cb" $! Owned (#r0)) as "[_ [Hincl_core _]]".
      iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
      iMod ("Hub_owned" $! π (#r0) l with "[Hdead] [Htag0 Htag_pad0 Hpayload0 Htail0]") as "Hb".
      { by iApply lft_dead_list_singleton. }
      { rewrite ltype_own_enum_unfold /enum_ltype_own.
        iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
        iExists r0. iSplit; first done. iModIntro. iExists variant_ly0.
        do 3 (iSplit; first done). iFrame. }
      iEval (rewrite ltype_own_core_equiv) in "Hb".
      iMod ("Hincl_core" with "Hb") as "Hb".
      iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own) in "Hb".
      iDestruct "Hb" as "(%el' & %Halg' & _ & _ & %r0' & -> & Hb)".
      assert (el' = el) as -> by congruence.
      iEval (rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /=
        ltype_core_syn_type_eq) in "Hb".
      iMod "Hb" as "(%variant_ly1 & %Htag1 & %Hvariant1 & %Hst1 & Htag1 & Htag_pad1 & Hpayload1 & Htail1)".
      iModIntro. iExists variant_ly1.
      iSplit; first (iPureIntro; exact (proj1 (Hcompat_back r0') Hcompat0)).
      do 2 (iSplit; first done). iFrame "Htag1 Htag_pad1 Htail1".
      iDestruct "Hpayload1" as "(%rv1 & %Hrfn1 & Hpayload1)".
      iExists rv1. iSplit; first done.
      iEval (rewrite ltype_own_core_equiv). done. }
    { iModIntro. iExists rnew. iFrame "Hauth". iModIntro.
      iExists variant_ly.
      rewrite /variant' interp_enum_ltype_variant_Some_match; last done.
      do 3 (iSplitR; first done). iFrame.
      done. }
    iMod ("HclR" with "Htok") as "$".
    iMod "HF_cl" as "_". iModIntro.
    iSplitL "Hat Hcred Hcred' Hrfn Hb".
    { rewrite ltype_own_enum_unfold /enum_ltype_own.
      iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb2".
      iFrame "Hrfn". iSplitL "Hat Hcred Hcred'".
      { unfold have_creds; simpl. iFrame.
        iApply tr_weaken; last done. unfold num_laters_per_step; lia. }
      iModIntro. iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
      subst V. iApply (pinned_bor_iff with "[] [] Hb").
      { iNext. iModIntro. iSplit; iIntros "$". }
      iNext. iModIntro. iSplit.
      all: iIntros "(%r0 & Hauth & Hb)"; iExists r0; iFrame "Hauth";
        iMod "Hb" as "(%ly0 & %Hcompat0 & %Hlook0 & %Hst0 & Htag0 & Hpad0 & Hpayload0 & Htail0)".
      - iDestruct ("Heq" $! Owned (#r0)) as "[[Hconv _] _]".
        iMod ("Hconv" $! π l with "[Htag0 Hpad0 Hpayload0 Htail0]") as "Hb".
        { iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own).
          iExists el. do 2 (iSplitR; first done). iSplitR; first done.
          iExists r0. iSplit; first done. iModIntro. iExists ly0.
          rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /= ltype_core_syn_type_eq.
          iSplit; first (iPureIntro; exact (proj1 Hcompat0)).
          do 2 (iSplit; first done). iFrame "Htag0 Hpad0 Htail0".
          iDestruct "Hpayload0" as "(%rv0 & %Hrfn0 & Hp)".
          iExists rv0. iSplit; first done. iEval (rewrite ltype_own_core_equiv) in "Hp". done. }
        iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own) in "Hb".
        iDestruct "Hb" as "(%el' & %Halg' & _ & _ & %r0' & -> & Hb)".
        assert (el' = el) as -> by congruence.
        iEval (rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /= ltype_core_syn_type_eq) in "Hb".
        iMod "Hb" as "(%ly1 & %Ht1 & %Hl1 & %Hs1 & Ht & Hp & Hdata & Htail)".
        iModIntro. iExists ly1.
        iSplit; first (iPureIntro; exact (proj2 (Hcompat_back r0') Hcompat0)).
        do 2 (iSplit; first done). iFrame "Ht Hp Htail".
        iDestruct "Hdata" as "(%rv0 & %Hrfn0 & Hdata)".
        iExists rv0. iSplit; first done. iEval (rewrite ltype_own_core_equiv). done.
      - iDestruct ("Heq" $! Owned (#r0)) as "[_ [Hconv _]]".
        iMod ("Hconv" $! π l with "[Htag0 Hpad0 Hpayload0 Htail0]") as "Hb".
        { iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own).
          iExists el. do 2 (iSplitR; first done). iSplitR; first done.
          iExists r0. iSplit; first done. iModIntro. iExists ly0.
          rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /= ltype_core_syn_type_eq.
          iSplit; first (iPureIntro; exact (proj1 Hcompat0)).
          do 2 (iSplit; first done). iFrame "Htag0 Hpad0 Htail0".
          iDestruct "Hpayload0" as "(%rv0 & %Hrfn0 & Hp)".
          iExists rv0. iSplit; first done. iEval (rewrite ltype_own_core_equiv) in "Hp". done. }
        iEval (rewrite ltype_core_enum ltype_own_enum_unfold /enum_ltype_own) in "Hb".
        iDestruct "Hb" as "(%el' & %Halg' & _ & _ & %r0' & -> & Hb)".
        assert (el' = el) as -> by congruence.
        iEval (rewrite interp_enum_ltype_variant_core /enum_ltype_variant_core /= ltype_core_syn_type_eq) in "Hb".
        iMod "Hb" as "(%ly1 & %Ht1 & %Hl1 & %Hs1 & Ht & Hp & Hdata & Htail)".
        iModIntro. iExists ly1.
        iSplit; first (iPureIntro; exact (proj1 (Hcompat_back r0') Hcompat0)).
        do 2 (iSplit; first done). iFrame "Ht Hp Htail".
        iDestruct "Hdata" as "(%rv0 & %Hrfn0 & Hdata)".
        iExists rv0. iSplit; first done. iEval (rewrite ltype_own_core_equiv). done. }
      iFrame "Hcond".
    - iIntros (rte' lte' re') "%Hst' %Hcompat_orig Htag Hpayload".
      set (variant_cur := Some (mk_enum_ltype_variant
        (interp_enum_ltype_variant en variant r).(eltv_tag) rte' lte' (Some re'))).
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with
        "Hrfn Hauth Hcred1 Hat Hincl HclR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (r0) "Hauth Hcore".
        simp_ltypes. iExists r0. iFrame "Hauth".
        iMod "Hcore" as "Hcore".
        iEval (rewrite -ltype_core_enum) in "Hcore".
        iApply (enum_ltype_owned_to_uniq_core_body en variant el π r0 l
          Halg (Hcompat_orig r0) with "Hcore"). }
      { iIntros (r0) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_enum_unfold /enum_ltype_own.
        iExists el. do 2 (iSplitR; first done). iSplitR; first done.
        iSplitL "Hat Hcred Hcred'".
        { unfold have_creds; simpl. iFrame.
          iApply tr_weaken; last done. unfold num_laters_per_step; lia. }
        iFrame "Hobs". iModIntro.
        iApply (pinned_bor_iff with "[] [] Hp").
        all: iNext; iModIntro; iSplit;
          iIntros "(%r1 & Hauth & Hb)"; iExists r1; iFrame "Hauth";
          iMod "Hb" as "Hb".
        - iModIntro.
          iAssert (enum_ltype_uniq_core_body en variant el π r1 l) with "[Hb]" as "Hb"; first done.
          iAssert (enum_ltype_uniq_normal_body en (enum_ltype_variant_core <$> variant) el π r1 l)
            with "[Hb]" as "Hb".
          { iApply (bi.equiv_entails_1_2 _ _ (enum_ltype_uniq_normal_body_core en variant el π r1 l)). done. }
          iExact "Hb".
        - iModIntro.
          iAssert (enum_ltype_uniq_normal_body en (enum_ltype_variant_core <$> variant) el π r1 l)
            with "[Hb]" as "Hb"; first done.
          iAssert (enum_ltype_uniq_core_body en variant el π r1 l) with "[Hb]" as "Hb".
          { iApply (bi.equiv_entails_1_1 _ _ (enum_ltype_uniq_normal_body_core en variant el π r1 l)). done. }
          iExact "Hb".
        - iModIntro.
          iAssert (enum_ltype_uniq_core_body en variant el π r1 l) with "[Hb]" as "Hb"; first done.
          iAssert (enum_ltype_uniq_core_body en (enum_ltype_variant_core <$> variant) el π r1 l)
            with "[Hb]" as "Hb".
          { iApply (bi.equiv_entails_1_2 _ _ (enum_ltype_uniq_core_body_core en variant el π r1 l)). done. }
          iExact "Hb".
        - iModIntro.
          iAssert (enum_ltype_uniq_core_body en (enum_ltype_variant_core <$> variant) el π r1 l)
            with "[Hb]" as "Hb"; first done.
          iAssert (enum_ltype_uniq_core_body en variant el π r1 l) with "[Hb]" as "Hb".
          { iApply (bi.equiv_entails_1_1 _ _ (enum_ltype_uniq_core_body_core en variant el π r1 l)). done. }
          iExact "Hb". }
      { rewrite ltype_own_enum_unfold /enum_ltype_own.
        iExists el. do 2 (iSplitR; first done). iSplitR; first done.
        iExists r. iSplit; first done. iModIntro. iExists variant_ly.
        rewrite /variant_cur interp_enum_ltype_variant_Some_match;
          last exact (proj1 Hcompat).
        iSplit; first (iPureIntro; exact (proj1 Hcompat)).
        iSplit; first done. iSplit; first done. iFrame "Htag Htag_pad Htail".
        iExists re'. iSplit; first done. done. }
  Qed.

End accessors.

Section subltype.
  Context `{!typeGS Σ}.

  Definition enum_ltype_variant_ltype_incl' b {rt1 rt2}
      (en1 : enum rt1) r1 (v1 : enum_ltype_variant)
      (en2 : enum rt2) r2 (v2 : enum_ltype_variant) : iProp Σ :=
    ∀ rv1 rv2,
      ⌜enum_ltype_variant_rfn en1 r1 v1 rv1⌝ -∗
      ⌜enum_ltype_variant_rfn en2 r2 v2 rv2⌝ -∗
      ltype_incl' b (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype).

  Definition enum_ltype_variant_ltype_incl b {rt1 rt2}
      (en1 : enum rt1) r1 (v1 : enum_ltype_variant)
      (en2 : enum rt2) r2 (v2 : enum_ltype_variant) : iProp Σ :=
    ∀ rv1 rv2,
      ⌜enum_ltype_variant_rfn en1 r1 v1 rv1⌝ -∗
      ⌜enum_ltype_variant_rfn en2 r2 v2 rv2⌝ -∗
      ltype_incl b (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype).

  Definition enum_ltype_variant_ltype_eq b {rt1 rt2}
      (en1 : enum rt1) r1 (v1 : enum_ltype_variant)
      (en2 : enum rt2) r2 (v2 : enum_ltype_variant) : iProp Σ :=
    ∀ rv1 rv2,
      ⌜enum_ltype_variant_rfn en1 r1 v1 rv1⌝ -∗
      ⌜enum_ltype_variant_rfn en2 r2 v2 rv2⌝ -∗
      ltype_eq b (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype).

  Local Lemma enum_ltype_incl'_owned_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    enum_ltype_variant_ltype_incl' Owned en1 r1 v1 en2 r2 v2 -∗
    ltype_incl' Owned (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst. iIntros "#Hincl !>" (π l).
    destruct Hcompat as [Hcompat [rv2 [Heq2 [Hrfn2 Hcanon2]]]].
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %r & -> & Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iExists r2. iR.
    iMod "Hb" as "(%ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb & Htail)".
    fold v1 in Hlook, Hst1 |- *. fold v2.
    iDestruct "Hb" as "(%rv1 & %Hrfn1 & Hb)".
    iMod ("Hincl" $! rv1 rv2 with "[] [] Hb") as "Hb"; [done.. |].
    iModIntro. iModIntro.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame. done.
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
    enum_ltype_variant_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    enum_ltype_variant_ltype_incl Owned en1 r1 v1 en2 r2 v2 -∗
    ltype_incl Owned (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst. iIntros "#Hincl".
    iModIntro. iSplit.
    - iApply enum_ltype_incl'_owned_in;
        [exact Hels | exact Htag | exact Hcompat | exact Hst |].
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iDestruct ("Hincl" $! rv1 rv2 with "[] []") as "[Hincl' _]"; [done.. |].
      done.
    - rewrite !ltype_core_enum.
      iApply enum_ltype_incl'_owned_in; first done;
        rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      + done.
      + done.
      + rewrite !ltype_core_syn_type_eq. done.
      + iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
        iDestruct ("Hincl" $! rv1 rv2 with "[] []") as "[_ Hcore]"; [done.. |].
        done.
  Qed.
  Lemma enum_ltype_incl_owned_in_inj {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem rp :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    enum_els en1 = enum_els en2 →
    enum_tag_ty_inj en2 v1.(eltv_tag) = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st (OfTy sem.(enum_tag_sem_ty)) →
    ∀ rv, enum_ltype_variant_rfn en1 r1 v1 rv →
    ltype_incl Owned (#rv) (#rp) v1.(eltv_ltype) (OfTy sem.(enum_tag_sem_ty)) -∗
    ltype_incl Owned (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1) (EnumLtype en2 None).
  Proof.
    intros v1 Hels Hsem Hst rv Hrfn. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 v1.(eltv_tag) sem Hel rp) as [Htag Heq Hr].
    pose proof (enum_tag_type_eq' en2 _ _ _ Htag Hsem) as Hty.
    iApply enum_ltype_incl_owned_in; first done.
    - simpl. rewrite /canonical_enum_ltype_variant /= (enum_tag'_Some _ _ _ Htag). done.
    - split.
      + rewrite /enum_ltype_variant_tag_compat /= (enum_tag'_Some _ _ _ Htag). exact Htag.
      + exists (enum_r en2 (sem.(enum_tag_rt_inj) rp)), eq_refl. split; done.
    - simpl. rewrite -Hty. generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem).
      intros Heq'. destruct Heq'. done.
    - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      have -> : rv1 = rv by eapply enum_ltype_variant_rfn_unique.
      change (rv2 = enum_r en2 (sem.(enum_tag_rt_inj) rp)) in Hrfn2. subst rv2.
      simpl. rewrite Hr -Hty.
      generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem) as Heq'.
      intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
      rewrite (UIP_refl _ _ Heq0). done.
  Qed.

  Lemma enum_ltype_incl_owned_in_inj_none {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem rp tag
      (lt : ltype rte) (Heq : sem.(enum_tag_sem_rt) = rte) :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let rp' : rte := eq_rect _ RT_rt rp _ Heq in
    enum_els en1 = enum_els en2 →
    v1.(eltv_tag) = tag →
    enum_tag_ty_inj en2 tag = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st lt →
    ∀ rv, enum_ltype_variant_rfn en1 r1 v1 rv →
    ltype_incl Owned (#rv) (#rp') v1.(eltv_ltype) lt -∗
    ltype_incl Owned (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt None))).
  Proof.
    destruct Heq. simpl.
    set (v1 := interp_enum_ltype_variant en1 variant1 r1).
    intros Hels Htag Hsem Hst rv Hrfn. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 tag sem Hel rp) as [Htag2 Heq2 Hr].
    iApply enum_ltype_incl_owned_in; first done.
    - rewrite interp_enum_ltype_variant_Some_match; done.
    - rewrite interp_enum_ltype_variant_Some_match; last done.
      split; first done.
      eexists rp.
      eexists (f_equal RT_rt (eq_sym Heq2)). split.
      + simpl. eexists (f_equal RT_rt (eq_sym Heq2)).
        erewrite Hr. generalize Heq2. intros []. done.
      + erewrite Hr. generalize Heq2. intros []. done.
    - rewrite interp_enum_ltype_variant_Some_match; last done. exact Hst.
    - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      rewrite interp_enum_ltype_variant_Some_match in rv2, Hrfn2 |- *; last done.
      have -> : rv1 = rv by eapply enum_ltype_variant_rfn_unique.
      have -> : rv2 = rp.
      { eapply enum_ltype_variant_rfn_unique; first exact Hrfn2.
        simpl. eexists (f_equal RT_rt (eq_sym Heq2)).
        erewrite Hr. generalize Heq2. intros []. done. }
      done.
  Qed.

  Lemma enum_ltype_incl_owned_in_inj_some {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem tag
      (lt : ltype rte) (re : rte) (Heq : sem.(enum_tag_sem_rt) = rte) :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let rp : sem.(enum_tag_sem_rt) := eq_rect _ RT_rt re _ (eq_sym Heq) in
    enum_els en1 = enum_els en2 →
    v1.(eltv_tag) = tag →
    enum_tag_ty_inj en2 tag = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st lt →
    ∀ rv, enum_ltype_variant_rfn en1 r1 v1 rv →
    ltype_incl Owned (#rv) (#re) v1.(eltv_ltype) lt -∗
    ltype_incl Owned (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt (Some re)))).
  Proof.
    destruct Heq. simpl.
    set (v1 := interp_enum_ltype_variant en1 variant1 r1).
    intros Hels Htag Hsem Hst rv Hrfn. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 tag sem Hel re) as [Htag2 Heq2 Hr].
    iApply enum_ltype_incl_owned_in; first done.
    - rewrite interp_enum_ltype_variant_Some_match; done.
    - rewrite interp_enum_ltype_variant_Some_match; last done.
      split; first done. eexists re, (f_equal RT_rt (eq_sym Heq2)). split; first done.
      erewrite Hr. generalize Heq2. intros []. done.
    - rewrite interp_enum_ltype_variant_Some_match; last done. exact Hst.
    - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      rewrite interp_enum_ltype_variant_Some_match in rv2, Hrfn2 |- *; last done.
      have -> : rv1 = rv by eapply enum_ltype_variant_rfn_unique.
      have -> : rv2 = re by eapply enum_ltype_variant_rfn_unique; [exact Hrfn2 | done].
      done.
  Qed.
End subltype.

Section uniform_subltype.
  Context `{!typeGS Σ}.

  Local Lemma enum_ltype_incl'_owned {rt} (en1 en2 : enum rt) variant1 variant2 r :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      enum_ltype_variant_ltype_incl' Owned en1 r' v1 en2 r' v2) -∗
    ltype_incl' Owned r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %r' & Hr & Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iExists r'. iFrame "Hr".
    iDestruct ("Hincl" $! r') as "(%Hcompat & %Hst & Hincl')".
    iMod "Hb" as "(%ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb & Htail)".
    destruct (Hcompat Hcompat1) as [Htag [Hcompat2 [rv2 [Heq2 [Hrfn2 Hcanon2]]]]].
    iDestruct "Hb" as "(%rv1 & %Hrfn1 & Hb)".
    iMod ("Hincl'" $! rv1 rv2 with "[] [] Hb") as "Hb"; [done.. |].
    iModIntro. iModIntro.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame.
    done.
  Qed.

  Lemma enum_ltype_incl_owned {rt} (en1 en2 : enum rt) variant1 variant2 r :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      enum_ltype_variant_ltype_incl Owned en1 r' v1 en2 r' v2) -∗
    ltype_incl Owned r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl". iModIntro. iSplit.
    - iApply enum_ltype_incl'_owned; first done.
      iIntros (r'). iDestruct ("Hincl" $! r') as "($ & $ & Hincl_payload)".
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iDestruct ("Hincl_payload" $! rv1 rv2 with "[] []") as "[Hincl' _]"; [done.. |]. done.
    - rewrite !ltype_core_enum. iApply enum_ltype_incl'_owned; first done.
      iIntros (r'). rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      rewrite !ltype_core_syn_type_eq.
      iDestruct ("Hincl" $! r') as "($ & $ & Hincl_payload)".
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iDestruct ("Hincl_payload" $! rv1 rv2 with "[] []") as "[_ Hcore]"; [done.. |]. done.
  Qed.
End uniform_subltype.

Section shared_subltype.
  Context `{!typeGS Σ}.

  Local Lemma enum_tag_rt_inj_is_xrfn {rt} (en : enum rt) tag sem rp :
    enum_tag_ty_inj en tag = Some sem →
    is_xrfn rp → is_xrfn (sem.(enum_tag_rt_inj) rp).
  Proof.
    intros Hsem Hxr.
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en tag sem Hel rp) as [Htag Heq Hr].
    apply (proj2 (enum_r_is_xrfn en _)). rewrite Hr.
    assert (eq_rect _ RT_rt rp _ Heq =
      eq_rect _ id rp _ (f_equal RT_rt Heq)) as Htransport.
    { clear Hr. destruct Heq. done. }
    rewrite Htransport.
    apply (proj1 (is_xrfn_transport_iff Heq (f_equal RT_rt Heq) rp)). done.
  Qed.

  Local Lemma enum_ltype_incl'_shared_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 κ :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    (∀ rv, enum_ltype_variant_rfn en2 r2 v2 rv → is_xrfn rv → is_xrfn r2) →
    enum_ltype_variant_ltype_incl' (Shared κ) en1 r1 v1 en2 r2 v2 -∗
    ltype_incl' (Shared κ) (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst Hcanonical. iIntros "#Hincl !>" (π l).
    destruct Hcompat as [Hcompat [rv2 [Heq2 [Hrfn2 Hcanon2]]]].
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %Hconc & %r & -> & #Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iSplitR; first (iPureIntro; apply place_rfn_is_concrete_in).
    iExists r2. iR. iModIntro.
    iMod "Hb" as "(%Hxr & %ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb' & Htail)".
    fold v1 in Hlook, Hst1 |- *. fold v2.
    iDestruct "Hb'" as "(%rv1 & %Hrfn1 & Hb')".
    iPoseProof ("Hincl" $! rv1 rv2 with "[] [] Hb'") as "#Hpayload2"; [done.. |].
    iMod (ltype_own_shared_is_xrfn with "Hpayload2") as "%Hxr2".
    iModIntro. iSplitR; first (iPureIntro; eapply Hcanonical; done).
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame.
    iExists rv2. iSplitR; first done. iExact "Hpayload2".
  Qed.

  Lemma enum_ltype_incl_shared_in {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 κ :
    enum_els en1 = enum_els en2 →
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2 in
    v1.(eltv_tag) = v2.(eltv_tag) →
    enum_ltype_variant_compat en2 r2 v2 →
    ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) →
    (∀ rv, enum_ltype_variant_rfn en2 r2 v2 rv → is_xrfn rv → is_xrfn r2) →
    enum_ltype_variant_ltype_incl (Shared κ) en1 r1 v1 en2 r2 v2 -∗
    ltype_incl (Shared κ) (#r1) (#r2) (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels v1 v2 Htag Hcompat Hst Hcanonical. iIntros "#Hincl".
    iModIntro. iSplit.
    - iApply enum_ltype_incl'_shared_in;
        [exact Hels | exact Htag | exact Hcompat | exact Hst | exact Hcanonical |].
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iDestruct ("Hincl" $! rv1 rv2 with "[] []") as "[Hincl' _]"; [done.. |]. done.
    - rewrite !ltype_core_enum.
      iApply enum_ltype_incl'_shared_in; first done;
        rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      + done.
      + done.
      + rewrite !ltype_core_syn_type_eq. done.
      + exact Hcanonical.
      + iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
        iDestruct ("Hincl" $! rv1 rv2 with "[] []") as "[_ Hcore]"; [done.. |]. done.
  Qed.

  Lemma enum_ltype_incl_shared_in_inj {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem rp κ :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    enum_els en1 = enum_els en2 →
    enum_tag_ty_inj en2 v1.(eltv_tag) = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st (OfTy sem.(enum_tag_sem_ty)) →
    ∀ rv, enum_ltype_variant_rfn en1 r1 v1 rv →
    ltype_incl (Shared κ) (#rv) (#rp) v1.(eltv_ltype) (OfTy sem.(enum_tag_sem_ty)) -∗
    ltype_incl (Shared κ) (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1) (EnumLtype en2 None).
  Proof.
    intros v1 Hels Hsem Hst rv Hrfn. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 v1.(eltv_tag) sem Hel rp) as [Htag Heq Hr].
    pose proof (enum_tag_type_eq' en2 _ _ _ Htag Hsem) as Hty.
    iApply enum_ltype_incl_shared_in; first done.
    - simpl. rewrite /canonical_enum_ltype_variant /= (enum_tag'_Some _ _ _ Htag). done.
    - split.
      + rewrite /enum_ltype_variant_tag_compat /= (enum_tag'_Some _ _ _ Htag). exact Htag.
      + exists (enum_r en2 (sem.(enum_tag_rt_inj) rp)), eq_refl. split; done.
    - simpl. rewrite -Hty. generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem).
      intros Heq'. destruct Heq'. done.
    - intros rv2 Hrfn2 Hxr2.
      change (rv2 = enum_r en2 (sem.(enum_tag_rt_inj) rp)) in Hrfn2.
      subst rv2. exact (proj2 (enum_r_is_xrfn en2 _) Hxr2).
    - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      have -> : rv1 = rv by eapply enum_ltype_variant_rfn_unique.
      change (rv2 = enum_r en2 (sem.(enum_tag_rt_inj) rp)) in Hrfn2. subst rv2.
      simpl. rewrite Hr -Hty.
      generalize (enum_tag_rt_eq en2 _ _ _ Htag Hsem) as Heq'.
      intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
      rewrite (UIP_refl _ _ Heq0). done.
  Qed.

  Lemma enum_ltype_incl_shared_in_inj_none {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem rp tag κ
      (lt : ltype rte) (Heq : sem.(enum_tag_sem_rt) = rte) :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let rp' : rte := eq_rect _ RT_rt rp _ Heq in
    enum_els en1 = enum_els en2 →
    v1.(eltv_tag) = tag →
    enum_tag_ty_inj en2 tag = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st lt →
    ∀ rv, enum_ltype_variant_rfn en1 r1 v1 rv →
    ltype_incl (Shared κ) (#rv) (#rp') v1.(eltv_ltype) lt -∗
    ltype_incl (Shared κ) (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt None))).
  Proof.
    destruct Heq. simpl.
    set (v1 := interp_enum_ltype_variant en1 variant1 r1).
    intros Hels Htag Hsem Hst rv Hrfn. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 tag sem Hel rp) as [Htag2 Heq2 Hr].
    iApply enum_ltype_incl_shared_in; first done.
    - rewrite interp_enum_ltype_variant_Some_match; done.
    - rewrite interp_enum_ltype_variant_Some_match; last done.
      split; first done.
      eexists rp.
      eexists (f_equal RT_rt (eq_sym Heq2)). split.
      + simpl. eexists (f_equal RT_rt (eq_sym Heq2)).
        erewrite Hr. generalize Heq2. intros []. done.
      + erewrite Hr. generalize Heq2. intros []. done.
    - rewrite interp_enum_ltype_variant_Some_match; last done. exact Hst.
    - intros rv2 Hrfn2 Hxr2.
      rewrite interp_enum_ltype_variant_Some_match in rv2, Hrfn2, Hxr2; last done.
      have Heqrv : rv2 = rp.
      { eapply enum_ltype_variant_rfn_unique; first exact Hrfn2.
        simpl. eexists (f_equal RT_rt (eq_sym Heq2)).
        erewrite Hr. generalize Heq2. intros []. done. }
      subst rv2.
      eapply enum_tag_rt_inj_is_xrfn; done.
    - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      rewrite interp_enum_ltype_variant_Some_match in rv2, Hrfn2 |- *; last done.
      have -> : rv1 = rv by eapply enum_ltype_variant_rfn_unique.
      have -> : rv2 = rp.
      { eapply enum_ltype_variant_rfn_unique; first exact Hrfn2.
        simpl. eexists (f_equal RT_rt (eq_sym Heq2)).
        erewrite Hr. generalize Heq2. intros []. done. }
      done.
  Qed.

  Lemma enum_ltype_incl_shared_in_inj_some {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 sem tag κ
      (lt : ltype rte) (re : rte) (Heq : sem.(enum_tag_sem_rt) = rte) :
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let rp : sem.(enum_tag_sem_rt) := eq_rect _ RT_rt re _ (eq_sym Heq) in
    enum_els en1 = enum_els en2 →
    v1.(eltv_tag) = tag →
    enum_tag_ty_inj en2 tag = Some sem →
    ltype_st v1.(eltv_ltype) = ltype_st lt →
    ∀ rv, enum_ltype_variant_rfn en1 r1 v1 rv →
    ltype_incl (Shared κ) (#rv) (#re) v1.(eltv_ltype) lt -∗
    ltype_incl (Shared κ) (#r1) (#(sem.(enum_tag_rt_inj) rp))
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt (Some re)))).
  Proof.
    destruct Heq. simpl.
    set (v1 := interp_enum_ltype_variant en1 variant1 r1).
    intros Hels Htag Hsem Hst rv Hrfn. iIntros "Hincl".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 tag sem Hel re) as [Htag2 Heq2 Hr].
    iApply enum_ltype_incl_shared_in; first done.
    - rewrite interp_enum_ltype_variant_Some_match; done.
    - rewrite interp_enum_ltype_variant_Some_match; last done.
      split; first done. eexists re, (f_equal RT_rt (eq_sym Heq2)). split; first done.
      erewrite Hr. generalize Heq2. intros []. done.
    - rewrite interp_enum_ltype_variant_Some_match; last done. exact Hst.
    - intros rv2 Hrfn2 Hxr2.
      rewrite interp_enum_ltype_variant_Some_match in rv2, Hrfn2, Hxr2; last done.
      have Heqrv : rv2 = re by eapply enum_ltype_variant_rfn_unique; [exact Hrfn2 | done].
      subst rv2.
      eapply enum_tag_rt_inj_is_xrfn; done.
    - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      rewrite interp_enum_ltype_variant_Some_match in rv2, Hrfn2 |- *; last done.
      have -> : rv1 = rv by eapply enum_ltype_variant_rfn_unique.
      have -> : rv2 = re by eapply enum_ltype_variant_rfn_unique; [exact Hrfn2 | done].
      done.
  Qed.

  Local Lemma enum_ltype_incl'_shared {rt} (en1 en2 : enum rt) variant1 variant2 r κ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      enum_ltype_variant_ltype_incl' (Shared κ) en1 r' v1 en2 r' v2) -∗
    ltype_incl' (Shared κ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & Hlb & %Hconc & %r' & Hr & #Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame "Hlb".
    iSplitR; first done. iExists r'. iFrame "Hr". iModIntro.
    iDestruct ("Hincl" $! r') as "(%Hcompat & %Hst & Hincl')".
    iMod "Hb" as "(%Hxr & %ly & %Hcompat1 & %Hlook & %Hst1 & Htag & Hpad & Hb' & Htail)".
    destruct (Hcompat Hcompat1) as [Htag [Hcompat2 [rv2 [Heq2 [Hrfn2 Hcanon2]]]]].
    iDestruct "Hb'" as "(%rv1 & %Hrfn1 & Hb')".
    iPoseProof ("Hincl'" $! rv1 rv2 with "[] [] Hb'") as "Hb'"; [done.. |].
    iModIntro. iSplitR; first done.
    iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first done). iFrame. done.
  Qed.

  Lemma enum_ltype_incl_shared {rt} (en1 en2 : enum rt) variant1 variant2 r κ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜enum_ltype_variant_tag_compat en1 r' v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      enum_ltype_variant_ltype_incl (Shared κ) en1 r' v1 en2 r' v2) -∗
    ltype_incl (Shared κ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Hincl". iModIntro. iSplit.
    - iApply enum_ltype_incl'_shared; first done.
      iIntros (r'). iDestruct ("Hincl" $! r') as "($ & $ & Hincl_payload)".
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iDestruct ("Hincl_payload" $! rv1 rv2 with "[] []") as "[Hincl' _]"; [done.. |]. done.
    - rewrite !ltype_core_enum. iApply enum_ltype_incl'_shared; first done.
      iIntros (r'). rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      rewrite !ltype_core_syn_type_eq.
      iDestruct ("Hincl" $! r') as "($ & $ & Hincl_payload)".
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iDestruct ("Hincl_payload" $! rv1 rv2 with "[] []") as "[_ Hcore]"; [done.. |]. done.
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
      enum_ltype_variant_ltype_eq Owned en1 r' v1 en2 r' v2) -∗
    ltype_incl' (Uniq κ γ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Heq !>" (π l).
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hloc & Hlb & Hcred & Hrfn & Hb)".
    iExists el. rewrite -Hels. iR. iR. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        destruct (proj1 Hcompat Hc) as [Hc2 [rv2 [Heq2 [Hrfn2 Hcanon2]]]].
        iDestruct "Hb" as "(%rv1 & %Hrfn1 & Hb)".
        iDestruct ("Heq_payload" $! rv1 rv2 with "[] []") as "((Hincl & _) & _)"; [done.. |].
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first naive_solver). iFrame. done.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        destruct (proj2 Hcompat Hc) as [Hc1 [rv1 [Heq1 [Hrfn1 Hcanon1]]]].
        iDestruct "Hb" as "(%rv2 & %Hrfn2 & Hb)".
        iDestruct ("Heq_payload" $! rv1 rv2 with "[] []") as "(_ & Hincl & _)"; [done.. |].
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite Htag Hst. do 3 (iSplitR; first naive_solver). iFrame. done.
    - iNext. iModIntro. iSplit.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        destruct (proj1 Hcompat Hc) as [Hc2 [rv2 [Heq2 [Hrfn2 Hcanon2]]]].
        iDestruct "Hb" as "(%rv1 & %Hrfn1 & Hb)".
        iDestruct ("Heq_payload" $! rv1 rv2 with "[] []") as "((_ & Hincl) & _)"; [done.. |].
        rewrite !ltype_own_core_equiv.
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite -Htag -Hst. do 3 (iSplitR; first naive_solver).
        iFrame "Htag Hpad Htail". iExists rv2. iSplit; first done.
        rewrite ltype_own_core_equiv. iFrame.
      + iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
        iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iMod "Hb" as "(%ly & %Hc & %Hlook & %Hly & Htag & Hpad & Hb & Htail)".
        destruct (proj2 Hcompat Hc) as [Hc1 [rv1 [Heq1 [Hrfn1 Hcanon1]]]].
        iDestruct "Hb" as "(%rv2 & %Hrfn2 & Hb)".
        iDestruct ("Heq_payload" $! rv1 rv2 with "[] []") as "(_ & _ & Hincl)"; [done.. |].
        rewrite !ltype_own_core_equiv.
        iMod ("Hincl" with "Hb") as "Hb". iModIntro.
        iExists ly. rewrite Htag Hst. do 3 (iSplitR; first naive_solver).
        iFrame "Htag Hpad Htail". iExists rv1. iSplit; first done.
        rewrite ltype_own_core_equiv. iFrame.
  Qed.

  Lemma enum_ltype_incl_uniq {rt} (en1 en2 : enum rt)
      variant1 variant2 r κ γ :
    enum_els en1 = enum_els en2 →
    (∀ r', let v1 := interp_enum_ltype_variant en1 variant1 r' in
      let v2 := interp_enum_ltype_variant en2 variant2 r' in
      ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
      ⌜enum_ltype_variant_compat en1 r' v1 ↔ enum_ltype_variant_compat en2 r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      enum_ltype_variant_ltype_eq Owned en1 r' v1 en2 r' v2) -∗
    ltype_incl (Uniq κ γ) r r (EnumLtype en1 variant1) (EnumLtype en2 variant2).
  Proof.
    intros Hels. iIntros "#Heq". iModIntro. iSplit.
    - by iApply enum_ltype_incl'_uniq.
    - rewrite !ltype_core_enum. iApply enum_ltype_incl'_uniq; first done.
      iIntros (r'). rewrite !interp_enum_ltype_variant_core /enum_ltype_variant_core /=.
      rewrite !ltype_core_syn_type_eq.
      iDestruct ("Heq" $! r') as "($ & %Hcompat & $ & Heq')".
      iSplitR; first done.
      iIntros (rv1 rv2) "%Hrfn1 %Hrfn2". iApply ltype_eq_core.
      iApply ("Heq'" $! rv1 rv2 with "[] []"); done.
  Qed.
End uniq_subltype.

Section enum_eqltype.
  Context `{!typeGS Σ}.

  Lemma enum_ltype_eq {rt} (en : enum rt) variant1 variant2 b r :
    (∀ r', let v1 := interp_enum_ltype_variant en variant1 r' in
      let v2 := interp_enum_ltype_variant en variant2 r' in
      ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
      ⌜enum_ltype_variant_tag_compat en r' v1 →
        enum_ltype_variant_compat en r' v1 ∧ enum_ltype_variant_compat en r' v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ∀ b, enum_ltype_variant_ltype_eq b en r' v1 en r' v2) -∗
    ltype_eq b r r (EnumLtype en variant1) (EnumLtype en variant2).
  Proof.
    iIntros "#Heq". iSplit.
    - destruct b.
      + iApply enum_ltype_incl_owned; first done.
        iIntros (r'). iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iSplit.
        { iPureIntro. intros Htag1. split; first done.
          destruct (Hcompat Htag1) as [_ Hcompat2]. exact Hcompat2. }
        iSplit; first done. iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
        iDestruct ("Heq_payload" $! Owned rv1 rv2 with "[] []") as "($ & _)"; done.
      + iApply enum_ltype_incl_shared; first done.
        iIntros (r'). iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iSplit.
        { iPureIntro. intros Htag1. split; first done.
          destruct (Hcompat Htag1) as [_ Hcompat2]. exact Hcompat2. }
        iSplit; first done. iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
        iDestruct ("Heq_payload" $! (Shared κ) rv1 rv2 with "[] []") as "($ & _)"; done.
      + iApply enum_ltype_incl_uniq; first done.
        iIntros (r'). iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & $ & Heq_payload)".
        iSplit; first done. iSplit.
        { iPureIntro. split.
          - intros Hcompat1. destruct (Hcompat (proj1 Hcompat1)) as [_ Hcompat2]. exact Hcompat2.
          - intros Hcompat2.
            have Htag1 : enum_ltype_variant_tag_compat en r'
                (interp_enum_ltype_variant en variant1 r').
            { unfold enum_ltype_variant_tag_compat. rewrite Htag. exact (proj1 Hcompat2). }
            destruct (Hcompat Htag1) as [Hcompat1 _]. exact Hcompat1. }
        iApply "Heq_payload".
    - destruct b.
      + iApply enum_ltype_incl_owned; first done.
        iIntros (r'). iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iSplit.
        { iPureIntro. intros Htag2. split; first by symmetry.
          have Htag1 : enum_ltype_variant_tag_compat en r'
              (interp_enum_ltype_variant en variant1 r').
          { unfold enum_ltype_variant_tag_compat. rewrite Htag. exact Htag2. }
          destruct (Hcompat Htag1) as [Hcompat1 _]. exact Hcompat1. }
        iSplit; first (iPureIntro; symmetry; exact Hst). iIntros (rv2 rv1) "%Hrfn2 %Hrfn1".
        iDestruct ("Heq_payload" $! Owned rv1 rv2 with "[] []") as "(_ & $)"; done.
      + iApply enum_ltype_incl_shared; first done.
        iIntros (r'). iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iSplit.
        { iPureIntro. intros Htag2. split; first by symmetry.
          have Htag1 : enum_ltype_variant_tag_compat en r'
              (interp_enum_ltype_variant en variant1 r').
          { unfold enum_ltype_variant_tag_compat. rewrite Htag. exact Htag2. }
          destruct (Hcompat Htag1) as [Hcompat1 _]. exact Hcompat1. }
        iSplit; first (iPureIntro; symmetry; exact Hst). iIntros (rv2 rv1) "%Hrfn2 %Hrfn1".
        iDestruct ("Heq_payload" $! (Shared κ) rv1 rv2 with "[] []") as "(_ & $)"; done.
      + iApply enum_ltype_incl_uniq; first done.
        iIntros (r'). iDestruct ("Heq" $! r') as "(%Htag & %Hcompat & %Hst & Heq_payload)".
        iSplit; first (iPureIntro; symmetry; exact Htag). iSplit.
        { iPureIntro. split.
          - intros Hcompat2.
            have Htag1 : enum_ltype_variant_tag_compat en r'
                (interp_enum_ltype_variant en variant1 r').
            { unfold enum_ltype_variant_tag_compat. rewrite Htag. exact (proj1 Hcompat2). }
            destruct (Hcompat Htag1) as [Hcompat1 _]. exact Hcompat1.
          - intros Hcompat1. destruct (Hcompat (proj1 Hcompat1)) as [_ Hcompat2]. exact Hcompat2. }
        iSplit; first (iPureIntro; symmetry; exact Hst). iIntros (rv2 rv1) "%Hrfn2 %Hrfn1".
        iDestruct ("Heq_payload" $! Owned rv1 rv2 with "[] []") as "Heq_payload'"; [done.. |].
        iApply ltype_eq_sym. done.
  Qed.
End enum_eqltype.
