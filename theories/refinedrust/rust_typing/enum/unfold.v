From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import programs.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section unfold.
  Context `{!typeGS Σ}.
  Import EqNotations.

  (* NOTE: we can only do this unfolding for PlaceIn -- because the variant we unfold to depends on that.
     I think this should not be a problem.
  *)

  Lemma enum_tag'_Some {rt} (en : enum rt) r variant :
    enum_tag en r = Some variant →
    enum_tag' en r = variant.
  Proof.
    rewrite /enum_tag'. intros ->. done.
  Qed.

  (* TODO: move *)
  Lemma owned_ofty_from_pointsto_val {rt} (ty : type rt) π r l v ly :
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    l `has_layout_loc` ly →
    loc_in_bounds l 0 (ly_size ly) -∗
    v ◁ᵥ{π, MetaNone} r @ ty -∗
    l ↦ v -∗
     lty_of_ty_own ty Owned π (#r) l.
  Proof.
    iIntros (??) "Hlb Hv Hl".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc".
    rewrite /lty_of_ty_own/=.
    iFrame. iR. iR. iR. done.
  Qed.

  Lemma shared_ofty_from_ty_shr {rt} (ty : type rt) κ π r l ly :
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    l `has_layout_loc` ly →
    loc_in_bounds l 0 (ly_size ly) -∗
    l ◁ₗ{π, MetaNone, κ} r @ ty -∗
     lty_of_ty_own ty (Shared κ) π (#r) l.
  Proof.
    iIntros (??) "Hlb #Hshr".
    iPoseProof (ty_shr_sidecond with "Hshr") as "#Hsc".
    rewrite /lty_of_ty_own/=.
    iExists ly. iR. iR. iR. iFrame "Hlb".
    iExists r. iSplitR; first done. iModIntro. iModIntro. done.
  Qed.

  Lemma enum_tag_padding_has_layout_loc el l :
    (l +ₗ ly_size (it_layout el.(el_tag_it))) `has_layout_loc` enum_tag_padding_ly el.
  Proof.
    apply has_layout_loc_1. rewrite /enum_tag_padding_ly /ly_align /=. done.
  Qed.
  Lemma enum_tail_padding_has_layout_loc el variant_ly l :
    (l +ₗ el.(el_data_offset) +ₗ ly_size variant_ly) `has_layout_loc` enum_tail_padding_ly el variant_ly.
  Proof.
    apply has_layout_loc_1. rewrite /enum_tail_padding_ly /ly_align /=. done.
  Qed.

  Local Lemma ofty_owned_to_pointsto_val {rt} (ty : type rt) π r l :
     lty_of_ty_own ty Owned π (#r) l ={lftE}=∗
    ∃ v, l ↦ v ∗ v ◁ᵥ{π, MetaNone} r @ ty.
  Proof.
    rewrite /lty_of_ty_own.
    iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & %r' & %Hrfn & Hv)".
    subst r'. done.
  Qed.

  Local Lemma ofty_shared_to_ty_shr {rt} (ty : type rt) κ π r l :
     lty_of_ty_own ty (Shared κ) π (#r) l ={lftE}=∗
    l ◁ₗ{π, MetaNone, κ} r @ ty.
  Proof.
    rewrite /lty_of_ty_own.
    iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & %r' & %Hrfn & #Hb)".
    subst r'. done.
  Qed.

  Local Lemma type_syn_type_rew {rt1 rt2 : RT} (Heq : rt1 = rt2) (ty : type rt1) m :
    ty_syn_type (rew [type] Heq in ty) m = ty_syn_type ty m.
  Proof. destruct Heq. done. Qed.

  Local Lemma type_own_val_rew {rt1 rt2 : RT} (Heq : rt1 = rt2) (ty : type rt1) π (r : rt1) m v :
    ty_own_val (rew [type] Heq in ty) π (rew [RT_rt] Heq in r) m v ≡
    ty_own_val ty π r m v.
  Proof. destruct Heq. done. Qed.

  Local Lemma type_shr_rew {rt1 rt2 : RT} (Heq : rt1 = rt2) (ty : type rt1) κ π (r : rt1) m l :
    ty_shr (rew [type] Heq in ty) κ π (rew [RT_rt] Heq in r) m l ≡
    ty_shr ty κ π r m l.
  Proof. destruct Heq. done. Qed.

  Lemma enum_unfold_1_owned {rt : RT} (en : enum rt) r :
    ⊢ ltype_incl' Owned r r (◁ (enum_t en))%I (EnumLtype en None).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_ofty_unfold ltype_own_enum_unfold /lty_of_ty_own /enum_ltype_own.
    iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & %r' & Hrfn & Hv)".
    iMod "Hv" as "(%v & Hl & Hv)".
    rewrite /ty_own_val /= enum_own_val_unfold /enum_own_val_def.
    iDestruct "Hv" as "(%el & %variant & %variant_ly & %Hmeta & %Halg & %Htag & %Hvariant & %Hpayload_st & Htag & Htag_pad & Hpayload & Htail)".
    subst.
    pose proof (enum_tag'_Some en r' variant Htag) as Htag'.
    pose proof (use_enum_layout_alg_Some_inv _ _ Halg) as Hel_st.
    assert (ly = layout_of_enum el) as -> by by eapply syn_type_has_layout_inj.
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    iExists el. iR.
    iSplitR. { done. }
    iSplitR. { iExact "Hlb". }
    iModIntro. iExists r'. iFrame "Hrfn".
    iModIntro.
    iEval (rewrite /canonical_enum_ltype_variant Htag').
    iExists variant_ly.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    iAssert (((∃ vtag : val, l ↦ vtag ∗
        vtag ◁ᵥ{π, MetaNone} els_lookup_tag en.(enum_els) variant @ int el.(el_tag_it)) ∗
      (∃ vtag_pad : val, (l +ₗ tag_size) ↦ vtag_pad ∗
        vtag_pad ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el))) ∗
      (∃ vvariant : val, (l +ₗ data_offset) ↦ vvariant ∗
        vvariant ◁ᵥ{π, MetaNone} en.(enum_r) r' @ en.(enum_ty) r') ∗
      (∃ vtail : val, (l +ₗ (data_offset + variant_size)%nat) ↦ vtail ∗
        vtail ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly))))%I)
      with "[Hl Htag Htag_pad Hpayload Htail]" as "(Htag & Htag_pad & Hpayload & Htail)".
    { rewrite /tag_size /data_offset /variant_size.
      rewrite -(enum_pointsto_val_split en π r' l el variant variant_ly Hvariant Hpayload_st).
      iExists v. iFrame. }
    iDestruct "Htag" as "(%vtag & Hl_tag & Htag)".
    iDestruct "Htag_pad" as "(%vtag_pad & Hl_tag_pad & Htag_pad)".
    iDestruct "Hpayload" as "(%vpayload & Hl_payload & Hpayload)".
    iDestruct "Htail" as "(%vtail & Hl_tail & Htail)".
    iSplitL "Hl_tag Htag".
    { iApply (owned_ofty_from_pointsto_val with "[] Htag Hl_tag").
      - simpl. apply syn_type_has_layout_int. done.
      - by apply enum_tag_has_layout_loc.
      - iApply (loc_in_bounds_enum_tag with "Hlb"). done. }
    iSplitL "Hl_tag_pad Htag_pad".
    { iApply (owned_ofty_from_pointsto_val with "[] Htag_pad Hl_tag_pad").
      - by apply enum_tag_padding_uninit_syn_type_has_layout with variant variant_ly.
      - apply enum_tag_padding_has_layout_loc.
      - iApply (loc_in_bounds_enum_tag_padding with "Hlb"). done. }
    iSplitL "Hl_payload Hpayload".
    { iEval (rewrite /canonical_enum_ltype_variant /OfTy /=).
      rewrite ltype_own_ofty_unfold.
      iApply (owned_ofty_from_pointsto_val with "[] Hpayload Hl_payload").
      - done.
      - by eapply enum_payload_has_layout_loc.
      - iApply (loc_in_bounds_enum_payload with "Hlb"). done. }
    rewrite shift_loc_assoc_nat.
    iApply (owned_ofty_from_pointsto_val with "[] Htail Hl_tail").
    - by apply enum_tail_padding_uninit_syn_type_has_layout with variant.
    - rewrite -shift_loc_assoc_nat. apply enum_tail_padding_has_layout_loc.
    - rewrite -/data_offset -/variant_size -shift_loc_assoc_nat.
      iApply (loc_in_bounds_enum_tail_padding with "Hlb"). done.
  Qed.

  Lemma enum_unfold_1_shared {rt : RT} (en : enum rt) κ r :
    ⊢ ltype_incl' (Shared κ) r r (◁ (enum_t en))%I (EnumLtype en None).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_ofty_unfold ltype_own_enum_unfold /lty_of_ty_own /enum_ltype_own.
    iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & %r' & Hrfn & #Hb)".
    apply syn_type_has_layout_enum_inv in Hst as (el & variant_lys & Halg & -> & Hvariants & ?).
    pose proof (use_enum_layout_alg_Some _ _ _ Hvariants Halg) as Halg_el.
    iExists el. iSplitR. { done. }
    iR. iR. iExists r'. iFrame "Hrfn".
    iModIntro. iMod "Hb" as "Hb".
    rewrite /ty_shr /= enum_shr_unfold /enum_shr_def.
    iDestruct "Hb" as "(%el' & %variant & %variant_ly & %Hmeta & %Halg' & %Htag & %Hvariant & %Hpayload_st & %Hly' & Htag & Htag_pad & Hpayload & Htail)".
    subst.
    assert (el' = el) as ->.
    { eapply (enum_layout_spec_has_layout_inj (enum_els en));
        rewrite /enum_layout_spec_has_layout; [exact Halg'|exact Halg_el]. }
    pose proof (enum_tag'_Some en r' variant Htag) as Htag'.
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    iModIntro. iEval (rewrite /canonical_enum_ltype_variant Htag').
    iExists variant_ly.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    iSplitL "Htag".
    { iApply (shared_ofty_from_ty_shr with "[] Htag").
      - simpl. apply syn_type_has_layout_int. done.
      - by apply enum_tag_has_layout_loc.
      - iApply (loc_in_bounds_enum_tag with "Hlb"). done. }
    iSplitL "Htag_pad".
    { iApply (shared_ofty_from_ty_shr with "[] Htag_pad").
      - by apply enum_tag_padding_uninit_syn_type_has_layout with variant variant_ly.
      - apply enum_tag_padding_has_layout_loc.
      - iApply (loc_in_bounds_enum_tag_padding with "Hlb"). done. }
    iSplitL "Hpayload".
    { iEval (rewrite /canonical_enum_ltype_variant /OfTy /=).
      rewrite ltype_own_ofty_unfold.
      iApply (shared_ofty_from_ty_shr with "[] Hpayload").
      - done.
      - by eapply enum_payload_has_layout_loc.
      - iApply (loc_in_bounds_enum_payload with "Hlb"). done. }
    rewrite shift_loc_assoc_nat.
    iApply (shared_ofty_from_ty_shr with "[] Htail").
    - by apply enum_tail_padding_uninit_syn_type_has_layout with variant.
    - rewrite -shift_loc_assoc_nat. apply enum_tail_padding_has_layout_loc.
    - rewrite -/data_offset -/variant_size -shift_loc_assoc_nat.
      iApply (loc_in_bounds_enum_tail_padding with "Hlb"). done.
  Qed.

  Lemma enum_unfold_2_owned {rt} (en : enum rt) r  :
    ⊢ ltype_incl' Owned r r (EnumLtype en None) (◁ enum_t en)%I.
  Proof.
    iModIntro. iIntros (π l) "Hb".
    rewrite ltype_own_enum_unfold ltype_own_ofty_unfold /enum_ltype_own /lty_of_ty_own.
    iDestruct "Hb" as "(%el & %Halg & %Hly & Hlb & %r' & Hrfn & Hb)".
    iMod "Hb" as "(%variant_ly & %Htagcompat & %Hvariant & %Hst & Htag & Htag_pad & Hpayload & Htail)".
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    iMod (ofty_owned_to_pointsto_val with "Htag") as "(%vtag & Hl_tag & Htag)".
    iMod (ofty_owned_to_pointsto_val with "Htag_pad") as "(%vtag_pad & Hl_tag_pad & Htag_pad)".
    iEval (rewrite /interp_enum_ltype_variant /OfTy /=) in "Hpayload".
    iEval (rewrite ltype_own_ofty_unfold) in "Hpayload".
    iMod (ofty_owned_to_pointsto_val with "Hpayload") as "(%vpayload & Hl_payload & Hpayload)".
    iMod (ofty_owned_to_pointsto_val with "Htail") as "(%vtail & Hl_tail & Htail)".
    rewrite /interp_enum_ltype_variant /OfTy /= in Hst.
    iModIntro.
    iExists (layout_of_enum el).
    iSplitR. { iPureIntro. by eapply use_enum_layout_alg_Some_inv. }
    iSplitR. { done. }
    iPoseProof (ty_own_val_sidecond with "Hpayload") as "#Hsc".
    iSplitR "Hlb Hrfn Hl_tag Htag Hl_tag_pad Htag_pad Hl_payload Hpayload Hl_tail Htail". { done. }
    iSplitL "Hlb". { iFrame "Hlb". }
    iExists r'. iFrame "Hrfn". iModIntro.
    rewrite /ty_own_val /= enum_own_val_unfold /enum_own_val_def.
    iAssert ((∃ v : val,
      l ↦ v ∗
      take (ly_size (it_layout el.(el_tag_it))) v
        ◁ᵥ{π, MetaNone} els_lookup_tag en.(enum_els) (enum_tag' en r') @ int el.(el_tag_it) ∗
      take (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it)))
        (drop (ly_size (it_layout el.(el_tag_it))) v)
        ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el)) ∗
      take (ly_size variant_ly) (drop el.(el_data_offset) v)
        ◁ᵥ{π, MetaNone} enum_r en r' @ enum_ty en r' ∗
      drop (el.(el_data_offset) + ly_size variant_ly) v
        ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly)))%I)
      with "[Hl_tag Htag Hl_tag_pad Htag_pad Hl_payload Hpayload Hl_tail Htail]" as "(%v & Hl & Htag & Htag_pad & Hpayload & Htail)".
    { rewrite /tag_size /data_offset /variant_size.
      rewrite enum_pointsto_val_split; [|done|done].
      iSplitL "Hl_tag Htag"; first (iExists _; iFrame).
      iSplitL "Hl_tag_pad Htag_pad"; first (iExists _; iFrame).
      iSplitL "Hl_payload Hpayload".
      { iExists _. iFrame. }
      iExists _. rewrite shift_loc_assoc_nat. iFrame. }
    iExists v. iFrame "Hl".
    iExists el, (enum_tag' en r'), variant_ly.
    do 5 iR.
    iFrame.
  Qed.

  Lemma enum_unfold_2_shared {rt} (en : enum rt) κ r :
    ⊢ ltype_incl' (Shared κ) r r (EnumLtype en None) (◁ enum_t en)%I.
  Proof.
    iModIntro. iIntros (π l) "Hb".
    rewrite ltype_own_enum_unfold ltype_own_ofty_unfold /enum_ltype_own /lty_of_ty_own.
    iDestruct "Hb" as "(%el & %Halg & %Hly & #Hlb & %r' & Hrfn & #Hb)".
    iExists (layout_of_enum el).
    iSplitR. { iPureIntro. by eapply use_enum_layout_alg_Some_inv. }
    iSplitR. { done. }
    iSplitR. { done. }
    iSplitR. { iFrame "Hlb". }
    iExists r'. iFrame "Hrfn".
    iModIntro.
    iMod "Hb" as "(%variant_ly & %Htagcompat & %Hvariant & %Hst & Htag & Htag_pad & Hpayload & Htail)".
    iMod (ofty_shared_to_ty_shr with "Htag") as "Htag".
    iMod (ofty_shared_to_ty_shr with "Htag_pad") as "Htag_pad".
    iEval (rewrite /interp_enum_ltype_variant /OfTy /=) in "Hpayload".
    iEval (rewrite ltype_own_ofty_unfold) in "Hpayload".
    iMod (ofty_shared_to_ty_shr with "Hpayload") as "Hpayload".
    iMod (ofty_shared_to_ty_shr with "Htail") as "Htail".
    rewrite /interp_enum_ltype_variant /OfTy /= in Hst.
    iModIntro.
    rewrite /ty_shr /= enum_shr_unfold /enum_shr_def.
    iExists el, (enum_tag' en r'), variant_ly.
    do 5 iR.
    iSplitR; first done.
    iSplitL "Htag"; first done.
    iSplitL "Htag_pad"; first done.
    iSplitL "Hpayload".
    { iFrame. }
    rewrite shift_loc_assoc_nat. iFrame.
  Qed.


  Local Lemma enum_unfold_uniq_case (b : bool) {rt : RT} (en : enum rt) π γ el l :
    use_enum_layout_alg en.(enum_els) = Some el →
    l `has_layout_loc` el →
    loc_in_bounds l 0 el.(el_size) -∗
    ((∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=> ∃ v : val,
        l ↦ v ∗ v ◁ᵥ{π, MetaNone} r' @ enum_t en) ↔
     (∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=> ∃ variant_ly,
        let v := interp_enum_ltype_variant en None r' in
        ⌜enum_ltype_variant_compat en r' v⌝ ∗
        ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
        ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
        lty_of_ty_own (int el.(el_tag_it)) Owned π
          (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
        lty_of_ty_own (uninit (LiteralSynType
          (Layout (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it))) 0))) Owned π
          (PlaceIn ()) (l +ₗ ly_size (it_layout el.(el_tag_it))) ∗
        (match b with
         | true => ltype_own_core v.(eltv_ltype) Owned π
             (PlaceIn v.(eltv_rfn)) (l +ₗ el.(el_data_offset))
         | false => ltype_own v.(eltv_ltype) Owned π
             (PlaceIn v.(eltv_rfn)) (l +ₗ el.(el_data_offset))
         end) ∗
        lty_of_ty_own (uninit (LiteralSynType
          (Layout (el.(el_size) - el.(el_data_offset) - ly_size variant_ly) 0))) Owned π
          (PlaceIn ()) (l +ₗ el.(el_data_offset) +ₗ ly_size variant_ly)))%I.
  Proof.
    iIntros (Halg Hly) "#Hlb".
    iSplit.
    - iIntros "(%r' & Hauth & Hb)".
      iExists r'. iFrame "Hauth".
      iMod "Hb" as "(%v & Hl & Hv)".
      rewrite /ty_own_val /= enum_own_val_unfold /enum_own_val_def.
      iDestruct "Hv" as "(%el' & %variant & %variant_ly & %Hmeta & %Halg' & %Htag & %Hvariant & %Hpayload_st & Htag & Htag_pad & Hpayload & Htail)".
      subst.
      assert (el' = el) as ->.
      { eapply (enum_layout_spec_has_layout_inj (enum_els en));
          rewrite /enum_layout_spec_has_layout; [exact Halg'|exact Halg]. }
      pose proof (enum_tag'_Some en r' variant Htag) as Htag'.
      rewrite Htag'.
      set (tag_size := ly_size (it_layout el.(el_tag_it))).
      set (data_offset := el.(el_data_offset)).
      set (variant_size := ly_size variant_ly).
      iModIntro. iExists variant_ly.
      iEval (rewrite /canonical_enum_ltype_variant /=).
      iSplitR.
      { iPureIntro. rewrite Htag'. split; [done | ]. exists eq_refl. done. }
      iSplitR; first done.
      iSplitR; first done.
      iAssert (((∃ vtag : val, l ↦ vtag ∗
          vtag ◁ᵥ{π, MetaNone} els_lookup_tag en.(enum_els) variant @ int el.(el_tag_it)) ∗
        (∃ vtag_pad : val, (l +ₗ tag_size) ↦ vtag_pad ∗
          vtag_pad ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el))) ∗
        (∃ vvariant : val, (l +ₗ data_offset) ↦ vvariant ∗
          vvariant ◁ᵥ{π, MetaNone} en.(enum_r) r' @ en.(enum_ty) r') ∗
        (∃ vtail : val, (l +ₗ (data_offset + variant_size)%nat) ↦ vtail ∗
          vtail ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType
            (enum_tail_padding_ly el variant_ly))))%I)
        with "[Hl Htag Htag_pad Hpayload Htail]" as "(Htag & Htag_pad & Hpayload & Htail)".
      { rewrite /tag_size /data_offset /variant_size.
        rewrite -(enum_pointsto_val_split en π r' l el variant variant_ly Hvariant Hpayload_st).
        iExists v. iFrame. }
      iDestruct "Htag" as "(%vtag & Hl_tag & Htag)".
      iDestruct "Htag_pad" as "(%vtag_pad & Hl_tag_pad & Htag_pad)".
      iDestruct "Hpayload" as "(%vpayload & Hl_payload & Hpayload)".
      iDestruct "Htail" as "(%vtail & Hl_tail & Htail)".
      iSplitL "Hl_tag Htag".
      { iApply (owned_ofty_from_pointsto_val with "[] Htag Hl_tag").
        - simpl. apply syn_type_has_layout_int. done.
        - by apply enum_tag_has_layout_loc.
        - iApply (loc_in_bounds_enum_tag with "Hlb"). done. }
      iSplitL "Hl_tag_pad Htag_pad".
      { iApply (owned_ofty_from_pointsto_val with "[] Htag_pad Hl_tag_pad").
        - by apply enum_tag_padding_uninit_syn_type_has_layout with variant variant_ly.
        - apply enum_tag_padding_has_layout_loc.
        - iApply (loc_in_bounds_enum_tag_padding with "Hlb"). done. }
      iSplitL "Hl_payload Hpayload".
      { destruct b; simpl.
        - rewrite ltype_own_core_equiv ltype_core_ofty ltype_own_ofty_unfold.
          iApply (owned_ofty_from_pointsto_val with "[] Hpayload Hl_payload").
          { done. }
          { by eapply enum_payload_has_layout_loc. }
          { iApply (loc_in_bounds_enum_payload with "Hlb"). done. }
        - rewrite ltype_own_ofty_unfold.
          iApply (owned_ofty_from_pointsto_val with "[] Hpayload Hl_payload").
          { done. }
          { by eapply enum_payload_has_layout_loc. }
          { iApply (loc_in_bounds_enum_payload with "Hlb"). done. } }
      rewrite shift_loc_assoc_nat.
      iApply (owned_ofty_from_pointsto_val with "[] Htail Hl_tail").
      + by apply enum_tail_padding_uninit_syn_type_has_layout with variant.
      + rewrite -shift_loc_assoc_nat. apply enum_tail_padding_has_layout_loc.
      + rewrite -/data_offset -/variant_size -shift_loc_assoc_nat.
        iApply (loc_in_bounds_enum_tail_padding with "Hlb"). done.
    - iIntros "(%r' & Hauth & Hb)".
      iExists r'. iFrame "Hauth".
      iMod "Hb" as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Htag_pad & Hpayload & Htail)".
      rewrite /canonical_enum_ltype_variant /= in Hcompat Hst.
      destruct Hcompat as (Htagcompat & _).
      iAssert ((l +ₗ el.(el_data_offset)) ◁ₗ[π, Owned]
        (PlaceIn (enum_r en r')) @ (◁ enum_ty en r'))%I
        with "[Hpayload]" as "Hpayload".
      { destruct b; simpl.
        - rewrite ltype_own_core_equiv ltype_core_ofty. iFrame.
        - iFrame. }
      iEval (rewrite ltype_own_ofty_unfold) in "Hpayload".
      iMod (ofty_owned_to_pointsto_val with "Htag") as "(%vtag & Hl_tag & Htag)".
      iMod (ofty_owned_to_pointsto_val with "Htag_pad") as "(%vtag_pad & Hl_tag_pad & Htag_pad)".
      iMod (ofty_owned_to_pointsto_val with "Hpayload") as "(%vpayload & Hl_payload & Hpayload)".
      iMod (ofty_owned_to_pointsto_val with "Htail") as "(%vtail & Hl_tail & Htail)".
      set (tag_size := ly_size (it_layout el.(el_tag_it))).
      set (data_offset := el.(el_data_offset)).
      set (variant_size := ly_size variant_ly).
      iModIntro.
      rewrite /ty_own_val /= enum_own_val_unfold /enum_own_val_def.
      iAssert ((∃ v : val,
        l ↦ v ∗
        take tag_size v ◁ᵥ{π, MetaNone} els_lookup_tag en.(enum_els) (enum_tag' en r') @ int el.(el_tag_it) ∗
        take (data_offset - tag_size) (drop tag_size v) ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el)) ∗
        take variant_size (drop data_offset v) ◁ᵥ{π, MetaNone} en.(enum_r) r' @ en.(enum_ty) r' ∗
        drop (data_offset + variant_size) v ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType
          (enum_tail_padding_ly el variant_ly)))%I)
        with "[Hl_tag Htag Hl_tag_pad Htag_pad Hl_payload Hpayload Hl_tail Htail]" as "(%v & Hl & Htag & Htag_pad & Hpayload & Htail)".
      { rewrite /tag_size /data_offset /variant_size.
        rewrite enum_pointsto_val_split; [|done|done].
        iSplitL "Hl_tag Htag"; first (iExists _; iFrame).
        iSplitL "Hl_tag_pad Htag_pad"; first (iExists _; iFrame).
        iSplitL "Hl_payload Hpayload"; first (iExists _; iFrame).
        iExists _. rewrite shift_loc_assoc_nat. iFrame. }
      iExists v. iFrame "Hl".
      iExists el, (enum_tag' en r'), variant_ly.
      do 5 iR. iFrame.
  Qed.

  Lemma enum_unfold_1_uniq {rt : RT} (en : enum rt) κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (◁ (enum_t en))%I (EnumLtype en None).
  Proof.
    iModIntro. iIntros (π l) "Hb".
    rewrite ltype_own_ofty_unfold ltype_own_enum_unfold /lty_of_ty_own /enum_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & %Hly & #Hsc & #Hlb & Hcred & Hrfn & Hb)".
    apply syn_type_has_layout_enum_inv in Hst as (el & variant_lys & Halg & -> & Hvariants & _).
    pose proof (use_enum_layout_alg_Some _ _ _ Hvariants Halg) as Halg_el.
    iExists el.
    iSplitR. { done. }
    iSplitR. { done. }
    iSplitR. { iFrame "Hlb". }
    iFrame "Hcred Hrfn".
    iMod "Hb" as "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      + iIntros "Hofty".
        iApply (enum_unfold_uniq_case false with "Hlb Hofty"); done.
      + iIntros "Henum". simpl.
        iApply (enum_unfold_uniq_case false with "Hlb Henum"); done.
    - iNext. iModIntro. iSplit.
      + iIntros "Hofty".
        iApply (enum_unfold_uniq_case true with "Hlb Hofty"); done.
      + iIntros "Henum". simpl.
        iApply (enum_unfold_uniq_case true with "Hlb Henum"); done.
  Qed.



  Lemma enum_unfold_2_uniq {rt} (en : enum rt) κ γ (r : place_rfn rt) :
    ⊢ ltype_incl' (Uniq κ γ) r r (EnumLtype en None) (◁ enum_t en)%I.
  Proof.
    iModIntro. iIntros (π l) "Hb".
    rewrite ltype_own_enum_unfold ltype_own_ofty_unfold /enum_ltype_own /lty_of_ty_own.
    iDestruct "Hb" as "(%el & %Halg & %Hly & Hlb & Hcred & Hrfn & Hb)".
    iDestruct "Hlb" as "#Hlb".
    iExists (layout_of_enum el).
    iSplitR. { iPureIntro. by eapply use_enum_layout_alg_Some_inv. }
    iSplitR. { done. }
    iSplitR. { done. }
    iSplitR. { iFrame "Hlb". }
    iFrame "Hcred Hrfn".
    iMod "Hb" as "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      + iIntros "Henum". simpl.
        iApply (enum_unfold_uniq_case false with "Hlb Henum"); done.
      + iIntros "Hofty".
        iApply (enum_unfold_uniq_case false with "Hlb Hofty"); done.
    - iNext. iModIntro. iSplit.
      + iIntros "Henum".
        iApply (enum_unfold_uniq_case true with "Hlb Henum"); done.
      + iIntros "Hofty".
        iApply (enum_unfold_uniq_case true with "Hlb Hofty"); done.
  Qed.

  Local Lemma enum_t_unfold_1' {rt} (en : enum rt) k r :
    ⊢ ltype_incl' k r r (◁ enum_t en)%I (EnumLtype en None).
  Proof.
    destruct k.
    - by apply enum_unfold_1_owned.
    - by apply enum_unfold_1_shared.
    - by apply enum_unfold_1_uniq.
  Qed.

  Lemma enum_t_unfold_1 {rt} (en : enum rt) k r :
    ⊢ ltype_incl k r r (◁ enum_t en)%I (EnumLtype en None).
  Proof.
    iModIntro. iSplitR.
    - by iApply enum_t_unfold_1'.
    - simp_ltypes. by iApply enum_t_unfold_1'.
  Qed.

  Local Lemma enum_t_unfold_2' {rt} (en : enum rt) k r :
    ⊢ ltype_incl' k r r (EnumLtype en None) (◁ enum_t en)%I.
  Proof.
    destruct k.
    - by apply enum_unfold_2_owned.
    - by apply enum_unfold_2_shared.
    - by apply enum_unfold_2_uniq.
  Qed.

  Lemma enum_t_unfold_2 {rt} (en : enum rt) k r :
    ⊢ ltype_incl k r r (EnumLtype en None) (◁ enum_t en)%I.
  Proof.
    iModIntro. iSplitR.
    - by iApply enum_t_unfold_2'.
    - simp_ltypes. by iApply enum_t_unfold_2'.
  Qed.

  Lemma enum_t_unfold {rt} (en : enum rt) k r :
    ⊢ ltype_eq k r r (◁ enum_t en)%I (EnumLtype en None).
  Proof.
    iSplit.
    - by iApply enum_t_unfold_1.
    - by iApply enum_t_unfold_2.
  Qed.

  Lemma enum_t_unfold_full_eqltype E L {rt} (en : enum rt) :
    full_eqltype E L (◁ enum_t en)%I (EnumLtype en None).
  Proof.
    iIntros (?) "HL CTX HE". iR.
    iIntros (??). iApply enum_t_unfold.
  Qed.

End unfold.

Section cast.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Lemma cast_ltype_enum_none {rt} E L (en : enum rt) T :
    T (enum_t en)
    ⊢ cast_ltype_to_type E L (EnumLtype en None) T.
  Proof.
    iIntros "HT". iExists _. iFrame.
    iPureIntro. symmetry.
    apply enum_t_unfold_full_eqltype.
  Qed.
  Definition cast_ltype_enum_none_inst := [instance @cast_ltype_enum_none].
  Global Existing Instance cast_ltype_enum_none_inst.

  (* TODO: can we get a reasonable instance for the other direction? *)

  (*
  Lemma cast_ltype_enum_some {rt} E L (en : enum rt) variant {rte} (lte : ltype rte) re T :
    cast_ltype_to_type E L lte (λ tye,
      mut_eqtype E L tye (en.(enum_ty)
      ∃ sem,
        ⌜enum_tag_ty_inj en variant = Some sem⌝ ∗
        ∃ (Heq : sem.(enum_tag_sem_rt) = rte),
        mut_eqtype E L (rew <- Heq in tye) (sem.(enum_tag_sem_ty)) (T (enum_t en)))
    ⊢ cast_ltype_to_type E L (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte re))) T.
  Proof.
  Admitted.
  *)
End cast.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_enum_unfold E L f l {rt} (en : enum rt) r bmin k P T :
    typed_place E L f l (EnumLtype en None) r bmin k P T
    ⊢ typed_place E L f l (◁ enum_t en) r bmin k P T.
  Proof.
    iIntros "HT". iApply typed_place_eqltype; last done.
    apply enum_t_unfold_full_eqltype.
  Qed.
  Definition typed_place_enum_unfold_inst := [instance @typed_place_enum_unfold].
  Global Existing Instance typed_place_enum_unfold_inst | 20.
End place.
