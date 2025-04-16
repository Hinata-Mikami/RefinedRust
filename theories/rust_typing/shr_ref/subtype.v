From refinedrust Require Export type ltypes.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Subtyping lemmas for shared references *)

Section subtype.
  Context `{typeGS Σ}.

  Lemma shr_ref_own_val_mono_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) v π r1 r2 κ1 κ2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    v ◁ᵥ{π} #r1 @ shr_ref κ2 ty1 -∗
    v ◁ᵥ{π} #r2 @ shr_ref κ1 ty2.
  Proof.
    iIntros "#Hincl (%Hst_eq & #Hsc_eq & _ & #Hincl_shr)".
    iIntros "(%l & %ly & %r' & -> & ? & ? & Hlb & Hsc & -> & #Hl)". iExists l, ly, r2.
    iSplitR; first done. rewrite -Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iR. iModIntro. iMod "Hl". iModIntro.
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.
  Lemma shr_ref_own_val_mono {rt} (ty1 ty2 : type rt) v π r κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ᵥ{π} r @ shr_ref κ2 ty1 -∗
    v ◁ᵥ{π} r @ shr_ref κ1 ty2.
  Proof.
    iIntros "#Hincl #Hsub".
    iDestruct ("Hsub" $! inhabitant) as "(%Hst_eq & #Hsc_eq & _)".
    iIntros "(%l & %ly & %r' & -> & ? & ? & Hlb & Hsc & Hr & #Hl)". iExists l, ly, r'.
    iSplitR; first done. rewrite -Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iModIntro. iMod "Hl". iModIntro.
    iPoseProof ("Hsub" $! r') as "(_ & _ & _ & #Hincl_shr)".
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.

  Lemma shr_ref_shr_mono_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) l π κ r1 r2 κ1 κ2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    l ◁ₗ{π, κ} #r1 @ shr_ref κ2 ty1 -∗
    l ◁ₗ{π, κ} #r2 @ shr_ref κ1 ty2.
  Proof.
    iIntros "#Hincl (%Hst_eq & #Hsc_eq & _ & #Hincl_shr)".
    iIntros "(%li & %ly & %r' & ? & ? & ? & Hlb & Hsc & -> & Hli & #Hb)".
    iExists li, ly, r2. rewrite Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iR. iModIntro. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.
  Lemma shr_ref_shr_mono {rt} (ty1 ty2 : type rt) l π κ r κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    l ◁ₗ{π, κ} r @ shr_ref κ2 ty1 -∗
    l ◁ₗ{π, κ} r @ shr_ref κ1 ty2.
  Proof.
    iIntros "#Hincl #Hsub".
    iPoseProof ("Hsub" $! inhabitant) as "(%Hst_eq & #Hsc_eq & _)".
    iIntros "(%li & %ly & %r' & ? & ? & ? & Hlb & Hsc & Hr & Hli & #Hb)".
    iExists li, ly, r'. rewrite Hst_eq. iFrame.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iModIntro. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iPoseProof ("Hsub" $! r') as "(_ & _ & _ & #Hincl_shr)".
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.

  Lemma shr_ref_type_incl_in {rt1 rt2} κ2 κ1 (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty2 ty1 -∗
    type_incl #r1 #r2 (shr_ref κ2 ty2) (shr_ref κ1 ty1).
  Proof.
    iIntros "#Hincl #Hsub".
    iSplitR; first done. iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (??). by iApply shr_ref_own_val_mono_in.
    - iIntros (???). by iApply shr_ref_shr_mono_in.
  Qed.
  Lemma shr_ref_type_incl {rt} κ2 κ1 (ty1 ty2 : type rt) r :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    type_incl r r (shr_ref κ2 ty2) (shr_ref κ1 ty1).
  Proof.
    iIntros "#Hincl #Hsub".
    iSplitR; first done. iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (??). by iApply shr_ref_own_val_mono.
    - iIntros (???). by iApply shr_ref_shr_mono.
  Qed.

  Lemma shr_ref_full_subtype {rt} E L κ2 κ1 (ty1 ty2 : type rt) :
    lctx_lft_incl E L κ1 κ2 →
    full_subtype E L ty2 ty1 →
    full_subtype E L (shr_ref κ2 ty2) (shr_ref κ1 ty1).
  Proof.
    iIntros (Hincl Hsubt r ?) "HL #HE".
    iPoseProof (Hincl with "HL") as "#Hincl".
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_subtype_acc_noend with "HE HL") as "#Hsubt"; first apply Hsubt.
    iApply shr_ref_type_incl; done.
  Qed.
End subtype.


