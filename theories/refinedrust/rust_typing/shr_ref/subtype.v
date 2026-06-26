From refinedrust Require Export type ltypes.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Subtyping lemmas for shared references *)

Section subtype.
  Context `{typeGS Σ}.

  Lemma shr_ref_own_val_mono_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) v π r1 r2 κ1 κ2 m :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    v ◁ᵥ{π, m} #r1 @ shr_ref κ2 ty1 -∗
    v ◁ᵥ{π, m} #r2 @ shr_ref κ1 ty2.
  Proof.
    iIntros "%Hcomp #Hincl (#Hsc_eq & _ & #Hincl_shr)".
    rewrite /ty_own_val/= shr_ref_own_val_unfold.
    iIntros "(%l & %ly & %r' & -> & %Hvl & %Halg & %Hly & Hlb & Hsc & -> & #Hl)". iExists l, ly, r2.
    iR. iR.
    iSplitR. { iPureIntro. change (syn_type_has_layout (st_of ty2 MetaNone) ly). by apply Hcomp. }
    iFrame.
    iR.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iR. iModIntro. iMod "Hl". iModIntro.
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.
  Lemma shr_ref_own_val_mono {rt} (ty1 ty2 : type rt) v π r κ1 κ2 m :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ᵥ{π, m} r @ shr_ref κ2 ty1 -∗
    v ◁ᵥ{π, m} r @ shr_ref κ1 ty2.
  Proof.
    iIntros "%Hcomp #Hincl #Hsub".
    iDestruct ("Hsub" $! inhabitant) as "(#Hsc_eq & _)".
    rewrite /ty_own_val/= shr_ref_own_val_unfold.
    iIntros "(%l & %ly & %r' & -> & %Hvl & %Halg & %Hly & Hlb & Hsc & Hr & #Hl)". iExists l, ly, r'.
    iR. iR.
    iSplitR. { iPureIntro. change (syn_type_has_layout (st_of ty2 MetaNone) ly). by apply Hcomp. }
    iFrame.
    iR.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iModIntro. iMod "Hl". iModIntro.
    iPoseProof ("Hsub" $! r') as "(_ & _ & #Hincl_shr)".
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.

  Lemma shr_ref_shr_mono_in {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) l π κ r1 r2 κ1 κ2 m :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    l ◁ₗ{π, m, κ} #r1 @ shr_ref κ2 ty1 -∗
    l ◁ₗ{π, m, κ} #r2 @ shr_ref κ1 ty2.
  Proof.
    iIntros "%Hcomp #Hincl (#Hsc_eq & _ & #Hincl_shr)".
    rewrite /ty_shr/= shr_ref_shr_unfold.
    iIntros "(%li & %ly & %r' & -> & %Hlyl & %Halg & %Hliy & Hlb & Hsc & -> & Hli & #Hb)".
    iExists li, ly, r2. iFrame. iR. iR.
    iSplitR. { iPureIntro. change (syn_type_has_layout (st_of ty2 MetaNone) ly). by apply Hcomp. }
    iFrame. iR.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iR. iModIntro. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.
  Lemma shr_ref_shr_mono {rt} (ty1 ty2 : type rt) l π κ r κ1 κ2 m :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    l ◁ₗ{π, m, κ} r @ shr_ref κ2 ty1 -∗
    l ◁ₗ{π, m, κ} r @ shr_ref κ1 ty2.
  Proof.
    iIntros "%Hcomp #Hincl #Hsub".
    rewrite /ty_shr/= shr_ref_shr_unfold.
    iPoseProof ("Hsub" $! inhabitant) as "(#Hsc_eq & _)".
    iIntros "(%li & %ly & %r' & -> & %Hlyl & %Halg & %Hliy & Hlb & Hsc & Hr & Hli & #Hb)".
    iExists li, ly, r'. iFrame. iR. iR.
    iSplitR. { iPureIntro. change (syn_type_has_layout (st_of ty2 MetaNone) ly). by apply Hcomp. }
    iFrame. iR.
    iSplitL "Hsc". { by iApply "Hsc_eq". }
    iModIntro. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iPoseProof ("Hsub" $! r') as "(_ & _ & #Hincl_shr)".
    iApply ty_shr_mono; first iApply "Hincl".
    by iApply "Hincl_shr".
  Qed.

  Lemma shr_ref_type_incl_in {rt1 rt2} κ2 κ1 (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    ⌜syn_type_compat (ty2.(ty_syn_type) MetaNone) (ty1.(ty_syn_type) MetaNone)⌝ -∗
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty2 ty1 -∗
    type_incl #r1 #r2 (shr_ref κ2 ty2) (shr_ref κ1 ty1).
  Proof.
    iIntros "%Hcomp #Hincl #Hsub".
    iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (???). iApply (shr_ref_own_val_mono_in with "[] Hincl Hsub"). done.
    - iIntros (????). iApply (shr_ref_shr_mono_in with "[] Hincl Hsub"). done.
  Qed.
  Lemma shr_ref_type_incl {rt} κ2 κ1 (ty1 ty2 : type rt) r :
    ⌜syn_type_compat (ty2.(ty_syn_type) MetaNone) (ty1.(ty_syn_type) MetaNone)⌝ -∗
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    type_incl r r (shr_ref κ2 ty2) (shr_ref κ1 ty1).
  Proof.
    iIntros "%Hcomp #Hincl #Hsub".
    iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (???). iApply (shr_ref_own_val_mono with "[] Hincl Hsub"). done.
    - iIntros (????). iApply (shr_ref_shr_mono with "[] Hincl Hsub"). done.
  Qed.

  Lemma shr_ref_full_subtype {rt} E L κ2 κ1 (ty1 ty2 : type rt) :
    lctx_lft_incl E L κ1 κ2 →
    full_subtype E L ty2 ty1 →
    full_subtype E L (shr_ref κ2 ty2) (shr_ref κ1 ty1).
  Proof.
    iIntros (Hincl Hsubt r ?) "HL #HE".
    iPoseProof (Hincl with "HL") as "#Hincl".
    iSpecialize ("Hincl" with "HE").
    iPoseProof (full_subtype_acc_noend with "HE HL") as "(%Hst & #Hsubt)"; first apply Hsubt.
    iSplitR. { done. }
    iApply (shr_ref_type_incl with "[] Hincl Hsubt").
    rewrite Hst//.
  Qed.
End subtype.
