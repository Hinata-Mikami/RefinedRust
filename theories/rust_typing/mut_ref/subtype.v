From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def.
From refinedrust Require Import options.

(** ** Subtyping lemmas for mutable references *)

Section subtype.
  Context `{!typeGS Σ}.

  Lemma mut_ref_own_val_mono {rt} (ty1 ty2 : type rt) v π r κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    v ◁ᵥ{π} r @ mut_ref κ2 ty1 -∗
    v ◁ᵥ{π} r @ mut_ref κ1 ty2.
  Proof.
    destruct r as [r γ].
    iIntros "#Hincl #Ht12 #Ht21 (%l & %ly & -> & ? & Hly & Hlb & Hsc & Hobs & ? & Hb)".
    iDestruct ("Ht12" $! inhabitant) as "(%Hst & #Hsceq & _)".
    (*iDestruct "Ht21" as "(_ & _ & #Hv21 & #Hs21)".*)
    iExists l, ly. iFrame. iSplitR; first done.
    rewrite -Hst. iFrame. iSplitL "Hsc". { by iApply "Hsceq". }
    iMod "Hb". iModIntro.
    iApply (pinned_bor_shorten with "Hincl").
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    + iIntros "(%r' & Hauth & Hv)". iExists r'. iFrame.
      iMod "Hv" as "(%v & Hl & Hv)". iModIntro. iExists v. iFrame.
      iDestruct ("Ht12" $! r') as "(_ & _ & Hv12 & _)". by iApply "Hv12".
    + iIntros "(%r' & Hauth & Hv)". iExists r'. iFrame.
      iMod "Hv" as "(%v & Hl & Hv)". iModIntro. iExists v. iFrame.
      iDestruct ("Ht21" $! r') as "(_ & _ & Hv21 & _)". by iApply "Hv21".
  Qed.

  Lemma mut_ref_shr_mono_in {rt} (ty1 ty2 : type rt) l π r1 r2 γ κ κ1 κ2 :
    κ1 ⊑ κ2 -∗
    type_incl r1 r2 ty1 ty2 -∗
    l ◁ₗ{π, κ} (#r1, γ) @ mut_ref κ2 ty1 -∗
    l ◁ₗ{π, κ} (#r2, γ) @ mut_ref κ1 ty2.
  Proof.
    iIntros "#Hincl #Ht12 (%li & %ly & %r' & ? & <- & Hs & ? & ? & ? & ? & Hsc & Hb)".
    iDestruct "Ht12" as "(%Hst & #Hsceq & #Hv12 & #Hs12)".
    iExists li, ly, r2. iFrame. iR. rewrite Hst. iFrame.
    iSplitL "Hsc". { by iApply "Hsceq". }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono.
    { iApply lft_incl_glb.
      + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply "Hincl".
      + iApply lft_intersect_incl_r. }
    by iApply "Hs12".
  Qed.
  Lemma mut_ref_shr_mono {rt} (ty1 ty2 : type rt) l π r κ κ1 κ2 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    l ◁ₗ{π, κ} r @ mut_ref κ2 ty1 -∗
    l ◁ₗ{π, κ} r @ mut_ref κ1 ty2.
  Proof.
    destruct r as [r γ].
    iIntros "#Hincl #Ht12 (%li & %ly & %r' & ? & ? & Hs & ? & ? & ? & ? & Hsc & Hb)".
    iDestruct ("Ht12" $! inhabitant) as "(%Hst & #Hsceq & _)".
    iExists li, ly, r'. iFrame. rewrite Hst. iFrame.
    iSplitL "Hsc". { by iApply "Hsceq". }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono.
    { iApply lft_incl_glb.
      + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply "Hincl".
      + iApply lft_intersect_incl_r. }
    iDestruct ("Ht12" $! r') as "(_ & _ & _ & #Hs12)". by iApply "Hs12".
  Qed.

  Lemma mut_ref_type_incl {rt} (ty1 ty2 : type rt) r κ2 κ1 :
    κ1 ⊑ κ2 -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    (∀ r, type_incl r r ty2 ty1) -∗
    type_incl r r (mut_ref κ2 ty1) (mut_ref κ1 ty2).
  Proof.
    iIntros "#Hincl #Ht12 #Ht21". iSplitR; first done. iSplitR; first done.
    iSplit; iIntros "!#".
    - iIntros (??). by unshelve iApply mut_ref_own_val_mono.
    - iIntros (???). by unshelve iApply mut_ref_shr_mono.
  Qed.

  Lemma mut_ref_full_subtype {rt} E L (ty1 ty2 : type rt) κ1 κ2 :
    full_eqtype E L ty1 ty2 →
    lctx_lft_incl E L κ2 κ1 →
    full_subtype E L (mut_ref κ1 ty1) (mut_ref κ2 ty2).
  Proof.
    iIntros (Hsub1 Hincl r qL) "HL #HE".
    iPoseProof (full_eqtype_acc_noend with "HE HL") as "#Heq"; first done.
    iPoseProof (Hincl with "HL HE") as "#Hincl".
    iApply mut_ref_type_incl; [done | ..].
    - iIntros (r'). iDestruct ("Heq" $! r') as "($ & _)".
    - iIntros (r'). iDestruct ("Heq" $! r') as "(_ & $)".
  Qed.
End subtype.
