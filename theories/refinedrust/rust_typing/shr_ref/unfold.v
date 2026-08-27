From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def subltype.
From refinedrust Require Import options.

(** ** Unfolding [shr_ref] into [ShrLtype] *)
Section ofty.
  Context `{!typeGS Σ}.

  (** A very fundamental equivalence that should hold *)
  Lemma shr_ref_ofty_shared_equiv {rt} (ty : type rt) π κ l r :
    l ◁ₗ[π, Shared κ] #r @ (◁ ty) ⊣⊢ l ◁ᵥ{π, MetaNone} #r @ shr_ref κ ty.
  Proof.
    rewrite ltype_own_ofty_unfold/lty_of_ty_own /ty_own_val/= shr_ref_own_val_unfold.
    iSplit.
    - iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & %Hconc & %r' & <- & #Ha)".
      iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
      iPoseProof (loc_in_bounds_nonnull with "Hlb") as "%Hnonnull".
      iExists l, ly, r. iR.
      iSplitR. { iPureIntro. by apply l2v_decodes_to_ref. }
      iR. iR. iR. iFrame "#". iSplitR; first done.
      iPoseProof (ty_shr_box_fupd_is_xrfn with "Ha") as "#Hcanon".
      iModIntro. iMod "Hcanon" as "(%Hxr & #Ha')". iModIntro.
      iSplitR; first (iPureIntro; by apply is_xrfn_place_in).
      iFrame "# %".
    - iIntros "(%l' & %ly & %r' & _ & %Hl & % & % & #Hlb & #Hsc & <- & #Ha)".
      iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
      apply val_decodes_to_ref_l2v_inv in Hl. subst.
      iExists _. iR. iR. iFrame "#".
      iSplitR; first (iPureIntro; apply place_rfn_is_concrete_in).
      iExists r. iR. iModIntro. iMod "Ha" as "(_ & _ & Ha)". iFrame. done.
  Qed.
End ofty.

Section ltype_agree.
  Context `{typeGS Σ}
    {rt : RT}
    (ty : type rt).

  Lemma shr_ref_unfold_1_owned κ r :
    ⊢ ltype_incl' (Owned) r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & #Hlb & %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly.
    iFrame. iR. iMod "Hb" as "(%Hxr & %l' & Hl & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb' & %Hconc & %ri' & Hrfn' & Hb)".
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb'") as "%".
    rewrite /ty_own_val/= shr_ref_own_val_unfold.
    iModIntro. iFrame.
    iDestruct "Hl" as "(%v & Hl & %Hdec)".
    iExists v. iFrame. iR. iR. iSplitR; first done.
    iApply (ty_shr_box_fupd_is_xrfn with "Hb").
  Qed.

  Lemma shr_ref_unfold_1_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & %Ha & % & #Hlb & %Hconc & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. do 4 iR.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%Hxr & %vi & %li & #Hs & %Hdec & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    rewrite /ty_shr/= shr_ref_shr_unfold.
    iDestruct "Hb" as "(%ly' & >? & >? & >Hsc & >Hlb' & >? & %r' & >Hrfn & Hb)".
    iModIntro.
    iExists vi, li, ly', r'. iFrame. iR.
    iSplitR. { apply syn_type_has_layout_ref_inv in Ha as ?. subst. done. }
    iFrame "Hs". iSplitR.
    { iPureIntro. apply syn_type_has_layout_ref_inv in Ha as ->. exact H0. }
    iSplitR; first done.
    iNext. iApply (ty_shr_box_fupd_is_xrfn with "Hb").
  Qed.

  Lemma shr_ref_unfold_1_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & ? & ? & ?  & Hb)". iExists ly. iFrame. iMod "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%Hxr & %l' & Hl & Hb)".
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %Hconc & %ri & Hrfn & Hb)".
        iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
        iDestruct "Hl" as "(%v & Hl & %Hdec)".
        iExists v. iModIntro. iFrame. iR. iR. iSplitR; first done.
         iApply (ty_shr_box_fupd_is_xrfn with "Hb").
      * iIntros "(%r' & Hauth & Hb)". iExists _; iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
         iDestruct "Hb" as "(%li & %ly' & %ri & _ & %Heq & ? & ? & Hlb & Hsc & Hrfn & #Hb)".
         iMod "Hb" as "(%Hxr & _ & #Hty)". iModIntro. iSplitR; first done.
        iExists li. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iFrame. iSplitR; first done. iSplitR.
        { iPureIntro. by apply is_xrfn_place_rfn_is_concrete. }
         iModIntro. iFrame "#". done.
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%Hxr & %l' & Hl & Hb)".
        rewrite ltype_own_core_equiv. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %Hconc & %ri & Hrfn & Hb)".
        iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
        iDestruct "Hl" as "(%v & Hl & %Hdec)".
        iExists v. iModIntro. iFrame. iR. iR. iSplitR; first done.
         iApply (ty_shr_box_fupd_is_xrfn with "Hb").
      * iIntros "(%r' & Hauth & Hb)". iExists _; iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
         iDestruct "Hb" as "(%li & %ly' & %ri & _ & %Heq & ? & ? & Hlb & Hsc & Hrfn & #Hb)".
         iMod "Hb" as "(%Hxr & _ & #Hty)". iModIntro. iSplitR; first done.
        iExists li. iFrame.
        rewrite ltype_own_core_equiv. simp_ltype.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iFrame. iSplitR; first done. iSplitR.
        { iPureIntro. by apply is_xrfn_place_rfn_is_concrete. }
         iModIntro. iFrame "#". done.
  Qed.

  Local Lemma shr_ref_unfold_1' κ k r :
    ⊢ ltype_incl' k r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. destruct k.
    - iApply shr_ref_unfold_1_owned.
    - iApply shr_ref_unfold_1_shared.
    - iApply shr_ref_unfold_1_uniq.
  Qed.
  Lemma shr_ref_unfold_1 κ k r :
    ⊢ ltype_incl k r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iSplit.
    - iApply shr_ref_unfold_1'.
    - simp_ltypes. iApply shr_ref_unfold_1'.
  Qed.

  Lemma shr_ref_unfold_2_owned κ r :
    ⊢ ltype_incl' (Owned) r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    rewrite /ty_own_val/= shr_ref_own_val_unfold.
    iIntros "(%ly & ? & ? & Hsc & Hlb & %r' & Hrfn & Hb)".
    iModIntro. iExists ly. iFrame.
    iMod "Hb" as "(%v & Hl & Hb)".
    iDestruct "Hb" as "(%li & %ly' & %ri & _ & %Heq & %Halg' & %Hly' & Hlb' & Hsc' & Hrfn' & #Hb)".
    iMod "Hb" as "(%Hxr & _ & #Hty)". iModIntro. iSplitR; first done.
    iExists li. iFrame. iSplitR; first done. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. iSplitR; first done. iSplitR; first done.
    iFrame "Hsc' Hlb'". iSplitR.
    { iPureIntro. by apply is_xrfn_place_rfn_is_concrete. }
    iExists ri. iFrame "Hrfn'". iModIntro. iFrame "#". done.
  Qed.

  Lemma shr_ref_unfold_2_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    rewrite /ty_shr/= shr_ref_shr_unfold.
    iIntros "(%ly & %Halg & %Hl & Hsc & Hlb & %Hconc & %r' & Hrfn & #Hb)". iExists ly. iFrame.
    iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%vi & %li & %ly' & %ri & %Hxr & _ & ? & %Hly & %Hlli & Hlb' & Hsc & Hrfn & Hs & %Hdec & Hb)".
    iModIntro. iSplitR; first done. iExists vi, li. iFrame. iSplitR; first done. iNext. iDestruct "Hb" as "#Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. iFrame "Hsc Hlb' %". iSplitR.
    { iPureIntro. destruct Hxr as [xr ->]. apply place_rfn_is_concrete_in. }
    iExists ri. iFrame "Hrfn #".
    iModIntro. iMod "Hb" as "(_ & Hb)". iFrame. done.
  Qed.

  Lemma shr_ref_unfold_2_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    (* same proof as above essentially *)
    iIntros "(%ly & ? & ? & Hsc & ? & ? & ? & Hb)". iExists ly. iFrame. iMod "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
         iDestruct "Hb" as "(%li & %ly' & %ri & _ & % & ? & ? & Hlb & Hsc & Hrfn & #Hb)".
         iMod "Hb" as "(%Hxr & _ & #Hty)". iModIntro. iSplitR; first done.
        iExists li. iFrame. iSplitR; first done. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'. iFrame. iSplitR.
        { iPureIntro. by apply is_xrfn_place_rfn_is_concrete. }
        iModIntro. iFrame "#". done.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%Hxr & %l' & Hl & Hb)".
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %Hconc & %ri & Hrfn & Hb)".
        iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
        iDestruct "Hl" as "(%v & Hl & %Hdec)".
        iExists v. iModIntro. iFrame. iR. iR. iSplitR; first done.
        iApply (ty_shr_box_fupd_is_xrfn with "Hb").
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
         iDestruct "Hb" as "(%li & %ly' & %ri & _ & % & ? & ? & Hlb & Hsc & Hrfn & #Hb)".
         iMod "Hb" as "(%Hxr & _ & #Hty)". iModIntro. iSplitR; first done.
        iExists li.
        iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
        iFrame. iSplitR; first done. rewrite ltype_own_core_equiv. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'. iFrame. iSplitR.
        { iPureIntro. by apply is_xrfn_place_rfn_is_concrete. }
        iModIntro. iFrame "#". done.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%Hxr & %l' & Hl & Hb)". rewrite ltype_own_core_equiv. simp_ltype.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        rewrite /ty_own_val/= shr_ref_own_val_unfold.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %Hconc & %ri & Hrfn & Hb)".
        iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
        iDestruct "Hl" as "(%v & Hl & %Hdec)".
        iExists v. iModIntro. iFrame. iR. iR. iSplitR; first done.
        iApply (ty_shr_box_fupd_is_xrfn with "Hb").
  Qed.

  Local Lemma shr_ref_unfold_2' κ k r :
    ⊢ ltype_incl' k r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    destruct k.
    - iApply shr_ref_unfold_2_owned.
    - iApply shr_ref_unfold_2_shared.
    - iApply shr_ref_unfold_2_uniq.
  Qed.

  Lemma shr_ref_unfold_2 κ k r :
    ⊢ ltype_incl k r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro; iSplit.
    - iApply shr_ref_unfold_2'.
    - simp_ltypes. iApply shr_ref_unfold_2'.
  Qed.

  Lemma shr_ref_unfold κ k r :
    ⊢ ltype_eq k r r (ShrLtype (◁ (ty)) κ) (◁ (shr_ref κ ty)).
  Proof.
    iSplit.
    - iApply shr_ref_unfold_1.
    - iApply shr_ref_unfold_2.
  Qed.

  Lemma shr_ref_unfold_full_eqltype E L κ (lt : ltype rt) :
    full_eqltype E L lt (◁ ty)%I →
    full_eqltype E L (ShrLtype lt κ) (◁ (shr_ref κ ty))%I.
  Proof.
    iIntros (Heql ?) "HL #CTX #HE". iR. iIntros (??).
    iPoseProof (Heql with "HL CTX HE") as "(_ & #Heql)".
    iApply ltype_eq_trans; last iApply shr_ref_unfold.
    iApply shr_ltype_eq; [ | iApply lft_incl_refl.. ].
    by iApply "Heql".
  Qed.
End ltype_agree.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_ofty_shr {rt} E L f l (ty : type rt) κ (r : place_rfn (place_rfn rt)) bmin0 b P T :
    typed_place E L f l (ShrLtype (◁ ty) κ) r bmin0 b P T
    ⊢ typed_place E L f l (◁ (shr_ref κ ty)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last done.
    iIntros (?) "HL CTX HE".
    iR. iIntros (??). iApply ltype_eq_sym. iApply shr_ref_unfold.
  Qed.
  Definition typed_place_ofty_shr_inst := [instance @typed_place_ofty_shr].
  Global Existing Instance typed_place_ofty_shr_inst | 30.
End place.

Section cast.
  Context `{!typeGS Σ}.

  (** cast_ltype *)
  Lemma cast_ltype_to_type_shr E L {rt} (lt : ltype rt) κ T  :
    cast_ltype_to_type E L lt (λ ty, T (shr_ref κ ty))
    ⊢ cast_ltype_to_type E L (ShrLtype lt κ) T.
  Proof.
    iIntros "Hs". iDestruct "Hs" as "(%ty & %Heq & HT)".
    iExists (shr_ref κ ty). iFrame "HT". iPureIntro.
    by apply shr_ref_unfold_full_eqltype.
  Qed.
  Definition cast_ltype_to_type_shr_inst := [instance @cast_ltype_to_type_shr].
  Global Existing Instance cast_ltype_to_type_shr_inst.
End cast.
