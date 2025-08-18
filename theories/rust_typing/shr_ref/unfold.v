From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def subltype.
From refinedrust Require Import options.

(** ** Unfolding [shr_ref] into [ShrLtype] *)
Section ofty.
  Context `{!typeGS Σ}.

  (** A very fundamental equivalence that should hold *)
  Lemma shr_ref_ofty_shared_equiv {rt} (ty : type rt) π κ l r :
    l ◁ₗ[π, Shared κ] #r @ (◁ ty) ⊣⊢ l ◁ᵥ{π} #r @ shr_ref κ ty.
  Proof.
    rewrite ltype_own_ofty_unfold/lty_of_ty_own /ty_own_val/=.
    iSplit.
    - iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & %r' & <- & #Ha)".
      iExists _, _, _. iR. iR. iR. iFrame "#". done.
    -iIntros "(%l' & %ly & %r' & %Hl & % & % & #Hsc & #Hlb & <- & #Ha)".
      apply val_of_loc_inj in Hl. subst.
      iExists _. iR. iR. iFrame "#". done.
  Qed.
End ofty.

Section ltype_agree.
  Context `{typeGS Σ}
    {rt : RT}
    (ty : type rt).

  Lemma shr_ref_unfold_1_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & #Hlb & ? &  %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly.
    iFrame. iR. iNext. iMod "Hb" as "(%l' & Hl & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb' & %ri' & Hrfn' & Hb)".
    iModIntro. iFrame. done.
  Qed.

  Lemma shr_ref_unfold_1_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & %Ha & % & #Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. do 3 iR.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & #Hs & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & >? & >? & >Hsc & >Hlb' & %r' & >Hrfn & Hb)".
    iModIntro.
    iExists _, _, _. iFrame. iSplitR; last done.
    apply syn_type_has_layout_ptr_inv in Ha as ?. subst. done.
  Qed.

  Lemma shr_ref_unfold_1_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (ShrLtype (◁ ty) κ) (◁ (shr_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & ? & ? & ?  & Hb)". iExists ly. iFrame. iMod "Hb". iModIntro.
    iApply (pinned_bor_iff with "[] [] Hb").
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iExists l'. iFrame.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', ly', _. iFrame. done.
      * iIntros "(%r' & Hauth & Hb)". iExists _; iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        by iFrame.
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iExists l'. iFrame.
        rewrite ltype_own_core_equiv. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', ly', _. iFrame. done.
      * iIntros "(%r' & Hauth & Hb)". iExists _; iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame.
        rewrite ltype_own_core_equiv. simp_ltype.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        by iFrame.
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
    iSplitR; first done. iModIntro. iSplit.
    - iApply shr_ref_unfold_1'.
    - simp_ltypes. iApply shr_ref_unfold_1'.
  Qed.

  Lemma shr_ref_unfold_2_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & Hlb & ? & %r' & Hrfn & Hb)".
    iModIntro. iExists ly. iFrame.
    iModIntro.
    iMod "Hb" as "(%v & Hl & %li & %ly' & %ri & -> & ? & ? & Hlb' & Hsc' & Hrfn' & Hb)".
    iModIntro.
    iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. iFrame.
  Qed.

  Lemma shr_ref_unfold_2_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (◁ (shr_ref κ ty)) (ShrLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_shr_ref_unfold /shr_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & Hlb & %r' & Hrfn & #Hb)". iExists ly. iFrame.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & %ly' & %ri & ? & ? & ? & Hlb' & Hsc & Hrfn & Hs & Hb)".
    iModIntro. iExists _. iFrame. iNext. iDestruct "Hb" as "#Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. by iFrame.
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
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'. by iFrame.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)".
        iExists l'. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', _, _. iFrame. done.
    - iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%v & Hl & Hb)".
        iDestruct "Hb" as "(%li & %ly' & %ri & -> & ? & ? & Hlb & Hsc & Hrfn & Hb)".
        iExists _. iFrame. rewrite ltype_own_core_equiv. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'. by iFrame.
      * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)".
        iExists l'. iFrame. rewrite ltype_own_core_equiv. simp_ltype.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb & %ri & Hrfn & Hb)".
        iExists l', _, _. iFrame. done.
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
    iSplitR; first done. iModIntro; iSplit.
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
    iIntros (Heql ?) "HL #CTX #HE". iIntros (??).
    iPoseProof (Heql with "HL CTX HE") as "#Heql".
    iApply ltype_eq_trans; last iApply shr_ref_unfold.
    iApply shr_ltype_eq; [ | iApply lft_incl_refl.. ].
    by iApply "Heql".
  Qed.
End ltype_agree.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_ofty_shr {rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt)) bmin0 b P T :
    typed_place π E L l (ShrLtype (◁ ty) κ) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (shr_ref κ ty)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last done.
    iIntros (?) "HL CTX HE".
    iIntros (??). iApply ltype_eq_sym. iApply shr_ref_unfold.
  Qed.
  Global Instance typed_place_ofty_shr_inst {rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt)) bmin0 b P :
    TypedPlace E L π l (◁ (shr_ref κ ty))%I r bmin0 b P | 30 := λ T, i2p (typed_place_ofty_shr π E L l ty κ r bmin0 b P T).

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
  Global Instance cast_ltype_to_type_shr_inst E L {rt} (lt : ltype rt) κ :
    CastLtypeToType E L (ShrLtype lt κ) :=
    λ T, i2p (cast_ltype_to_type_shr E L lt κ T).

End cast.

