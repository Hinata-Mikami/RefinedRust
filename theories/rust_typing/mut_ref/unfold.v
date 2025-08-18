From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def subltype.
From refinedrust Require Import options.

(** ** Unfolding mutable references into [MutLtype] *)
Section ofty.
  Context `{!typeGS Σ}.

  (** A very fundamental equivalence that should hold. *)
  Lemma mut_ref_ofty_uniq_equiv {rt} (ty : type rt) π κ l r γ :
    l ◁ₗ[π, Uniq κ γ] #r @ (◁ ty) ⊣⊢ l ◁ᵥ{π} (#r, γ) @ mut_ref κ ty.
  Proof.
    rewrite ltype_own_ofty_unfold/lty_of_ty_own {3}/ty_own_val/=.
    iSplit.
    - iIntros "(%ly & %Hst & %Hly & #Hsc & #Hlb & Hc & Hobs & Hb)".
      iExists _, _. iR. iR. iR. iFrame "# ∗".
    -iIntros "(%l' & %ly & %Hl & % & % & #Hlb & #Hsc & Hobs & Hc & Hb)".
      apply val_of_loc_inj in Hl. subst.
      iExists _. iR. iR. iFrame "# ∗".
  Qed.
End ofty.


Section ltype_agree.
  Context `{typeGS Σ}
    {rt : RT}
    (ty: type rt).

  Lemma mut_ref_unfold_1_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (MutLtype (◁ ty) κ) (◁ (mut_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hlb & ? & %γ & %r' & Hrfn & Hb)".
    iModIntro.
    iExists ly. iFrame "∗". iNext.
    iMod "Hb" as "(%l' & Hl & Hb)".
    iExists l'. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & ? & ? & Hsc & Hlb' & ? & Hrfn'  & Hb)".
    iExists l'. iFrame. done.
  Qed.

  Lemma mut_ref_unfold_1_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (MutLtype (◁ ty) κ) (◁ (mut_ref κ ty)).
  Proof.
    iModIntro.
    iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & %Hly & ? & ? & ? & Hb)". iExists ly. iFrame "∗". iSplitR; first done.
    iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv. simp_ltypes.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%l' & Hl & Hb)".
      iExists l'. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own. destruct r' as [r' γ'].
      iDestruct "Hb" as "(%ly' & Hst' & Hly' & Hsc & Hlb & ? & Hrfn & >Hb)".
      iModIntro. iExists l', ly'. iFrame "∗". iSplitR; first done. by iFrame.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%v & Hl & Hb)". destruct r' as [r' γ'].
      iDestruct "Hb" as "(%l' & %ly' & -> & ? & ? & Hlb & Hsc & Hrfn & ? & >Hb)".
      iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iModIntro. iExists ly'. iFrame. done.
  Qed.

  Lemma mut_ref_unfold_1_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (MutLtype (◁ ty) κ) (◁ (mut_ref κ ty)).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & %Hst & % & #Hlb & %ri & %γ & Hrfn & #Hb)".
    apply syn_type_has_layout_ptr_inv in Hst as ?. subst.
    iExists _. iFrame "# ∗". iSplitR; first done. iSplitR; first done.
    iModIntro. iMod "Hb" as "(%li & Hs & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly' & >? & >? & >Hsc & >Hlb' & %r' & >Hrfn & #Hb)".
    iModIntro. iExists _, _. iFrame "∗ #". done.
  Qed.

  Local Lemma mut_ref_unfold_1' κ k r :
    ⊢ ltype_incl' k r r (MutLtype (◁ ty) κ) (◁ (mut_ref κ ty)).
  Proof.
    destruct k.
    - iApply mut_ref_unfold_1_owned.
    - iApply mut_ref_unfold_1_shared.
    - iApply mut_ref_unfold_1_uniq.
  Qed.

  Lemma mut_ref_unfold_1 κ k r :
    ⊢ ltype_incl k r r (MutLtype (◁ ty) κ) (◁ (mut_ref κ ty)).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    - iApply mut_ref_unfold_1'.
    - simp_ltypes. iApply mut_ref_unfold_1'.
  Qed.

  Lemma mut_ref_unfold_2_owned κ wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (mut_ref κ ty)) (MutLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & _ & #Hlb & ? & %r' & Hrfn & Hb)". destruct r' as [r' γ'].
    (*iApply except_0_if_intro.*)
    iModIntro. iExists ly. iFrame "∗ #". iNext.
    iMod "Hb" as "(%v & Hl & %l' & %ly' & -> & ? & ? & #Hlb' & Hsc & ? &  Hrfn' & >Hb)".
    iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly'. iFrame "∗ #". done.
  Qed.

  Lemma mut_ref_unfold_2_uniq κ κ' γ r :
    ⊢ ltype_incl' (Uniq κ' γ) r r (◁ (mut_ref κ ty)) (MutLtype (◁ ty) κ).
  Proof.
    iModIntro.
    iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? &  _ & Hlb & ? &  Hrfn & Hb)". iExists ly. iFrame "∗". iMod "Hb".
    iModIntro.
    setoid_rewrite ltype_own_core_equiv. simp_ltypes.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%v & Hl & Hb)". destruct r' as [r' γ'].
      iDestruct "Hb" as "(%l' & %ly' & -> & ? & ? & Hlb & Hsc & Hrfn & ? & >Hb)".
      iExists _. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iModIntro. iExists ly'. iFrame. done.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iMod "Hb" as "(%l' & Hl & Hb)".
      iExists l'. iFrame. rewrite ltype_own_ofty_unfold /lty_of_ty_own. destruct r' as [r' γ'].
      iDestruct "Hb" as "(%ly' & Hst' & Hly' & Hsc & Hlb & ? &  Hrfn & >Hb)".
      iModIntro. iExists l', ly'. iFrame "∗". iSplitR; first done. by iFrame.
  Qed.

  Lemma mut_ref_unfold_2_shared κ κ' r :
    ⊢ ltype_incl' (Shared κ') r r (◁ (mut_ref κ ty)) (MutLtype (◁ ty) κ).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_mut_ref_unfold /mut_ltype_own ltype_own_ofty_unfold /lty_of_ty_own.
    iIntros "(%ly & ? & ? & Hsc & Hlb & %r' & Hrfn & #Hb)". destruct r' as [r' γ'].
    iExists ly. iFrame "∗ #".
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & %ly' & %ri & ? & Hrfn' & Hs & ? & ? & Hlb & Hlb' & Hsc & #Hb)".
    iModIntro. iExists li. iFrame.
    iNext. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly'. by iFrame.
  Qed.

  Local Lemma mut_ref_unfold_2' κ k r :
    ⊢ ltype_incl' k r r (◁ (mut_ref κ ty)) (MutLtype (◁ ty) κ).
  Proof.
    destruct k.
    - iApply mut_ref_unfold_2_owned.
    - iApply mut_ref_unfold_2_shared.
    - iApply mut_ref_unfold_2_uniq.
  Qed.

  Lemma mut_ref_unfold_2 κ k r :
    ⊢ ltype_incl k r r (◁ (mut_ref κ ty)) (MutLtype (◁ ty) κ).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    - iApply mut_ref_unfold_2'.
    - simp_ltypes. iApply mut_ref_unfold_2'.
  Qed.

  Lemma mut_ref_unfold κ k r :
    ⊢ ltype_eq k r r (MutLtype (◁ ty) κ) (◁ (mut_ref κ ty)).
  Proof.
    iSplit; iModIntro.
    - iApply mut_ref_unfold_1.
    - iApply mut_ref_unfold_2.
  Qed.

  Lemma mut_ref_unfold_full_eqltype E L κ (lt : ltype rt) :
    full_eqltype E L lt (◁ ty)%I →
    full_eqltype E L (MutLtype lt κ) (◁ (mut_ref κ ty))%I.
  Proof.
    iIntros (Heql ?) "HL #CTX #HE". iIntros (b r).
    iPoseProof (Heql with "HL CTX HE") as "#Heql".
    iApply ltype_eq_trans; last iApply mut_ref_unfold.
    iApply mut_ltype_eq; [ | iApply lft_incl_refl.. ].
    by iApply "Heql".
  Qed.
End ltype_agree.

Section place.
  Context `{!typeGS Σ}.

  (* This needs to have a lower priority than the id instances, because we do not want to unfold when P = []. *)
  Lemma typed_place_ofty_mut {rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)%type) bmin0 b P T :
    typed_place π E L l (MutLtype (◁ ty) κ) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (mut_ref κ ty)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last done.
    iIntros (?) "HL CTX HE". iIntros (??).
    iApply ltype_eq_sym. iApply mut_ref_unfold.
  Qed.
  Global Instance typed_place_ofty_mut_inst {rt} π E L l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)%type) bmin0 b P :
    TypedPlace E L π l (◁ (mut_ref κ ty))%I r bmin0 b P | 30 := λ T, i2p (typed_place_ofty_mut π E L l ty κ r bmin0 b P T).
End place.

Section cast.
  Context `{!typeGS Σ}.

  (** cast_ltype *)
  Lemma cast_ltype_to_type_mut E L {rt} (lt : ltype rt) κ T  :
    cast_ltype_to_type E L lt (λ ty, T (mut_ref κ ty))
    ⊢ cast_ltype_to_type E L (MutLtype lt κ) T.
  Proof.
    iIntros "Hs". iDestruct "Hs" as "(%ty & %Heq & HT)".
    iExists (mut_ref κ ty). iFrame "HT". iPureIntro.
    by apply mut_ref_unfold_full_eqltype.
  Qed.
  Global Instance cast_ltype_to_type_mut_inst E L {rt} (lt : ltype rt) κ :
    CastLtypeToType E L (MutLtype lt κ) :=
    λ T, i2p (cast_ltype_to_type_mut E L lt κ T).
End cast.
