From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** ** Lemmas about [MutLtype] *)

Section subltype.
  Context `{!typeGS Σ}.

  Local Lemma mut_ltype_incl'_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 γ κ1 κ2 :
    ltype_incl (Shared (κ1 ⊓ κ')) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? & (%r' & %γ' & %Hrfn & #Hb))".
    iExists ly. iFrame. iExists _, _. iFrame. iSplitR; first done.
    iModIntro. iMod "Hb" as "(%li & Hs & Hb)". iModIntro.
    iDestruct ("Heq") as "(%Hly_eq & #Hi1 & #Hc1)".
    injection Hrfn as -> ->.
    iExists li. iFrame. iApply ltype_own_shr_mono; last by iApply "Hi1".
    iApply lft_intersect_mono; first done.
    iApply lft_incl_refl.
  Qed.
  Lemma mut_ltype_incl_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' γ r1 r2 κ1 κ2 :
    ltype_incl (Shared (κ1 ⊓ κ')) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_shared_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma mut_ltype_incl'_shared {rt} (lt1 lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1 ⊓ κ')) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? & (%r' & %γ & Hrfn & #Hb))".
    iExists ly. iFrame.
    iModIntro. iMod "Hb" as "(%li & Hs & Hb)". iModIntro.
    iDestruct ("Heq" $! r') as "(%Hly_eq & #Hi1 & #Hc1)".
    iExists li. iFrame. iApply ltype_own_shr_mono; last by iApply "Hi1".
    iApply lft_intersect_mono; first done.
    iApply lft_incl_refl.
  Qed.

  Lemma mut_ltype_incl_shared {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1 ⊓ κ')) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_shared; [ | done  ]).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  Local Lemma mut_ltype_incl'_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 γ :
    ltype_incl (Uniq κ1 γ) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? &  ? & (%γ' & %r' & %Hrfn & Hl))".
    injection Hrfn as <- <-.
    iModIntro.
    iExists ly. iFrame. iExists γ, r2. iSplitR; first done.
    iNext. iMod "Hl" as "(%l' & Hl & Hb)".
    iExists l'. iFrame. iDestruct "Heq" as "(_ & Heq & _)".
    iApply ltype_own_uniq_mono; last by iApply "Heq". done.
  Qed.
  Lemma mut_ltype_incl_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 γ :
    ltype_incl (Uniq κ1 γ) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) #(r1, γ) #(r2, γ) (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_owned_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma mut_ltype_incl'_owned {rt} (lt1 lt2 : ltype rt) κ1 κ2 wl r :
    (∀ γ r, ltype_incl (Uniq κ1 γ) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? &  ? & (%γ' & %r' & Hrfn & Hl))".
    iModIntro.
    iExists ly. iFrame.
    iNext. iMod "Hl" as "(%l' & Hl & Hb)".
    iExists l'. iFrame. iModIntro.
    iApply ltype_own_uniq_mono; first done.
    iDestruct ("Heq" $! _ _) as "(_ & #Heq' & _)". by iApply "Heq'".
  Qed.
  Lemma mut_ltype_incl_owned {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ1 κ2 wl r :
    (∀ γ r, ltype_incl (Uniq κ1 γ) r r lt1 lt2)  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type (Uniq _ inhabitant) inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_owned; [ | done  ]).
    - done.
    - iIntros (??). iApply ltype_incl_core. done.
  Qed.

  (* Refinement subtyping under mutable references is restricted: we need to make sure that, no matter the future updates,
     we can always get back to what the lender expects. Thus we loose all refinement information when descending below mutable references. *)
  Local Lemma mut_ltype_incl'_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ γ r, ltype_eq (Uniq (κ1) γ) r r lt1 lt2) -∗
    (* Note: requires mutual inclusion, because we may be below a mutable reference *)
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl' (Uniq κ γ) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2". iModIntro.
    iIntros (π l). rewrite !ltype_own_mut_ref_unfold /mut_ltype_own /=.
    iIntros "(%ly & ? & ? & ? & ? & ? & Hb)".
    iExists ly. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        iApply ltype_own_uniq_mono; last by iApply "Hi1". done.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        iApply "Hi2". iApply ltype_own_uniq_mono; done.
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        rewrite !ltype_own_core_equiv.
        iApply ltype_own_uniq_mono; last by iApply "Hc1". done.
      * iIntros "(%r' & Hauth & Hb)"; iExists _; iFrame.
        iMod "Hb" as "(%l' & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! _ r'.1) as "((%Hly_eq & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2))".
        rewrite !ltype_own_core_equiv.
        iApply "Hc2". iApply ltype_own_uniq_mono; done.
  Qed.
  Lemma mut_ltype_incl_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ γ r, ltype_eq (Uniq (κ1) γ) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl (Uniq κ γ) r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iPoseProof (ltype_eq_syn_type (Uniq _ inhabitant) inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply mut_ltype_incl'_uniq; [ | done  | done]).
    - done.
    - iIntros (??). iApply ltype_eq_core. done.
  Qed.

  Lemma mut_ltype_incl {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl b r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    destruct b.
    - iApply mut_ltype_incl_owned; last done. iIntros (??). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply mut_ltype_incl_shared; last done. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply mut_ltype_incl_uniq; [ | done..]. iIntros (??). done.
  Qed.

  Lemma mut_ltype_eq {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_eq b r r (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iSplit.
    - iApply mut_ltype_incl; done.
    - iApply mut_ltype_incl; [ | done..]. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  Lemma mut_full_subltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_subltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    intros Heq Hincl1 Hincl2.
    iIntros (qL) "HL #CTX #HE". iIntros (b r).
    iPoseProof (Heq with "HL CTX HE") as "#Heq".
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl2"; first apply Hincl2.
    iApply mut_ltype_incl; done.
  Qed.
  Lemma mut_full_eqltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_eqltype E L (MutLtype lt1 κ1) (MutLtype lt2 κ2).
  Proof.
    intros Heq Hincl1 Hincl2.
    apply full_subltype_eqltype; eapply mut_full_subltype; naive_solver.
  Qed.
End subltype.


Section access.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Lemma mut_ltype_place_cond b κ {rt rt2} (lt1 : ltype rt) (lt2 : ltype rt2) :
    typed_place_cond (b) lt1 lt2
    ⊢ typed_place_cond b (MutLtype lt1 κ) (MutLtype lt2 κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "->". simp_ltypes. done.
    - iIntros "(%Hrefl & Heq & Hub)".
      subst rt2. cbn.
      iExists eq_refl. cbn. iSplitR "Hub".
      + simp_ltypes. iIntros (??). iApply (mut_ltype_eq with "Heq"); iApply lft_incl_refl.
      + by iApply mut_ltype_imp_unblockable.
  Qed.

  Lemma mut_ltype_acc_owned {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' γ' wl :
    lftE ⊆ F →
    rrust_ctx -∗
    l ◁ₗ[π, Owned wl] #(r, γ') @ MutLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ l' ◁ₗ[π, Uniq κ' γ'] r @ lt ∗
      logical_step F
      (∀ rt' (lt2 : ltype rt') r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Uniq κ' γ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Owned wl] #(r2, γ') @ MutLtype lt2 κ').
  Proof.
    iIntros (?) "#[LFT TIME] HP".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & Hcred & %γ & %r' & %Heq & Hb)".
    apply syn_type_has_layout_ptr_inv in Halg as ?. subst.
    injection Heq as <- <-.
    iFrame "Hlb %".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%l' & Hl & Hb)".
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>". iIntros (rt2 lt2 r2) "Hl Hb".
    iModIntro.
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own. iExists void*.
    iSplitR; first done. by iFrame "Hlb % ∗".
  Qed.

  Lemma mut_ltype_acc_uniq {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' γ' κ γ q R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #(r, γ') @ MutLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ (l' ◁ₗ[π, Uniq κ' γ'] r @ lt) ∗
      logical_step F
      ( (* weak update *)
       (∀ bmin (lt2 : ltype rt) r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Uniq κ' γ'] r2 @ lt2  -∗
        bmin ⪯ₚ UpdUniq [κ] -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        typed_place_cond bmin lt lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #(r2, γ') @ MutLtype lt2 κ' ∗
        R ∗
        typed_place_cond bmin (MutLtype lt κ') (MutLtype lt2 κ')) ∧
      (* strong update, go to Opened *)
      (∀ rt2 (lt2 : ltype rt2) r2,
        l ↦ l' -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        l' ◁ₗ[π, Uniq κ' γ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn (r2, γ') @ OpenedLtype (MutLtype lt2 κ') (MutLtype lt κ') (MutLtype lt κ')
          (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#[LFT TIME] Hκ HR HP".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    apply syn_type_has_layout_ptr_inv in Halg as ?. subst.
    iFrame "Hlb". iSplitR; first done.

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    (* NOTE: we are currently throwing away the existing "coring"-viewshift that we get *)
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ'' & #Hincl & Hb & _ & Hb_cl)"; first done.
    iMod "Hcl_F" as "_".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' &  Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "(%l' & Hl & Hb)"; first done.
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat".
    iModIntro.
    iSplit.
    - (* close *)
      iIntros (bmin lt2 r2) "Hl Hb #Hincl_k %Hst_eq #Hcond".
      (* extract the necessary info from the place_cond *)
      iPoseProof (typed_place_cond_incl _ (UpdUniq [κ]) with "Hincl_k Hcond") as "Hcond'".
      iDestruct "Hcond'" as "(%Heq & Heq & (#Hub & _))".
      rewrite (UIP_refl _ _ Heq). cbn.
      (* close the borrow *)
      iMod (gvar_update (r2, γ') with "Hauth Hrfn") as "(Hauth & Hrfn)".
      set (V := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ∃ (l' : loc), l ↦ l' ∗ ltype_own lt2 (Uniq κ' r'.2) π r'.1 l'))%I).
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hl Hb]") as "(Hb & Htok)".
      { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
        iModIntro. iNext. iExists r'. iFrame "Hauth".
        clear. iMod "Hb" as "(%l' & ? & Ha)".
        iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
        (* unblock *)
        iMod ("Hub" with "[$Hdead //] Ha") as "Ha".
        (* use that the cores are equal *)
        iDestruct ("Heq" $! (Uniq _ _) _) as "(_ & (%Hst & #Hi & _))".
        rewrite ltype_own_core_equiv. iPoseProof ("Hi" with "Ha") as "Ha".
        rewrite -ltype_own_core_equiv. eauto with iFrame. }
      { iModIntro. rewrite /V. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        iExists void*. iFrame. do 3 iR.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        iModIntro. subst V.
        (* need to adapt the pinned part, too *)
        iApply (pinned_bor_iff with "[] [] Hb").
        { iNext. iModIntro. eauto. }
        clear -Hst_eq.
        iNext. iModIntro. iSplit.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & Hl & Hb)".
          iDestruct ("Heq" $! (Uniq _ _) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iPoseProof ("Heq1" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          eauto with iFrame.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & Hl & Hb)".
          iDestruct ("Heq" $! (Uniq _ _) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iPoseProof ("Heq2" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          eauto with iFrame.
      }
      iApply mut_ltype_place_cond; done.
    - (* shift to OpenedLtype *)
      iIntros (rt2 lt2 r2) "Hl %Hst' Hb". iModIntro.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(% & _ & _ & _ & _ & %r' & % & -> & >(%l0 & Hl & Hb))".
        iModIntro. setoid_rewrite ltype_own_core_equiv.
        iExists _. eauto with iFrame. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        setoid_rewrite ltype_own_core_equiv. rewrite ltype_core_idemp.
        iModIntro. eauto 8 with iFrame. }
      { rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
        iExists void*. do 4 iR.
        iExists _, r2. iR. iNext. iModIntro. eauto with iFrame. }
  Qed.

  Lemma mut_ltype_acc_shared {rt} F π (lt : ltype rt) r l q κ κ' γ :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    l ◁ₗ[π, Shared κ] #(r, γ) @ MutLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc) q', l ↦{q'} l' ∗ (|={F}▷=> l' ◁ₗ[π, Shared (κ' ⊓ κ)] r @ lt) ∗
    (∀ rt' (lt' : ltype rt') r',
      l ↦{q'} l' -∗
      l' ◁ₗ[π, Shared (κ' ⊓ κ)] r' @ lt' -∗ |={F}=>
      l ◁ₗ[π, Shared κ] #(r', γ) @ MutLtype lt' κ' ∗
      q.[κ]).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ Hb". rewrite {1}ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & %Hly & #Hlb & %r' & %γ' & %Ha & #Hb)".
    injection Ha as <- <-.
    apply syn_type_has_layout_ptr_inv in Hst as ?. subst ly.
    iR. iR.
    iMod (fupd_mask_mono with "Hb") as "(%li & #Hf & #Hl)"; first done.
    iMod (frac_bor_acc with "LFT Hf Hκ") as "(%q' & >Hpts & Hclf)"; first done.
    iModIntro. iExists _, _. iFrame.
    iSplitR. { iApply step_fupd_intro; first done. auto. }
    iIntros (rt' lt' r'') "Hpts #Hl'".
    iMod ("Hclf" with "Hpts") as "Htok".
    iFrame.
    iModIntro.
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iExists void*. iFrame "% #". by iExists _.
  Qed.

End access.
