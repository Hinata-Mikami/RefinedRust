From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** ** Lemmas about [ShrLtype] *)

Section subltype.
  Context `{!typeGS Σ}.

  (** Shared references *)
  Local Lemma shr_ltype_incl'_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 κ1 κ2 :
    ltype_incl (Shared (κ1)) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq. iFrame.
    iDestruct "Hrfn" as "->".
    iExists r2. iSplitR; first done. iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hs & Hb)". iModIntro. iExists li. iFrame. iNext.
    iDestruct "Heq" as "(_ & Hi1 & _)".
    iApply ltype_own_shr_mono; last by iApply "Hi1". done.
  Qed.
  Lemma shr_ltype_incl_shared_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ' r1 r2 κ1 κ2 :
    ltype_incl (Shared (κ1)) r1 r2 lt1 lt2 -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_shared_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma shr_ltype_incl'_shared {rt} (lt1 lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1)) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Shared κ') r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & %ri & Hrfn & #Hb)".
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq. iFrame.
    iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%li & Hs & Hb)". iModIntro. iExists li. iFrame. iNext.
    iDestruct ("Heq" $! _) as "(_ & Hi1 & _)".
    iApply ltype_own_shr_mono; last by iApply "Hi1". done.
  Qed.
  Lemma shr_ltype_incl_shared {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ' r κ1 κ2 :
    (∀ r, ltype_incl (Shared (κ1)) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Shared κ') r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_shared; [ | done  ]).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  Local Lemma shr_ltype_incl'_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 :
    ltype_incl (Shared κ1) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq.
    iFrame. iDestruct "Hrfn" as "->". iExists r2. iSplitR; first done. iNext.
    iMod "Hb" as "(%li & Hli & Hb)". iExists li. iFrame "Hli".
    iDestruct "Heq" as "(_ & Heq & _)".
    iApply ltype_own_shr_mono; last by iApply "Heq". done.
  Qed.
  Lemma shr_ltype_incl_owned_in {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 wl r1 r2 :
    ltype_incl (Shared κ1) r1 r2 lt1 lt2  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) #(r1) #(r2) (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_owned_in; [ | done  ]).
    - done.
    - iApply ltype_incl_core. done.
  Qed.

  Local Lemma shr_ltype_incl'_owned {rt} (lt1 lt2 : ltype rt) κ1 κ2 wl r :
    (∀ r, ltype_incl (Shared κ1) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    ltype_incl' (Owned wl) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1". iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? & %ri & Hrfn & Hb)".
    iModIntro.
    iExists ly. iFrame. rewrite -?Hd -?Hly_eq.
    iFrame. iNext.
    iMod "Hb" as "(%li & Hli & Hb)". iExists li. iFrame "Hli".
    iDestruct ("Heq" $! _) as "(_ & Heq' & _)".
    iApply ltype_own_shr_mono; last by iApply "Heq'". done.
  Qed.
  Lemma shr_ltype_incl_owned {rt} (lt1 : ltype rt) (lt2 : ltype rt) κ1 κ2 wl r :
    (∀ r, ltype_incl (Shared κ1) r r lt1 lt2)  -∗
    κ2 ⊑ κ1 -∗
    ltype_incl (Owned wl) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1".
    iPoseProof (ltype_incl_syn_type (Shared _) inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_owned; [ | done  ]).
    - done.
    - iIntros (?). iApply ltype_incl_core. done.
  Qed.

  (* Refinement subtyping under mutable references is restricted: we need to make sure that, no matter the future updates,
     we can always get back to what the lender expects. Thus we loose all refinement information when descending below mutable references. *)
  Local Lemma shr_ltype_incl'_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ r, ltype_eq (Shared (κ1)) r r lt1 lt2) -∗
    (* Note: requires mutual inclusion, because we may be below a mutable reference *)
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl' (Uniq κ γ) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2". iModIntro.
    iIntros (π l). rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
    iIntros "(%ly & ? & ? & Hlb & ? &  Hrfn & Hb)".
    iExists ly. iFrame. rewrite -?Hly_eq. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro. iSplit.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "((_ & Hi & _) & _)".
        iApply ltype_own_shr_mono; last by iApply "Hi". done.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "(_ & (_ & Hi & _))".
        iApply "Hi"; last by iApply ltype_own_shr_mono.
    + (* the same proof *)
      iNext. iModIntro. iSplit.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "((_ & _ & Hi) & _)".
        rewrite !ltype_own_core_equiv.
        iApply ltype_own_shr_mono; last by iApply "Hi". done.
      * iIntros "(%ri & Hauth & Hb)". iExists ri. iFrame.
        iMod "Hb" as "(%li & Hl & Hb)". iModIntro. iExists _. iFrame.
        iDestruct ("Heq" $! ri) as "(_ & (_ & _ & Hi))".
        rewrite !ltype_own_core_equiv.
        iApply "Hi"; last by iApply ltype_own_shr_mono.
  Qed.
  Lemma shr_ltype_incl_uniq {rt} (lt1 lt2 : ltype rt) κ1 κ2 κ r γ :
    (∀ r, ltype_eq (Shared (κ1)) r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl (Uniq κ γ) r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iPoseProof (ltype_eq_syn_type _ inhabitant with "Heq") as "%Hst".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply shr_ltype_incl'_uniq; [ | done  | done]).
    - done.
    - iIntros (?). iApply ltype_eq_core. done.
  Qed.

  Lemma shr_ltype_incl {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_incl b r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    destruct b.
    - iApply shr_ltype_incl_owned; last done. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply shr_ltype_incl_shared; last done. iIntros (?). iDestruct ("Heq" $! _ _) as "[$ _]".
    - iApply shr_ltype_incl_uniq; [ | done..]. iIntros (?). done.
  Qed.
  Lemma shr_ltype_eq {rt} (lt1 lt2 : ltype rt) b r κ1 κ2 :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    κ2 ⊑ κ1 -∗
    κ1 ⊑ κ2 -∗
    ltype_eq b r r (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    iIntros "#Heq #Hincl1 #Hincl2".
    iSplit.
    - iApply shr_ltype_incl; done.
    - iApply shr_ltype_incl; [ | done..]. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  Lemma shr_full_subltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_subltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    intros Hsub Hincl1 Hincl2.
    iIntros (qL) "HL #CTX #HE". iIntros (??).
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl_noend with "HL HE") as "#Hincl2"; first apply Hincl2.
    iPoseProof (Hsub  with "HL CTX HE") as "Hsub".
    iApply (shr_ltype_incl with "Hsub Hincl2 Hincl1").
  Qed.
  Lemma shr_full_eqltype E L {rt} (lt1 lt2 : ltype rt) κ1 κ2 :
    full_eqltype E L lt1 lt2 →
    lctx_lft_incl E L κ1 κ2 →
    lctx_lft_incl E L κ2 κ1 →
    full_eqltype E L (ShrLtype lt1 κ1) (ShrLtype lt2 κ2).
  Proof.
    intros Hsub Hincl1 Hincl2.
    apply full_subltype_eqltype; eapply shr_full_subltype; naive_solver.
  Qed.
End subltype.

Section acc.
  Context `{!typeGS Σ}.

  Lemma shr_ltype_place_cond b κ {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    typed_place_cond b lt1 lt2 -∗
    typed_place_cond b (ShrLtype lt1 κ) (ShrLtype lt2 κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "->". done.
    - iIntros "(%Hrefl & Heq & Hub)".
      subst rt2. cbn.
      iExists eq_refl. cbn. iSplitR "Hub".
      + simp_ltypes. iIntros (??). iApply (shr_ltype_eq with "Heq"); iApply lft_incl_refl.
      + by iApply shr_ltype_imp_unblockable.
  Qed.

  Lemma shr_ltype_acc_owned {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' wl :
    lftE ⊆ F →
    rrust_ctx -∗
    l ◁ₗ[π, Owned wl] PlaceIn (r) @ ShrLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc), l ↦ l' ∗ l' ◁ₗ[π, Shared κ'] r @ lt ∗
      logical_step F
      (∀ rt' (lt2 : ltype rt') r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Shared κ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Owned wl] #r2 @ ShrLtype lt2 κ').
  Proof.
    iIntros (?) "#[LFT TIME] HP".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & Hcred & %r' & %Heq & Hb)".
    apply syn_type_has_layout_ptr_inv in Halg as ?. subst.
    iFrame "Hlb %".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%l' & Hl & Hb)".
    iModIntro. iExists l'. iFrame.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>". iIntros (rt2 lt2 r2) "Hl Hb".
    iModIntro.
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own. iExists void*.
    iSplitR; first done. iFrame "Hlb % ∗".
    iSplitR; first done. iNext. eauto with iFrame.
  Qed.


  (* Note: this doesn't allow changing the type below the shared reference *)
  Lemma shr_ltype_acc_uniq {rt} F π (lt : ltype rt) (r : place_rfn rt) l κ' κ γ q R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #r @ ShrLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ l' : loc, l ↦ l' ∗ (l' ◁ₗ[π, Shared κ'] r @ lt) ∗
      logical_step F
      ( (* weak update *)
       (∀ (bmin : place_update_kind) (lt2 : ltype rt) r2,
        l ↦ l' -∗
        l' ◁ₗ[π, Shared κ'] r2 @ lt2 -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        bmin ⪯ₚ UpdUniq [κ] -∗
        typed_place_cond bmin lt lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r2 @ ShrLtype lt2 κ' ∗
        R ∗
        typed_place_cond bmin (ShrLtype lt κ') (ShrLtype lt2 κ')) ∧
      (* strong update, go to Opened *)
      (∀ rt2 (lt2 : ltype rt2) r2,
        l ↦ l' -∗
        ⌜ltype_st lt2 = ltype_st lt⌝ -∗
        l' ◁ₗ[π, Shared κ'] r2 @ lt2 ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r2 @ OpenedLtype (ShrLtype lt2 κ') (ShrLtype lt κ') (ShrLtype lt κ')
          (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#[LFT TIME] Hκ HR HP".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "HP" as "(%ly & %Halg & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    apply syn_type_has_layout_ptr_inv in Halg as ?. subst.
    iFrame "Hlb". iSplitR; first done.

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ'' & #Hincl & Hb & Hx & Hb_cl)"; first done.
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
      iIntros (bmin lt2 r2) "Hl Hb %Hst_eq #Hincl_k #Hcond".
      (* extract the necessary info from the place_cond *)
      iPoseProof (typed_place_cond_incl with "Hincl_k Hcond") as "Hcond'".
      iDestruct "Hcond'" as "(%Heq & Heq & _)".
      rewrite (UIP_refl _ _ Heq). cbn.
      (* close the borrow *)
      iMod (gvar_update r2 with "Hauth Hrfn") as "(Hauth & Hrfn)".
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      (* Throw away the existing coring viewshift [Hx] *)
      set (V := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ∃ (l' : loc), l ↦ l' ∗ ltype_own lt2 (Shared κ') π r' l'))%I).
      iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hl Hb]") as "(Hb & Htok)".
      { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
        iModIntro. iNext. iExists r'. iFrame "Hauth".
        clear. iMod "Hb" as "(%l' & ? & Ha)".
        (* go to core *)
        iPoseProof (ltype_own_shared_to_core with "Ha") as "Ha".
        (* use that the cores are equal *)
        iDestruct ("Heq" $! (Shared _) _) as "(_ & (%Hst & #Hi & _))".
        setoid_rewrite ltype_own_core_equiv. iPoseProof ("Hi" with "Ha") as "Ha".
        eauto with iFrame. }
      { iModIntro. rewrite /V. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        iExists void*. iFrame. do 3 iR.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        (* need to adapt the pinned part, too *)
        iApply (pinned_bor_iff with "[] [] Hb").
        { iNext. iModIntro. eauto. }
        clear -Hst_eq.
        iNext. iModIntro. iSplit.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & Hl & Hb)".
          iDestruct ("Heq" $! (Shared _) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iPoseProof ("Heq1" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          eauto with iFrame.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame.
          iMod "Hb" as "(%l' & Hl & Hb)".
          iDestruct ("Heq" $! (Shared _) _) as "((_ & #Heq1 & _) & (_ & #Heq2 & _))".
          rewrite ltype_own_core_equiv. iPoseProof ("Heq2" with "Hb") as "Hb". rewrite -ltype_own_core_equiv.
          eauto with iFrame.
      }
      iApply shr_ltype_place_cond; done.
    - (* shift to OpenedLtype *)
      iIntros (rt2 lt2 r2) "Hl %Hst' Hb". iModIntro.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(% & _ & _ & _ & _ & %r' & -> & >(%l0 & Hl & Hb))".
        iModIntro. setoid_rewrite ltype_own_core_equiv.
        iExists _. eauto with iFrame. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        setoid_rewrite ltype_own_core_equiv. rewrite ltype_core_idemp.
        iModIntro. eauto 8 with iFrame. }
      { rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
        iExists void*. do 4 iR.
        iExists r2. iR. iNext. iModIntro. eauto with iFrame. }
  Qed.

  Lemma shr_ltype_acc_shared {rt} F π (lt : ltype rt) r l q κ κ' :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    l ◁ₗ[π, Shared κ] #r @ ShrLtype lt κ' -∗
    ⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l 0 (ly_size void*) ∗ |={F}=>
      ∃ (l' : loc) q', l ↦{q'} l' ∗ (|={F}▷=> l' ◁ₗ[π, Shared κ'] r @ lt) ∗
    (∀ rt' (lt' : ltype rt') r',
      l ↦{q'} l' -∗
      l' ◁ₗ[π, Shared κ'] r' @ lt' -∗ |={F}=>
      l ◁ₗ[π, Shared κ] #r' @ ShrLtype lt' κ' ∗
      q.[κ]).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ Hb". rewrite {1}ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & %Hly & #Hlb & %r' & -> & #Hb)".
    apply syn_type_has_layout_ptr_inv in Hst as ?. subst ly.
    iR. iR.
    iMod (fupd_mask_mono with "Hb") as "(%li & #Hf & #Hl)"; first done.
    iMod (frac_bor_acc with "LFT Hf Hκ") as "(%q' & >Hpts & Hclf)"; first done.
    iModIntro. iExists _, _. iFrame.
    iSplitR. { iApply step_fupd_intro; first done. auto. }
    iIntros (rt' lt' r'') "Hpts #Hl'".
    iMod ("Hclf" with "Hpts") as "Htok".
    iFrame.
    iModIntro. rewrite ltype_own_shr_ref_unfold /shr_ltype_own. iExists void*. by iFrame "% #".
  Qed.
End acc.
