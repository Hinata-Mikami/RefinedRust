From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules programs.
From refinedrust.mut_ref Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Place rules for mutable references *)
Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_mut_owned {rto} π κ (lt2 : ltype rto) P E L γ l r wl bmin0
    (T : place_cont_t ((place_rfn rto) * gname)%type) :
    (∀ l', typed_place π E L l' lt2 r (Uniq κ γ ⊓ₖ bmin0) (Uniq κ γ) P
        (λ L' κs l2 b2 bmin rti tyli ri mstrong,
          T L' (κs) l2 b2 bmin rti tyli ri
          (mk_mstrong
          (option_map (λ strong, mk_strong
            (λ rti2, (place_rfn (strong.(strong_rt) rti2)) * gname)%type
            (λ rti2 lti2 ri, MutLtype (strong.(strong_lt) _ lti2 ri) κ)
            (λ rti2 (r : place_rfn rti2), PlaceIn (strong.(strong_rfn) _ r, γ))
            strong.(strong_R)) mstrong.(mstrong_strong))
          (fmap (λ weak,  mk_weak
            (λ ltyi2 ri2, MutLtype (weak.(weak_lt) ltyi2 ri2) κ)
            (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r, γ))
            weak.(weak_R)) mstrong.(mstrong_weak))
          )))
    ⊢ typed_place π E L l (MutLtype lt2 κ) (PlaceIn (r, γ)) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??).
    rewrite /li_tactic /lctx_lft_alive_count_goal.
    iIntros "#(LFT & TIME & LLCTX) #HE HL Hincl0 HP HΦ/=".
    iPoseProof (mut_ltype_acc_owned F with "[$LFT $TIME $LLCTX] HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iApply fupd_wp. iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HR" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L' κs l2 b2 bmin rti tyli ri [strong weak]) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ bmin _ _ _ _ with "Hincl1 Hb").
    simpl. iSplit.
    - (* strong *) iDestruct "Hs" as "[Hs _]".
      destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hb & Hcond & HR)".
      iMod ("Hc" with "Hl Hb") as "(Hb & _)".
      iFrame. iPureIntro. simp_ltypes. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs)".
      iIntros (ltyi2 ri2 bmin').
      iIntros "Hincl2 Hl2 Hcond".
      iMod ("Hs" with "Hincl2 Hl2 Hcond") as "(Hb & Hcond & $ & HR)".
      iMod ("Hc" with "Hl Hb") as "(Hb & Hcond')".
      iPoseProof ("Hcond'" with "Hcond") as "Hcond".
      iModIntro. iFrame "HR Hb".
      iApply typed_place_cond_incl; last iApply "Hcond".
      iApply bor_kind_min_incl_r.
  Qed.
  Definition typed_place_mut_owned_inst := [instance @typed_place_mut_owned].
  Global Existing Instance typed_place_mut_owned_inst | 30.

  Lemma typed_place_mut_uniq {rto} π E L (lt2 : ltype rto) P l r κ γ κ' γ' bmin0 (T : place_cont_t (place_rfn rto * gname)%type) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (Uniq κ γ ⊓ₖ bmin0) (Uniq κ γ) P
        (λ L'' κs' l2 b2 bmin rti tyli ri mstrong,
          T L'' (κs ++ κs') l2 b2 (Uniq κ' γ' ⊓ₖ bmin) rti tyli ri
            (mk_mstrong
            (* strong branch: fold to OpenedLtype *)
            (fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti) * gname)%type)
              (λ rti2 ltyi2 ri2,
                OpenedLtype (MutLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (MutLtype lt2 κ) (MutLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
              (λ rti2 ri2, #((strong.(strong_rfn) _ ri2), γ))
              strong.(strong_R)) mstrong.(mstrong_strong))
            (* weak branch: just keep the MutLtype *)
            (fmap (λ weak, mk_weak (λ lti' ri', MutLtype (weak.(weak_lt) lti' ri') κ) (λ (r : place_rfn rti), #(weak.(weak_rfn) r, γ)) weak.(weak_R)) mstrong.(mstrong_weak))
            ))))
    ⊢ typed_place π E L l (MutLtype lt2 κ) #(r, γ) bmin0 (Uniq κ' γ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (mut_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Hκ' Hclκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred Hcl".
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri [strong weak]) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ (Uniq κ' γ' ⊓ₖ bmin) _ _ _ _ with "[Hincl1] Hb").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit.
    - (* strong update *)
      iDestruct "Hs" as "(Hs & _)". iDestruct "Hcl" as "(_ & Hcl)".
      destruct strong as [ strong | ]; last done.
      iIntros (tyli2 ri2 bmin').
      iIntros "Hl2 %Hst".
      iMod ("Hs" with "Hl2 [//]") as "(Hb & %Hst' & HR)".
      iMod ("Hcl" with "Hl [] Hb") as "Hb".
      { iPureIntro. done. }
      iModIntro. simp_ltypes.
      iFrame. done.
    - (* weak update *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs)". iDestruct "Hcl" as "(Hcl & _)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hl2 Hcond".
      iMod ("Hs" with "[Hincl2] Hl2 Hcond") as "(Hb & Hcond & ? & HR)".
      { iApply bor_kind_incl_trans; first iApply "Hincl2". iApply bor_kind_min_incl_r. }
      simpl.
      iMod ("Hcl" with "Hl Hb [] Hcond") as "(Hb & Hκ' & Hcond)".
      { iApply bor_kind_incl_trans; first iApply bor_kind_min_incl_r. done. }
      iModIntro. iFrame. rewrite llft_elt_toks_app. iFrame.
      iApply typed_place_cond_incl; last done.
      iApply bor_kind_min_incl_r.
  Qed.
  Definition typed_place_mut_uniq_inst := [instance @typed_place_mut_uniq].
  Global Existing Instance typed_place_mut_uniq_inst | 30.

  Lemma typed_place_mut_shared {rto} π E L (lt2 : ltype rto) P l r κ γ κ' bmin0 (T : place_cont_t (place_rfn rto * gname)%type) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r (Shared (κ ⊓ κ') ⊓ₖ bmin0) (Shared (κ ⊓ κ')) P
        (λ L'' κs' l2 b2 bmin rti tyli ri mstrong,
          T L'' (κs ++ κs') l2 b2 (Shared κ' ⊓ₖ bmin) rti tyli ri
            (mk_mstrong
            (* strong branch: fold to ShadowedLtype *)
              None (* TODO *)
            (*(fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti) * gname)%type)*)
              (*(λ rti2 ltyi2 ri2,*)
                (*OpenedLtype (MutLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (MutLtype lt2 κ) (MutLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))*)
              (*(λ rti2 ri2, #((strong.(strong_rfn) _ ri2), γ))*)
              (*strong.(strong_R)) strong)*)
            (* weak branch: just keep the MutLtype *)
            (fmap (λ weak, mk_weak (λ lti' ri', MutLtype (weak.(weak_lt) lti' ri') κ) (λ (r : place_rfn rti), #(weak.(weak_rfn) r, γ)) weak.(weak_R)) mstrong.(mstrong_weak))
            ))))
    ⊢ typed_place π E L l (MutLtype lt2 κ) #(r, γ) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (mut_ltype_acc_shared F with "[$LFT $TIME $LLCTX] Hκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & %q' & Hl & >Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply wp_fupd. iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred". iMod (fupd_mask_mono with "Hb") as "#Hb"; first done.
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri [strong weak]) "#Hincl1 Hb' Hs".
    iApply ("HΦ" $! _ _ _ _ (Shared κ' ⊓ₖ bmin) _ _ _ _ with "[Hincl1] Hb'").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit.
    - (* strong update *)
      done.
    - (* weak update *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hl2 Hcond".
      iMod ("Hs" with "[Hincl2] Hl2 Hcond") as "(Hb' & Hcond & ? & HR)".
      { iApply bor_kind_incl_trans; first iApply "Hincl2". iApply bor_kind_min_incl_r. }
      simpl.
      iMod ("Hcl" with "Hl Hb'") as "(Hb' & Hκ' & Hcond')".
      iFrame. rewrite llft_elt_toks_app.
      iMod (fupd_mask_mono with "(Hclκ' Hκ')") as "?"; first done.
      iFrame. iApply "Hcond'".
      + done.
      + iApply typed_place_cond_incl; last done.
        iApply bor_kind_min_incl_r.
  Qed.
  Definition typed_place_mut_shared_inst := [instance @typed_place_mut_shared].
  Global Existing Instance typed_place_mut_shared_inst | 30.

  (** prove_place_cond instances *)
  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  Lemma prove_place_cond_unfold_mut_l E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (MutLtype (◁ ty) κ) lt T
    ⊢ prove_place_cond E L k (◁ (mut_ref κ ty)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Definition prove_place_cond_unfold_mut_l_inst := [instance @prove_place_cond_unfold_mut_l].
  Global Existing Instance prove_place_cond_unfold_mut_l_inst | 10.
  Lemma prove_place_cond_unfold_mut_r E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (MutLtype (◁ ty) κ) T
    ⊢ prove_place_cond E L k lt (◁ (mut_ref κ ty)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Definition prove_place_cond_unfold_mut_r_inst := [instance @prove_place_cond_unfold_mut_r].
  Global Existing Instance prove_place_cond_unfold_mut_r_inst | 10.

  Lemma prove_place_cond_mut_ltype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 k T :
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ prove_place_cond E L k lt1 lt2 (λ upd, T $ access_result_lift (λ rt, (place_rfn rt * gname)%type) upd)
    ⊢ prove_place_cond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & HT)". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hincl2.
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & Hcond & HT))".
    iExists _. iFrame.
    destruct upd.
    - subst rt2. cbn.
      iApply ltype_eq_place_cond_ty_trans; first last.
      { by iApply mut_ltype_place_cond. }
      iIntros (??). iApply mut_ltype_eq; [ | done..]. iIntros (??). iApply ltype_eq_refl.
    - cbn. done.
  Qed.
  Definition prove_place_cond_mut_ltype_inst := [instance @prove_place_cond_mut_ltype].
  Global Existing Instance prove_place_cond_mut_ltype_inst | 5.
End place.
