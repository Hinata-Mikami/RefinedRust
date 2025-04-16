From caesium Require Import derived.
From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def subltype unfold.
From iris.prelude Require Import options.

(** ** Place access rules for shared references *)

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_shr_owned {rto} π κ (lt2 : ltype rto) P E L l r wl bmin0 (T : place_cont_t (place_rfn rto)) :
   introduce_with_hooks E L (£1) (λ L1,
     ∀ l', typed_place π E L1 l' lt2 r (Shared κ ⊓ₖ bmin0) (Shared κ) P
        (λ L' κs l2 b2 bmin rti tyli ri mstrong,
          T L' (κs) l2 b2 bmin rti tyli ri
          (mk_mstrong (option_map (λ strong, mk_strong
            (λ rti2, (place_rfn (strong.(strong_rt) rti2)))%type
            (λ rti2 lti2 ri2, ShrLtype (strong.(strong_lt) _ lti2 ri2) κ)
            (λ rti2 (r : place_rfn rti2), #(strong.(strong_rfn) _ r))
            strong.(strong_R)) mstrong.(mstrong_strong))
          (fmap (λ weak,  mk_weak
            (λ lti2 ri2, ShrLtype (weak.(weak_lt) lti2 ri2) κ)
            (λ (r : place_rfn rti), #(weak.(weak_rfn) r))
            weak.(weak_R)) mstrong.(mstrong_weak))
          mstrong.(mstrong_immut)
          )))
    ⊢ typed_place π E L l (ShrLtype lt2 κ) (#r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??).
    iIntros "#(LFT & TIME & LLCTX) #HE HL Hincl0 HP HΦ/=".
    iPoseProof (shr_ltype_acc_owned F with "[$LFT $TIME $LLCTX] HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iApply fupd_wp. iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iMod ("HR" with "[] HE HL Hcred") as "(%L1 & HL & HR)"; first done.
    iApply ("HR" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L' κs l2 b2 bmin rti tyli ri [strong weak immut]) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ bmin _ _ _ _ with "Hincl1 Hb").
    simpl. iSplit; last iSplit.
    - (* strong *) iDestruct "Hs" as "[Hs _]".
      destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hb & Hcond & HR)".
      iMod ("Hc" with "Hl Hb") as "(Hb & _)".
      iFrame. iPureIntro. simp_ltypes. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "(_ & Hs & _)".
      iIntros (ltyi2 ri2 bmin').
      iIntros "Hincl2 Hl2 Hcond".
      iMod ("Hs" with "Hincl2 Hl2 Hcond") as "(Hb & Hcond & $ & HR)".
      iMod ("Hc" with "Hl Hb") as "(Hb & Hcond')".
      iPoseProof ("Hcond'" with "Hcond") as "Hcond".
      iModIntro. iFrame "HR Hb".
      iApply typed_place_cond_incl; last iApply "Hcond".
      + iApply bor_kind_min_incl_r.
      + iPureIntro. apply place_access_rt_rel_refl.
    - (* immut *)
      destruct immut as [immut | ]; last done.
      iDestruct "Hs" as "(_ & _ & Hs)". simpl.
      iIntros "Ha". iMod ("Hs" with "Ha") as "(Ha & $)".
      iMod ("Hc" with "Hl Ha") as "($ & _)".
      done.
  Qed.
  Global Instance typed_place_shr_owned_inst {rto} E L π κ (lt2 : ltype rto) bmin0 r l wl P :
    TypedPlace E L π l (ShrLtype lt2 κ) (#r) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_shr_owned π κ lt2 P E L l r wl bmin0 T).

  Lemma typed_place_shr_uniq {rto} π κ (lt2 : ltype rto) P E L l r κ' γ bmin0 (T : place_cont_t (place_rfn rto)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L1),
      introduce_with_hooks E L1 (£1) (λ L2,
    (∀ l', typed_place π E L2 l' lt2 r (Shared κ) (Shared κ) P
        (λ L3 κs' l2 b2 bmin rti tyli ri mstrong,
          T L3 (κs' ++ κs) l2 b2 bmin rti tyli ri
            (mk_mstrong
            (* strong branch: fold to OpenedLtype *)
            (fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti)))
              (λ rti2 ltyi2 ri2,
                OpenedLtype (ShrLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (ShrLtype lt2 κ) (ShrLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
              (λ rti2 ri2, #((strong.(strong_rfn) _ ri2)))
              strong.(strong_R)) mstrong.(mstrong_strong))
              (* TODO: maybe we should enable weak accesses *)
            (* weak branch: just keep the ShrLtype *)
              (*
            (fmap (λ weak,  mk_weak
            (λ lti2 ri2, ShrLtype (weak.(weak_lt) lti2 ri2) κ)
            (λ (r : place_rfn rti), PlaceIn (weak.(weak_rfn) r))
            weak.(weak_R)) mstrong.(mstrong_weak))
               *)
              None None)
        ))))
    ⊢ typed_place π E L l (ShrLtype lt2 κ) (#r) bmin0 (Uniq κ' γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (shr_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Hκ' Hclκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iMod ("HT" with "[] HE HL Hcred") as "(%L1 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_incl_refl. }
    iModIntro. iIntros (L' κs' l2 b2 bmin rti tyli ri [strong weak]) "#Hincl1 Hb Hs".
    iApply ("HΦ" $! _ _ _ _ bmin _ _ _ _ with "Hincl1 Hb").
    simpl. iSplit; last iSplitL.
    - (* strong *) iDestruct "Hs" as "[Hs _]".
      destruct strong as [ strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hl2 Hcond".
      iMod ("Hs" with "Hl2 Hcond") as "(Hb & %Hcond & HR)".
      iDestruct "Hc" as "[_ Hc]". simpl.
      iMod ("Hc" with "Hl [] Hb") as "Hb".
      { rewrite Hcond. done. }
      iFrame. iPureIntro. simp_ltypes. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hs" as "[_ Hs]".
      done.
      (*
      iIntros (ltyi2 ri2 bmin').
      iIntros "Hincl2 Hl2 Hcond".
      iDestruct "Hc" as "[Hc _]". simpl.
      iMod ("Hs" with "Hincl2 Hl2 Hcond") as "(Hb & Hcond & Htoks & HR)".

      iMod ("Hc" with "Hl Hb []") as "(Hb & Hcond')".
      iPoseProof ("Hcond'" with "Hcond") as "Hcond".
      iModIntro. iFrame "HR Hb".
      iApply typed_place_cond_incl; last iApply "Hcond".
      + iApply bor_kind_min_incl_r.
      + iPureIntro. apply place_access_rt_rel_refl.
       *)
    - (* immut *)
      done.
  Qed.
  Global Instance typed_place_shr_uniq_inst {rto} E L π κ (lt2 : ltype rto) bmin0 r l κ' γ P :
    TypedPlace E L π l (ShrLtype lt2 κ) (#r) bmin0 (Uniq κ' γ) (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_shr_uniq π κ lt2 P E L l r κ' γ bmin0 T).

  Lemma typed_place_shr_shared {rto} π E L (lt2 : ltype rto) P l r κ κ' bmin0 (T : place_cont_t (place_rfn rto)) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      introduce_with_hooks E L' (£1) (λ L1,
      (∀ l', typed_place π E L1 l' lt2 r (Shared κ ⊓ₖ bmin0) (Shared κ) P
        (λ L2 κs' l2 b2 bmin rti tyli ri mstrong,
          T L2 (κs ++ κs') l2 b2 (Shared κ' ⊓ₖ bmin) rti tyli ri
            (mk_mstrong
            (* strong branch: fold to ShadowedLtype *)
              None (* TODO *)
            (*(fmap (λ strong, mk_strong (λ rti, (place_rfn (strong.(strong_rt) rti) * gname)%type)*)
              (*(λ rti2 ltyi2 ri2,*)
                (*OpenedLtype (MutLtype (strong.(strong_lt) _ ltyi2 ri2) κ) (MutLtype lt2 κ) (MutLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))*)
              (*(λ rti2 ri2, #((strong.(strong_rfn) _ ri2), γ))*)
              (*strong.(strong_R)) strong)*)
            (* weak branch: just keep the MutLtype *)
            (fmap (λ weak, mk_weak (λ lti' ri', ShrLtype (weak.(weak_lt) lti' ri') κ) (λ (r : place_rfn rti), #(weak.(weak_rfn) r)) weak.(weak_R)) mstrong.(mstrong_weak))
            None
            )))))
    ⊢ typed_place π E L l (ShrLtype lt2 κ) #r bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL #Hincl0 HP HΦ/=".
    (* get a token *)
    iApply fupd_wp. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (shr_ltype_acc_shared F with "[$LFT $TIME $LLCTX] Hκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & %q' & Hl & >Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply wp_fupd.
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext.
    iIntros (st) "Hl Hcred". iMod (fupd_mask_mono with "Hb") as "#Hb"; first done.
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iMod ("HT" with "[] HE HL Hcred") as "(%L1 & HL &HT)"; first done.
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [] Hb"). { iApply bor_kind_min_incl_l. }
    iModIntro. iIntros (L'' κs' l2 b2 bmin rti tyli ri [strong weak]) "#Hincl1 Hb' Hs".
    iApply ("HΦ" $! _ _ _ _ (Shared κ' ⊓ₖ bmin) _ _ _ _ with "[Hincl1] Hb'").
    { iApply bor_kind_incl_trans; last iApply "Hincl1". iApply bor_kind_min_incl_r. }
    simpl. iSplit; last iSplit.
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
    - (* immut *)
      done.
  Qed.
  Global Instance typed_place_shr_shared_inst {rto} E L π κ κ' (lt2 : ltype rto) bmin0 r l P :
    TypedPlace E L π l (ShrLtype lt2 κ) (#r) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) | 30 := λ T, i2p (typed_place_shr_shared π E L lt2 P l r κ κ' bmin0 T).

  (** prove_place_cond instances *)
  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  Lemma prove_place_cond_unfold_shr_l E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (ShrLtype (◁ ty) κ) lt T
    ⊢ prove_place_cond E L k (◁ (shr_ref κ ty)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply shr_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_shr_l_inst E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k (◁ (shr_ref κ ty))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_shr_l E L ty lt κ k T).
  Lemma prove_place_cond_unfold_shr_r E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (ShrLtype (◁ ty) κ) T
    ⊢ prove_place_cond E L k lt (◁ (shr_ref κ ty)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply shr_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_shr_r_inst E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k lt (◁ (shr_ref κ ty))%I | 10 := λ T, i2p (prove_place_cond_unfold_shr_r E L ty lt κ k T).

  Lemma prove_place_cond_ShrLtype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ k T :
    prove_place_cond E L (Shared κ ⊓ₖ k) lt1 lt2 (λ upd, T $ access_result_lift place_rfn upd)
    ⊢ prove_place_cond E L k (ShrLtype lt1 κ) (ShrLtype lt2 κ) T.
  Proof.
    (* TODO *)
  Abort.

End place.
