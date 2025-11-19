From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules programs.
From refinedrust.mut_ref Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Place rules for mutable references *)
Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_mut_owned {rto} π κ (lt2 : ltype rto) P E L γ l r wl bmin0
    (T : place_cont_t ((place_rfn rto) * gname)%type bmin0) :
    (∀ l', typed_place π E L l' lt2 r bmin0 (Uniq κ γ) P
        (λ L' κs l2 b2 bmin rti tyli ri updcx,
          T L' (κs) l2 b2 bmin rti tyli ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
              (place_rfn upd'.(pupd_rt) * gname)%type
              (MutLtype upd'.(pupd_lt) κ)
              (#(upd'.(pupd_rfn), γ))
              upd'.(pupd_R)
              upd'.(pupd_performed)
              (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_1))
              (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_2)))))
          ))
    ⊢ typed_place π E L l (MutLtype lt2 κ) (#(r, γ)) bmin0 (Owned wl) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??).
    rewrite /li_tactic /lctx_lft_alive_count_goal.
    iIntros "#(LFT & TIME & LLCTX) #HE HL HP HΦ/=".
    iPoseProof (mut_ltype_acc_owned F with "[$LFT $TIME $LLCTX] HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iApply fupd_wp. iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iNext. iIntros (st) "Hl Hcred Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iApply ("HR" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb").
    iModIntro. iIntros (L' κs l2 bmin b2 rti tyli ri updcx) "Hb Hs".
    iApply ("HΦ" $! _ _ _ bmin with "Hb").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl' & %Hsteq' & Hcond & ? & ? & HL & Hcont)".
    iMod ("Hc" with "Hl Hl'") as "Hl".
    iFrame. simpl. iFrame. iR.
    by iApply mut_ltype_place_cond.
  Qed.
  Definition typed_place_mut_owned_inst := [instance @typed_place_mut_owned].
  Global Existing Instance typed_place_mut_owned_inst | 30.

  Lemma typed_place_mut_uniq {rto} π E L (lt2 : ltype rto) P l r κ γ κ' γ' bmin0 (T : place_cont_t (place_rfn rto * gname)%type bmin0) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r bmin0 (Uniq κ γ) P
        (λ L'' κs' l2 b2 bmin rti tyli ri updcx,
          T L'' κs' l2 b2 bmin rti tyli ri
            (λ L4 upd cont, updcx L4 upd (λ upd',
              li_tactic (check_llctx_place_update_kind_incl_goal E L4 upd'.(pupd_performed) (UpdUniq [κ'])) (λ b,
              if b then
                (* keep MutLtype *)
                cont (mkPUpd _ bmin0
                  (place_rfn (upd').(pupd_rt) * gname)%type
                  (MutLtype (upd').(pupd_lt) κ)
                  (# ((upd').(pupd_rfn), γ))
                  ((upd').(pupd_R) ∗ llft_elt_toks κs)
                  (upd').(pupd_performed)
                  (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_1))
                  (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_2)))
              else
                (* fold to OpenedLtype *)
                (* for this, we need to allow strong updates *)
                ⌜bmin0 = UpdStrong⌝ ∗
                cont (mkPUpd _ bmin0
                  (place_rfn (upd').(pupd_rt) * gname)%type
                  (OpenedLtype (MutLtype upd'.(pupd_lt) κ) (MutLtype lt2 κ) (MutLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
                  (# ((upd').(pupd_rfn), γ))
                  (upd').(pupd_R)
                  UpdStrong
                  I
                  (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_2)))
              )))
            )))
    ⊢ typed_place π E L l (MutLtype lt2 κ) #(r, γ) bmin0 (Uniq κ' γ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL HP HΦ/=".
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
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb").
    iModIntro. iIntros (L'' κs' l2 bmin b2 rti tyli ri updcx) "Hb Hs".
    iApply ("HΦ" $! _ _ _ bmin with "Hb").
    simpl. iIntros (upd) "#Hincl Hl2 %Hst ? Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hb & %Hsteq & Hcond & ? & ? & ? & HL & HT)".
    unfold check_llctx_place_update_kind_incl_goal.
    iDestruct "HT" as (b Hb) "HT".
    destruct b; simpl.
    - (* weak *)
      iDestruct "Hcl" as "[Hc _]". simpl.
      iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl2"; first apply Hb.
      iPoseProof (pupd_performed_incl_uniq_rt with "Hincl2") as "%Heq".
      destruct upd' as [rt' ? ? ? ? Heq1 ? ]; simpl in *.
      subst rt'.
      iMod ("Hc" with "Hl Hb [] [] Hcond") as "(Hb & ? & Hcond')".
      { done. }
      { done. }
      iFrame. simpl. iFrame.
      done.
    - (* strong *)
      iDestruct "HT" as "(-> & HT)".
      iDestruct "Hcl" as "[_ Hc]".
      iMod ("Hc" with "Hl [] Hb") as "Hb".
      { rewrite Hsteq. done. }
      iFrame. simpl. iFrame.
      done.
  Qed.
  Definition typed_place_mut_uniq_inst := [instance @typed_place_mut_uniq].
  Global Existing Instance typed_place_mut_uniq_inst | 30.

  Lemma typed_place_mut_shared {rto} π E L (lt2 : ltype rto) P l r κ γ κ' bmin0 (T : place_cont_t (place_rfn rto * gname)%type bmin0) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      (∀ l', typed_place π E L' l' lt2 r bmin0 (Shared (κ ⊓ κ')) P
        (λ L'' κs' l2 b2 bmin rti tyli ri updcx,
          T L'' (κs ++ κs') l2 b2 bmin rti tyli ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
              (place_rfn upd'.(pupd_rt) * gname)%type
              (MutLtype upd'.(pupd_lt) κ)
              (#(upd'.(pupd_rfn), γ))
              upd'.(pupd_R)
              upd'.(pupd_performed)
              (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_1))
              (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd').(pupd_eq_2)))))
            )))
    ⊢ typed_place π E L l (MutLtype lt2 κ) #(r, γ) bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & TIME & LLCTX) #HE HL HP HΦ/=".
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
    iApply ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hb").
    iModIntro. iIntros (L'' κs' l2 bmin b2 rti tyli ri updcx) "Hb' Hs".
    iApply ("HΦ" $! _ _ _ bmin with "Hb'").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl' & %Hsteq2 & Hcond & ? & ? & HL & Hcont)".
    iMod ("Hcl" with "Hl Hl'") as "(Hl & Htok)".
    iMod (fupd_mask_mono with "(Hclκ' Htok)") as "Htoks"; first done.
    iFrame. simpl. iFrame. iR.
    rewrite llft_elt_toks_app. iFrame.
    by iApply mut_ltype_place_cond.
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
    ⌜lctx_lft_incl E L κ1 κ2⌝ ∗ ⌜lctx_lft_incl E L κ2 κ1⌝ ∗ prove_place_cond E L k lt1 lt2 (λ upd, T (mkPUKRes
        upd.(puk_res_k) (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd).(puk_res_eq_1)) (opt_place_update_eq_lift (λ rt, place_rfnRT rt * gname)%type (upd).(puk_res_eq_2))))
    ⊢ prove_place_cond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) T.
  Proof.
    iIntros "(%Hincl1 & %Hincl2 & HT)". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1"; first apply Hincl1.
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hincl2.
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & ? & Hcond & % & HT))".
    iFrame. iL.
    simpl.
    iApply ltype_eq_place_cond_ty_trans; simpl; first last.
    { by iApply mut_ltype_place_cond. }
    iIntros (??). iApply mut_ltype_eq; [ | done..].
    iIntros (??). iApply ltype_eq_refl.
  Qed.
  Definition prove_place_cond_mut_ltype_inst := [instance @prove_place_cond_mut_ltype].
  Global Existing Instance prove_place_cond_mut_ltype_inst | 5.
End place.
