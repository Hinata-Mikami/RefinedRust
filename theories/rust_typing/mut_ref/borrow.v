From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def.
From refinedrust Require Import options.

(** ** Borrow rule for mutable references *)

Section rules.
  Context `{!typeGS Σ}.


  (** Typing rule for mutable borrows, manually applied by the tactics *)
  Lemma type_mut_bor E L (T : typed_val_expr_cont_t) e κ_name (ty_annot : option rust_type) :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookup_nofail_goal M κ_name) (λ κ,
      (named_lfts M -∗ typed_borrow_mut E L e κ ty_annot (λ L' π v γ rt ty r,
        T L' π v MetaNone (place_rfn rt * gname)%type (mut_ref κ ty) (#r, γ)))))
    ⊢ typed_val_expr E L (&ref{Mut, ty_annot, κ_name} e)%E T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "HT".
    iDestruct "HT" as "(%M & Hnamed & %κ & _ & HT)". iIntros (Φ) "#(LFT & LLCTX) #HE HL HΦ".
    wp_bind. iSpecialize ("HT" with "Hnamed").
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] [//] [$LFT $LLCTX] HE HL").
    iIntros (l) "Hat HT".
    unfold Ref.
    wp_bind.
    iApply wp_fupd.
    iApply (wp_logical_step with "[HT Hat]"); [solve_ndisj.. | | ].
    { iApply (logical_step_compose with "HT").
      iApply (logical_step_intro_tr with "Hat").
      iIntros "Ha Hcred !> H3".
      iApply ("H3" with "Hcred [Ha]").
      iApply tr_weaken; last done. simpl. unfold num_laters_per_step; lia. }
    (* also need to generate a new cumulative receipt for the created reference *)
    iMod (tr_zero) as "Hc".
    iApply wp_skip.
    iApply (physical_step_intro_tr with "Hc").
    iIntros "!> Hc Hcred1 !> HT" => /=.
    iMod ("HT") as "(%L' & %π & %rt' & %ty & %r & %γ & %ly & Hobs & Hbor & %Hst & %Hly & #Hlb & #Hsc & HL & HT)".
    iModIntro.
    (* generate the credits for the new reference *)
    iApply wp_skip.
    iApply (physical_step_intro_tr with "Hc").
    simpl. unfold num_laters_per_step. simpl.
    iNext. iIntros "Hat Hcred2".
    (* We use [Hcred2] for folding the pinned borrow, and [Hcred1] as a deposit in the reference *)
    iApply ("HΦ" with "HL [Hcred2 Hcred1 Hat Hbor Hobs] HT").
    iExists l, ly. iSplitR; first done. iFrame "# ∗".
    iR. iR. iR.
    iSplitL "Hat". { iApply tr_weaken; last done. lia. }
    iApply (pinned_bor_unfold with "LFT [Hcred2] Hbor"); first done.
    iApply lc_weaken; last done. lia.
  Qed.
End rules.
