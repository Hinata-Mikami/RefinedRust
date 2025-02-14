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
        T L' π v (place_rfn rt * gname)%type (mut_ref κ ty) (#r, γ)))))
    ⊢ typed_val_expr E L (&ref{Mut, ty_annot, κ_name} e)%E T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "HT".
    iDestruct "HT" as "(%M & Hnamed & %κ & _ & HT)". iIntros (Φ) "#(LFT & TIME & LLCTX) #HE HL HΦ".
    wp_bind. iSpecialize ("HT" with "Hnamed").
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] [//] [$LFT $TIME $LLCTX] HE HL").
    iIntros (l) "Hat HT".
    unfold Ref.
    wp_bind.
    iApply (wp_logical_step with "TIME [HT Hat]"); [solve_ndisj.. | | ].
    { iApply (logical_step_compose with "HT").
      iApply (logical_step_intro_atime with "Hat").
      iIntros "H1 H2 !> H3". iApply ("H3" with "H1 H2"). }
    (* also need to generate a new cumulative receipt for the created reference *)
    iMod (additive_time_receipt_0) as "Hc".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wp_skip_credits with "TIME Hc Hp"); first done.
    iIntros "!> Hcred1 Hc HT" => /=.
    iMod ("HT") as "(%L' & %π & %rt' & %ty & %r & %γ & %ly & Hobs & Hbor & %Hst & %Hly & #Hlb & #Hsc & HL & HT)".
    iModIntro.
    (* generate the credits for the new reference *)
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wp_skip_credits with "TIME Hc Hp"); first done.
    rewrite (additive_time_receipt_sep 1). iNext. iIntros "[Hcred2 Hcred] [Hat1 Hat]".
    (* We use [Hcred1] for folding the pinned borrow, and [Hcred] as a deposit in the reference *)
    iApply ("HΦ" with "HL [Hcred Hcred1 Hat Hat1 Hbor Hobs] HT").
    iExists l, ly. iSplitR; first done. iFrame "# ∗".
    iSplitR; first done. iSplitR; first done.
    by iApply (pinned_bor_unfold with "LFT Hcred1 Hbor").
  Qed.


End rules.
