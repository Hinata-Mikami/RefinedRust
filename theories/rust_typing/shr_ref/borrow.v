From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Borrow rule for shared references *)

Section rule.
  Context `{!typeGS Σ}.

  (** Typing rule for shared borrowing, manually applied by the tactics *)
  Lemma type_shr_bor E L (T : typed_val_expr_cont_t) e κ_name ty_annot :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookup_nofail_goal M κ_name) (λ κ,
    (named_lfts M -∗ typed_borrow_shr E L e κ ty_annot (λ L' π v rt ty r,
      T L' π v MetaNone (place_rfn rt) (shr_ref κ ty) (r)))))
    ⊢ typed_val_expr E L (&ref{Shr, ty_annot, κ_name} e)%E T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ & _ & HT)". iIntros (Φ) "#(LFT & LLCTX) #HE HL HΦ".
    wp_bind. iSpecialize ("HT" with "Hnamed").
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] [//] [$LFT $LLCTX] HE HL").
    iIntros (l) "HT".
    unfold Ref. wp_bind. iApply ewp_fupd.
    iApply (wp_logical_step with "HT"); [solve_ndisj.. | ].
    iApply wp_skip. iApply physical_step_intro; iNext. iIntros "HT !>".
    iApply wp_fupd.
    iApply (wp_logical_step with "HT"); [solve_ndisj.. | ].
    iApply wp_skip.
    iApply physical_step_intro_lc. iIntros "(Hcred & Hcred1) !> !> HT".
    iMod ("HT" with "Hcred1") as (L' π rt ty r r' ly) "(#Hrfn & #Hshr & %Halg & %Hly & #Hlb & #Hsc & HL & HT)".
    iModIntro. iApply ("HΦ" with "HL [Hshr] HT").
    iExists l, ly, r'. iR. iR. iFrame "Hlb Hrfn Hsc %".
    iModIntro. iModIntro. done.
  Qed.
End rule.
