From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Borrow rule for shared references *)

Section rule.
  Context `{!typeGS Σ}.

  (** Typing rule for shared borrowing, manually applied by the tactics *)
  Lemma type_shr_bor E L f (T : typed_val_expr_cont_t) e κ_name ty_annot :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookup_nofail_goal M κ_name) (λ κ,
    (named_lfts M -∗ typed_borrow_shr E L f e κ ty_annot (λ L' v rt ty r,
      T L' v MetaNone (place_rfn rt) (shr_ref κ ty) (r)))))
    ⊢ typed_val_expr E L f (&ref{Shr, ty_annot, κ_name} e)%E T.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ & _ & HT)". iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    wpe_bind. iSpecialize ("HT" with "Hnamed").
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] [//] [$LFT $LLCTX] HE HL Hf").
    iIntros (l) "HT".
    unfold Ref. wpe_bind. iApply wpe_fupd.
    iApply (wpe_logical_step with "HT"); [solve_ndisj.. | ].
    iApply wp_skip. iApply physical_step_intro; iNext. iIntros "HT !>".
    iApply wpe_fupd.
    iApply (wpe_logical_step with "HT"); [solve_ndisj.. | ].
    iApply wp_skip.
    iApply physical_step_intro_lc. iIntros "(Hcred & Hcred1) !> !> HT".
    iMod ("HT" with "Hcred1") as (L' rt ty r r' ly) "(#Hrfn & #Hshr & %Halg & %Hly & #Hlb & #Hsc & HL & Hf & HT)".
    iModIntro. iApply ("HΦ" with "HL Hf [Hshr] HT").
    iExists l, ly, r'. iR. iR. iFrame "Hlb Hrfn Hsc %".
    iModIntro. iModIntro. done.
  Qed.
End rule.
