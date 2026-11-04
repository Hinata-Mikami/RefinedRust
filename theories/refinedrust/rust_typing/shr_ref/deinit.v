From refinedrust Require Export base type ltypes base.value.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Lemmas about deinitializing *)

Section deinit.
  Context `{!typeGS Σ}.
  Lemma ltype_deinit_shr F π l {rt} (lt : ltype rt) r κ :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] .@ (◁ typed_value_t RefSynType).
  Proof.
    iIntros (?) "Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hlb & %r' & ? & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%Hxr & %l' & (%vi & Hl & %Hdec) & Hb)"; first done.
    iPoseProof (ltype_own_addr_in_usize with "Hb") as "%".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iR.
    iR. iR.
    iSplitL "Hlb"; first by iFrame.
    iExists _. iR.
    iModIntro. iExists vi. iFrame.
    rewrite /ty_own_val/=. iR.
    iExists _.
    by iApply type_ref_value.
  Qed.
End deinit.

Section rule.
  Context `{!typeGS Σ}.

  (* Directly subsume ShrLtype, as there can not be any interesting borrow information to extract *)
  Lemma owned_subltype_step_shrltype_uninit π E L step {rt} (lt : ltype rt) r st κ l T  :
    owned_subltype_step π E L step l r (#()) (ShrLtype lt κ) (◁ typed_value_t st) T :-
    exhale ⌜st = RefSynType⌝;
    return T L True%I.
  Proof.
    iIntros "(-> & HT)".
    iIntros (????) "CTX HE HL Hl". simp_ltypes; simpl.
    iMod (ltype_deinit_shr with "Hl") as "Hl"; [done.. | ].
    iExists _, _. iFrame.
    iModIntro. iApply maybe_logical_step_intro.
    iL.
    iPoseProof (ltype_own_has_layout with "Hl") as "(% & %Hst & %)".
    simp_ltypes in Hst. simpl in Hst.
    done.
  Qed.
  Definition owned_subltype_step_shrltype_uninit_inst := [instance owned_subltype_step_shrltype_uninit].
  Global Existing Instance owned_subltype_step_shrltype_uninit_inst | 20.

  (** Extraction *)
  Lemma stratify_ltype_extract_shrltype π E L {rt} (lt : ltype rt) r κ l (T : stratify_ltype_post_hook_cont_t) :
    (T L (True) _ (◁ typed_value_t RefSynType)%I (#()))
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (ShrLtype lt κ) r (Owned) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    iMod (ltype_deinit_shr with "Hl") as "Hl"; [done.. | ].
    iExists _, _, _, _, _. iFrame.
    iFrame. simp_ltypes.
    done.
  Qed.
  Definition stratify_ltype_extract_shrltype_inst := [instance @stratify_ltype_extract_shrltype].
  Global Existing Instance stratify_ltype_extract_shrltype_inst.
End rule.
