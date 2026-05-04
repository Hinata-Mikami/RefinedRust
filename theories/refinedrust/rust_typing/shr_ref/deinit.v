From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Lemmas about deinitializing *)

Section deinit.
  Context `{!typeGS Σ}.

  Lemma ltype_deinit_shr F π l st {rt} (lt : ltype rt) r κ :
    lftE ⊆ F →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hlb & %r' & ? & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR.
    iSplitL "Hlb"; first by iFrame.
    iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iR. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  Lemma ltype_deinit_shr' F π l st {rt} (lt : ltype rt) r κ :
    lftE ⊆ F →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hlb & %r' & ? & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR.
    iSplitL "Hlb"; first by iFrame.
    iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iR. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.
End deinit.

Section rule.
  Context `{!typeGS Σ}.

  (* Directly subsume ShrLtype, as there can not be any interesting borrow information to extract *)
  Lemma owned_subltype_step_shrltype_uninit π E L {rt} (lt : ltype rt) r st κ l T  :
    owned_subltype_step π E L l r #() (ShrLtype lt κ) (◁ uninit st) T :-
    exhale (⌜syn_type_compat PtrSynType st⌝);
    return T L True%I.
  Proof.
    iIntros "(%Hstcomp & HT)".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.
    iMod (ltype_deinit_shr with "Hl") as "Hl"; [done.. | ].
    iExists _, _. iFrame.
    iSplitL. { iApply logical_step_intro. by iFrame. }
    iModIntro. iPureIntro.
    by apply syn_type_compat_size_eq.
  Qed.
  Definition owned_subltype_step_shrltype_uninit_inst := [instance owned_subltype_step_shrltype_uninit].
  Global Existing Instance owned_subltype_step_shrltype_uninit_inst | 20.

  (** Extraction *)
  Lemma stratify_ltype_extract_shrltype π E L {rt} (lt : ltype rt) r κ l (T : stratify_ltype_post_hook_cont_t) :
    T L (True) _ (◁ uninit PtrSynType)%I (#())
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (ShrLtype lt κ) r (Owned) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    iMod (ltype_deinit_shr' with "Hl") as "Hl"; [done.. | | ].
    { left. done. }
    iExists _, _, _, _, _. iFrame.
    iFrame. simp_ltypes. done.
  Qed.
  Definition stratify_ltype_extract_shrltype_inst := [instance @stratify_ltype_extract_shrltype].
  Global Existing Instance stratify_ltype_extract_shrltype_inst.
End rule.
