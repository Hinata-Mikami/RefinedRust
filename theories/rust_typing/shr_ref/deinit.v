From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def.
From refinedrust Require Import options.

(** ** Lemmas about deinitializing *)

Section deinit.
  Context `{!typeGS Σ}.

  Lemma ltype_deinit_shr F π l st {rt} (lt : ltype rt) r κ wl :
    lftE ⊆ F →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned wl] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned false] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hlb & Hcreds & %r' & ? & Hb)".
    iMod (maybe_use_credit with "Hcreds Hb") as "(? & ? & %l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR.
    iSplitL "Hlb"; first by iFrame. iR.
    iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  Lemma ltype_deinit_shr' F π l st {rt} (lt : ltype rt) r κ wl :
    lftE ⊆ F →
    syn_type_compat PtrSynType st →
    £ (Nat.b2n wl) -∗
    (l ◁ₗ[π, Owned wl] r @ (ShrLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned wl] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hcred Hl".
    rewrite ltype_own_shr_ref_unfold /shr_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hlb & Hcreds & %r' & ? & Hb)".
    iMod (maybe_use_credit with "Hcreds Hb") as "(? & ? & %l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR.
    iSplitL "Hlb"; first by iFrame.
    iSplitR "Hl".
    { destruct wl; last done. simpl. rewrite /num_cred. iFrame. iApply lc_succ; iFrame. }
    iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iExists ly.
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
    iModIntro. iPureIntro. intros ?? Hst1 Hst2.
    destruct Hstcomp as [<- | (ly1' & Hst' & ->)].
    + f_equiv. by eapply syn_type_has_layout_inj.
    + eapply syn_type_has_layout_untyped_inv in Hst2 as (<- & _).
      f_equiv. by eapply syn_type_has_layout_inj.
  Qed.
  Definition owned_subltype_step_shrltype_uninit_inst := [instance owned_subltype_step_shrltype_uninit].
  Global Existing Instance owned_subltype_step_shrltype_uninit_inst | 20.

  (** Extraction *)
  Lemma stratify_ltype_extract_shrltype π E L {rt} (lt : ltype rt) r κ l (wl : bool) (T : stratify_ltype_post_hook_cont_t) :
    prove_with_subtype E L false ProveDirect (£ (Nat.b2n wl)) (λ L' κs R, (R -∗ T L' (True) _ (◁ uninit PtrSynType)%I (#())))
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (ShrLtype lt κ) r (Owned wl) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L' & %κs & %R & >(Hcred & HR)& HL & HT)".
    iMod (ltype_deinit_shr' with "Hcred Hl") as "Hl"; [done.. | | ].
    { left. done. }
    iSpecialize ("HT" with "HR").
    iExists _, _, _, _, _. iFrame.
    iFrame. simp_ltypes. done.
  Qed.
  Global Instance stratify_ltype_extract_shrltype_inst π E L {rt} (lt : ltype rt) r κ l (wl : bool) :
    StratifyLtypePostHook π E L (StratifyExtractOp κ) l (ShrLtype lt κ) r (Owned wl) :=
    λ T, i2p (stratify_ltype_extract_shrltype π E L lt r κ l wl T).
End rule.
