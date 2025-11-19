From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Stratification rules for mutable references *)
Section stratify.
  Context `{!typeGS Σ}.

  (** Structural rules *)
  Lemma stratify_ltype_mut_owned mu mdu ma {rt} π E L {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ (T : stratify_ltype_cont_t) :
    (∀ l', stratify_ltype π E L mu mdu ma ml l' lt r (Uniq κ γ) (λ L' R rt' lt' r',
      match ma with
      | StratRefoldFull =>
          cast_ltype_to_type E L' lt' (λ ty', T L' R _ (◁ (mut_ref κ ty'))%I (PlaceIn (r', γ)))
      | _ =>
          T L' R _ (MutLtype lt' κ) (PlaceIn (r', γ))
      end))
    ⊢ stratify_ltype π E L mu mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Owned wl) T.
  Proof.
    iIntros "Hs". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hb".
    iPoseProof (mut_ltype_acc_owned F with "[$LFT $TIME $LLCTX] Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    destruct (decide (ma = StratRefoldFull)) as [Heq | ].
    - subst ma.
      iDestruct "Hc" as "(%ty' & %Heq' & HT)".
      iPoseProof (eqltype_use F with "[$LFT $TIME $LLCTX] HE HL") as "(Hvs & HL)"; [done | .. ].
      { apply full_eqltype_alt. apply Heq'. }
      (*iPoseProof (eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; first done.*)
      iModIntro. iExists L', R, _, _, _. iFrame.
      iSplitR. { simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      iMod ("Hvs" with "Hb") as "Hb".
      iMod ("Hcl" with "Hl Hb") as "Hb".
      iDestruct (mut_ref_unfold_1 ty' κ (Owned wl)) as "(_ & #Hi & _)".
      iMod (fupd_mask_mono with "(Hi Hb)") as "$"; first done.
      done.
    - iAssert (T L' R _ (MutLtype lt' κ) (PlaceIn (r', γ)))%I with "[Hc]" as "Hc".
      { destruct ma; done. }
      iModIntro. iExists L', R, _, _, _. iFrame.
    iSplitR. { simp_ltypes; done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro. iIntros "(Hb & $) Hcl".
      by iMod ("Hcl" with "Hl Hb") as "$".
  Qed.
  Definition stratify_ltype_mut_owned_weak_inst := [instance (@stratify_ltype_mut_owned StratMutWeak)].
  Global Existing Instance stratify_ltype_mut_owned_weak_inst.
  Definition stratify_ltype_mut_owned_none_inst := [instance (@stratify_ltype_mut_owned StratMutNone)].
  Global Existing Instance stratify_ltype_mut_owned_none_inst.

  Lemma stratify_ltype_mut_uniq mu mdu ma {rt} π E L {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
    (* get a lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L1),
      (∀ l', stratify_ltype π E L1 mu mdu ma ml l' lt r (Uniq κ γ) (λ L2 R rt' lt' r',
        (* validate the update *)
        prove_place_cond E L2 UpdStrong lt lt' (λ upd,
          li_tactic (check_llctx_place_update_kind_incl_goal E L2 upd.(puk_res_k) (UpdUniq [κ'])) (λ b,
          if b then
            (* update obeys the contract, get a mutable reference *)
            match ma with
            | StratRefoldFull => cast_ltype_to_type E L2 lt' (λ ty', T L2 (llft_elt_toks κs ∗ R) _ (◁ (mut_ref κ ty'))%I (#(r', γ)))
            | _ => T L2 (llft_elt_toks κs ∗ R) _ (MutLtype lt' κ) (#(r', γ))
            end
          else
            (* unfold to an OpenedLtype *)
            ⌜ma = StratNoRefold⌝ ∗
            T L2 R _ (OpenedLtype (MutLtype lt' κ) (MutLtype lt κ) (MutLtype lt κ) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs)) (#(r', γ))
          )))))
    ⊢ stratify_ltype π E L mu mdu ma ml l (MutLtype lt κ) (#(r, γ)) (Uniq κ' γ') T.
  Proof.
    iIntros "Hs". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hb".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "Hs" as "(%κs & %L1 & %Hal & Hs)".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "HF_cl" as "_".
    iPoseProof (mut_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Htok Hcl_tok Hb") as "Hb"; [done.. | ].
    iDestruct "Hb" as "(%Hly & #Hlb & >(%l' & Hl & Hb & Hcl))".
    iPoseProof ("Hs" with "[//] [//] [//] [$LFT $TIME $LLCTX] HE HL Hb") as "Hb".
    iMod "Hb" as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hcond & Hstep & Hc)".
    iMod ("Hc" with "[] [$LFT $TIME $LLCTX] HE HL") as "(HL & %upd & #Hincl & Hcond &  %Hsteq & Hs)"; first done.
    unfold check_llctx_place_update_kind_incl_goal.
    iDestruct "Hs" as "(%b & %Hb & Hs)".
    destruct b.
    - (* weak *)
      iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl2"; first apply Hb.
      iPoseProof (typed_place_cond_Uniq_rt_eq with "Hincl2 Hcond") as "%Heq".
      subst rt'.
      iAssert (∃ lt2, ⌜full_eqltype E L2 (MutLtype lt' κ) lt2⌝ ∗ T L2 (llft_elt_toks κs ∗ R) _ lt2 # (r', γ))%I with "[Hs]" as "HT".
      { destruct ma.
        - iDestruct "Hs" as "(%ty & %Heqty & $)".
          iPureIntro. apply mut_ref_unfold_full_eqltype. done.
        - iFrame. done.
        - iFrame. done. }
      iDestruct "HT" as "(%lt2 & %Heql & $)".
      iPoseProof (full_eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; [apply Heql | ].
      iFrame.
      iSplitR. {
        unshelve iSpecialize ("Heq" $! inhabitant inhabitant); [apply _.. | ].
        iApply (ltype_eq_syn_type with "Heq"). }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hcl").
      iModIntro. iApply logical_step_intro.
      iIntros "[Hcl _] (Hb & HR)".
      iFrame. iMod ("Hcl" with "Hl Hb Hincl2 [//] Hcond") as "(Hl & $ & _)".
      iDestruct ("Heq" $! _ _) as "(Heq1 & _)".
      iMod (ltype_incl_use with "Heq1 Hl") as "Hb"; done.
    - (* strong *)
      iDestruct "Hs" as "(-> & Hs)".
      iFrame. iR.
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hcl").
      iModIntro. iApply logical_step_intro.
      iIntros "[_ Hcl] (Hb & HR)".
      iFrame. iMod ("Hcl" with "Hl [] Hb") as "Hb".
      { done. }
      done.
  Qed.
  Definition stratify_ltype_mut_uniq_weak_inst := [instance (@stratify_ltype_mut_uniq StratMutWeak)].
  Global Existing Instance stratify_ltype_mut_uniq_weak_inst.
  Definition stratify_ltype_mut_uniq_none_inst := [instance (@stratify_ltype_mut_uniq StratMutNone)].
  Global Existing Instance stratify_ltype_mut_uniq_none_inst.

  (** Unfolding instances *)
  Lemma stratify_ltype_ofty_mut {rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)%type) b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (MutLtype (◁ ty) κ) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (mut_ref κ ty)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply ltype_eq_sym. iApply mut_ref_unfold.
  Qed.
  Definition stratify_ltype_ofty_mut_inst := [instance @stratify_ltype_ofty_mut].
  Global Existing Instance stratify_ltype_ofty_mut_inst | 30.
End stratify.
