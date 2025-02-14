From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Stratification rules for mutable references *)
Section stratify.
  Context `{!typeGS Σ}.

  (** Structural rules *)
  Lemma stratify_ltype_mut_owned {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
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
      iMod ("Hcl" with "Hl Hb") as "(Hb & _)".
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
      by iMod ("Hcl" with "Hl Hb") as "($ & _)".
  Qed.
  Global Instance stratify_ltype_mut_owned_weak_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ :
    StratifyLtype π E L StratMutWeak mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Owned wl) :=
      λ T, i2p (stratify_ltype_mut_owned π E L StratMutWeak mdu ma ml l lt κ r wl γ T).
  Global Instance stratify_ltype_mut_owned_none_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) wl γ :
    StratifyLtype π E L StratMutNone mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Owned wl) := λ T, i2p (stratify_ltype_mut_owned π E L StratMutNone mdu ma ml l lt κ r wl γ T).

  Lemma stratify_ltype_mut_uniq {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ
      (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :
    (* get a lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L1),
      (∀ l', stratify_ltype π E L1 mu mdu ma ml l' lt r (Uniq κ γ) (λ L2 R rt' lt' r',
        (* validate the update *)
        prove_place_cond E L2 (Uniq κ' γ') lt lt' (λ upd,
          match upd with
          | ResultWeak Heq =>
              (* update obeys the contract, get a mutable reference *)
              match ma with
              | StratRefoldFull => cast_ltype_to_type E L2 lt' (λ ty', T L2 (llft_elt_toks κs ∗ R) _ (◁ (mut_ref κ ty'))%I (#(r', γ)))
              | _ => T L2 (llft_elt_toks κs ∗ R) _ (MutLtype lt' κ) (#(r', γ))
              end
          | ResultStrong =>
              (* unfold to an OpenedLtype *)
              ⌜ma = StratNoRefold⌝ ∗
              T L2 R _ (OpenedLtype (MutLtype lt' κ) (MutLtype lt κ) (MutLtype lt κ) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs)) (#(r', γ))
          end))))
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
    iMod ("Hc" with "[] [$LFT $TIME $LLCTX] HE HL") as "(HL & %upd & Hupd & Hs)"; first done.
    destruct upd as [ Heq | ].
    - (* weak *)
      subst rt'.
      destruct (decide (ma = StratRefoldFull)) as [Heq | ].
      + rewrite Heq. iDestruct "Hs" as "(%ty' & %Heqt & HT)".
        iPoseProof (full_eqltype_acc with "[$LFT $TIME $LLCTX] HE HL") as "#Heq"; [apply Heqt | ].

        iExists _, _, _, _, _. iFrame.
        iSplitR. { iModIntro. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iApply (logical_step_compose with "Hcl").
        iModIntro. iApply logical_step_intro.
        iIntros "[Hcl _] (Hb & HR)".
        iFrame. iMod ("Hcl" with "Hl Hb [] [Hupd]") as "(Hl & $ & _)".
        { iApply bor_kind_incl_refl. }
        { iSplit; first done. done. }
        iDestruct (mut_ltype_incl_uniq with "[] [] []") as "(_ & #Hincl & _)".
        { iIntros (?). iApply "Heq". }
        { iApply lft_incl_refl. }
        { iApply lft_incl_refl. }
        iPoseProof ("Hincl" with "Hl") as "Hl".
        by iApply (mut_ref_unfold_1_uniq with "Hl").
      + iAssert (T L2 (llft_elt_toks κs ∗ R) _ (MutLtype lt' κ) #(r', γ))%I with "[Hs]" as "Hs".
        { destruct ma; first done. all: done. }
        iExists _, _, _, _, _. iFrame.
        iSplitR. { iModIntro. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iApply (logical_step_compose with "Hcl").
        iModIntro. iApply logical_step_intro.
        iIntros "[Hcl _] (Hb & HR)".
        iFrame. iMod ("Hcl" with "Hl Hb [] [Hupd]") as "(Hl & $ & _)".
        { iApply bor_kind_incl_refl. }
        { iSplit; first done. done. }
        done.
    - (* strong *)
      iDestruct "Hs" as "(-> & Hs)".
      iDestruct "Hupd" as "%Hst".
      iExists _, _, _, _, _. iFrame.
      iSplitR. { done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hcl").
      iModIntro. iApply logical_step_intro.
      iIntros "[_ Hcl] (Hb & HR)".
      iFrame. iMod ("Hcl" with "Hl [] Hb") as "Hb".
      { done. }
      done.
  Qed.
  Global Instance stratify_ltype_mut_uniq_weak_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ :
    StratifyLtype π E L StratMutWeak mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Uniq κ' γ') :=
      λ T, i2p (stratify_ltype_mut_uniq π E L StratMutWeak mdu ma ml l lt κ r κ' γ' γ T).
  Global Instance stratify_ltype_mut_uniq_none_inst {rt} π E L mdu ma {M} (ml : M) l (lt : ltype rt) κ (r : (place_rfn rt)) κ' γ' γ :
    StratifyLtype π E L StratMutNone mdu ma ml l (MutLtype lt κ) (PlaceIn (r, γ)) (Uniq κ' γ') :=
      λ T, i2p (stratify_ltype_mut_uniq π E L StratMutNone mdu ma ml l lt κ r κ' γ' γ T).

  (** Unfolding instances *)
  Lemma stratify_ltype_ofty_mut {rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)%type) b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (MutLtype (◁ ty) κ) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (mut_ref κ ty)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply ltype_eq_sym. iApply mut_ref_unfold.
  Qed.
  Global Instance stratify_ltype_ofty_mut_inst {rt} π E L mu ma {M} (ml : M) l (ty : type rt) κ (r : place_rfn (place_rfn rt * gname)%type) b :
    StratifyLtype π E L mu StratDoUnfold ma ml l (◁ (mut_ref κ ty))%I r b | 30 :=
      λ T, i2p (stratify_ltype_ofty_mut π E L mu ma ml l ty κ r b T).

End stratify.
