From refinedrust Require Export type ltypes.
From refinedrust Require Import int programs.
From refinedrust.array Require Import def subltype.
From refinedrust Require Import options.

Section place.
  Context `{!typeGS Σ}.

  Local Lemma typed_place_cond_array_lift {rt} (def : type rt) len bmin i lts (lt1 lt2 : ltype rt) :
    interpret_iml (◁ def)%I len lts !! i = Some lt1 →
    ([∗ list] lt ∈ lts, place_kind_outlives_unblock_lt bmin lt.2) -∗
    typed_place_cond bmin lt1 lt2 -∗
    [∗ list] lt1;lt2 ∈ interpret_iml (◁ def) len lts;<[i:= lt2]> (interpret_iml (◁ def) len lts), typed_place_cond bmin lt1 lt2.
  Proof.
    iIntros (Hlook) "#Houtl Hcond".
    rewrite -{1}(list_insert_id (interpret_iml _ _ _) i lt1); last done.
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ lt1 lt2, typed_place_cond bmin lt1 lt2) 0); cycle 1.
    { by eapply lookup_lt_Some. }
    { by eapply lookup_lt_Some. }
    iFrame. iApply big_sepL2_intro; first done.
  iModIntro. iIntros (k lt1' lt2' Hlook' ?). case_decide; first done.
    assert (lt1' = lt2') as -> by congruence.
    apply lookup_interpret_iml_Some_inv in Hlook' as (? & [-> | Hel]).
    { iApply typed_place_cond_refl_ofty. }
    apply list_elem_of_lookup_1 in Hel as (k' & Hlook2).
    iApply typed_place_cond_refl.
    iPoseProof (big_sepL_lookup _ _ k' with "Houtl") as "Ha"; first done.
    done.
  Qed.

  (** ** typed_place *)
  Import EqNotations.

  Lemma place_update_kind_rt_same_array {bmin} :
    place_update_kind_rt_same (bmin ⊓ₚ RestrictWeak) = true.
  Proof.
    destruct bmin; reflexivity.
  Defined.

  Local Lemma array_incl_blocked_lfts_unblock {rt} (lts : list (nat * ltype rt)) b :
    UpdUniq (mjoin ((λ x, ltype_blocked_lfts x.2) <$> lts)) ⪯ₚ b -∗
    [∗ list] lt ∈ lts, place_kind_outlives_unblock_lt b lt.2.
  Proof.
    iIntros "#Hincl".
    iApply big_sepL_intro. iModIntro. iIntros (k [? lt] Hlook).
    simpl. unfold place_kind_outlives_unblock_lt.
    iApply place_update_kind_outlives_incl; first done.
    simpl.
    iApply lft_list_incl_subset.
    apply list_subseteq_mjoin.
    apply list_elem_of_fmap.
    eexists; split; first last.
    { apply list_elem_of_lookup. eauto. }
    done.
  Qed.

  Lemma typed_place_array_owned π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) wl bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜lctx_place_update_kind_outlives E L1 bmin (mjoin ((λ lt, ltype_blocked_lfts lt.2) <$> (lts)))⌝ ∗
        typed_place π E L1 (l offsetst{ty_syn_type def}ₗ i') lt r (bmin ⊓ₚ RestrictWeak) (Owned false) P (λ L2 κs li bi bmin2 rti ltyi ri updcx,
          T L2 κs li bi bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (mkPUpd _ bmin
              (listRT (place_rfnRT rt))
              (ArrayLtype def len ((Z.to_nat i', rew <-(opt_place_update_eq_use _ _ _ place_update_kind_rt_same_array upd'.(pupd_eq_2)) in upd'.(pupd_lt)) :: lts))
              (#(<[Z.to_nat i' := rew <-[place_rfnRT](opt_place_update_eq_use _ _ _ place_update_kind_rt_same_array upd'.(pupd_eq_2)) in upd'.(pupd_rfn)]> rs))
              upd'.(pupd_R)
              (upd'.(pupd_performed)  ⊔ₚₖ UpdUniq (mjoin ((λ lt, ltype_blocked_lfts lt.2) <$> (lts))))
              opt_place_update_eq_refl
              opt_place_update_eq_refl
            )))
        )))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Owned wl) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) T.
  Proof.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (array_ltype_acc_owned with "Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & >(Hb & Hcl))"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "%Hi".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { split; last nia.
      specialize (MinInt_le_0 ISize). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred Hcl".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite length_interpret_iml in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite length_interpret_iml. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use _ _ _ _ Houtl with " HE HL") as "#Houtl".
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[Hb]").
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs l2 b2 bmin0 rti ltyi ri' updcx) "Hi Hc".
    iApply ("Hcont" with "Hi").
    iIntros (upd) "#Hincl Hl2 %Hsteq HR Hcond".
    iMod ("Hc" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hsteq2 & Hcond & #Hincl2 & ? & ? & HL & Hcont)".
    iFrame. simpl.
    generalize (opt_place_update_eq_use _ _ (pupd_rt upd') place_update_kind_rt_same_array upd'.(pupd_eq_2)).
    intros Heq.
    destruct upd' as [rt' lt' r' ? ? ? ?].  simpl in *.
    subst rt'.
    iPoseProof ("Hcl_b" with "[Hl]") as "Hl".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq2//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" with "[//] Hl") as "Hb ".
    iFrame. iR.

    iSplitL; first last.
    { iApply place_update_kind_incl_lub; last done.
      iApply place_update_kind_incl_trans; first done.
      iApply place_update_kind_restrict_incl. }
    iApply array_ltype_place_cond.
    { apply place_access_rt_rel_refl. }
    { done. }
    iApply typed_place_cond_array_lift; [ done | | ].
    { (* so now I need to show that I actually outlive the time when the lts become unblockable. *)
      iApply array_incl_blocked_lfts_unblock.
      iApply place_update_kind_max_incl_r. }
    { iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_l. }
  Qed.
  Definition typed_place_array_owned_inst := [instance @typed_place_array_owned].
  Global Existing Instance typed_place_array_owned_inst | 30.

  Lemma typed_place_array_uniq π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ γ bmin0 ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      (* get lifetime token *)
      li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜lctx_place_update_kind_outlives E L2 (UpdUniq [κ]) (mjoin ((λ lt, ltype_blocked_lfts lt.2) <$> (lts)))⌝ ∗
        ⌜lctx_place_update_kind_incl E L2 (UpdUniq [κ]) bmin0⌝ ∗
        typed_place π E L2 (l offsetst{ty_syn_type def}ₗ i') lt r (bmin0 ⊓ₚ RestrictWeak) (Owned false) P (λ L3 κs' li bi bmin2 rti ltyi ri updcx,
          T L3 (κs ++ κs') li bi bmin2 rti ltyi ri
            (λ L4 upd cont, updcx L4 upd (λ upd',
              ⌜lctx_place_update_kind_incl E L4 upd'.(pupd_performed) (UpdUniq [κ])⌝ ∗
              cont (mkPUpd _ bmin0
                (listRT (place_rfnRT rt))
                (ArrayLtype def len ((Z.to_nat i', rew <-(opt_place_update_eq_use _ _ _ place_update_kind_rt_same_array upd'.(pupd_eq_2)) in upd'.(pupd_lt)) :: lts))
                (#(<[Z.to_nat i' := rew <-[place_rfnRT](opt_place_update_eq_use _ _ _ place_update_kind_rt_same_array upd'.(pupd_eq_2)) in upd'.(pupd_rfn)]> rs))
                upd'.(pupd_R)
                (UpdUniq [κ])
                opt_place_update_eq_refl
                opt_place_update_eq_refl
              )))
          ))))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin0 (Uniq κ γ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iDestruct "HT" as "(%κs & %L1 & %Hal & HT)".
    iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcltok & HL)"; [done.. | ].
    iPoseProof (array_ltype_acc_uniq with "CTX Htok Hcltok Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & Hb)"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "%Hi".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME Hcl"); [done.. | ].
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { split; last nia.
      specialize (MinInt_le_0 ISize). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred Hcl".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite length_interpret_iml in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite length_interpret_iml. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & %Hincl & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Houtl"; first apply Houtl.
    iPoseProof (lctx_place_update_kind_incl_use _ _ _ _ Hincl with "HE HL") as "#Houtl2".
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[Hb]").
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs' l2 b2 bmin1 rti ltyi ri' updcx) "Hi Hc".
    iApply ("Hcont" with "Hi").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hc" with "Hincl Hl2 [//] [$] Hcond") as "Hc".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hc" with "HL Hcont") as (upd') "(Hl & %Hsteq2 & Hcond & #Hincl2 & ? & ? & HL & %Hincl2 & Hcont)".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl3"; first apply Hincl2.
    iFrame. simpl.

    generalize (opt_place_update_eq_use _ _ (pupd_rt upd') place_update_kind_rt_same_array upd'.(pupd_eq_2)).
    intros Heq.
    destruct upd' as [rt' lt' r' ? ? ? ?].  simpl in *.
    subst rt'.
    iPoseProof ("Hcl_b" with "[Hl]") as "Hl".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq2//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" $! _ _ _ (UpdUniq [κ]) with "[//] [] [] [Hcond] Hl") as "(Hb & ? & Hcond)".
    { rewrite length_insert//. }
    { iApply place_update_kind_incl_refl. }
    { iApply typed_place_cond_array_lift; [ done | | ].
      - iApply array_incl_blocked_lfts_unblock. done.
      - iApply typed_place_cond_incl; last done. done. }
    iFrame.
    iR. iR. rewrite llft_elt_toks_app. by iFrame.
  Qed.
  Definition typed_place_array_uniq_inst := [instance @typed_place_array_uniq].
  Global Existing Instance typed_place_array_uniq_inst | 30.

  (* TODO this is a problem, because we can only get strong below OpenedLtype etc. *)
  Lemma typed_place_array_shared π E L {rt rtv} (def : type rt) (lts : list (nat * ltype rt)) (len : nat) (rs : list (place_rfn rt)) κ bmin ly l it v (tyv : type rtv) (i : rtv) P T :
    (∃ i',
      ⌜syn_type_has_layout (ty_syn_type def) ly⌝ ∗
      subsume_full E L false (v ◁ᵥ{π} i @ tyv) (v ◁ᵥ{π} i' @ int it) (λ L1 R2, R2 -∗
      ⌜(0 ≤ i')%Z⌝ ∗ ⌜(i' < len)%Z⌝ ∗
      ∀ lt r,
        (* relies on Lithium's built-in simplification of lookups. *)
        ⌜interpret_iml (◁ def) len lts !! Z.to_nat i' = Some lt⌝ -∗
        ⌜rs !! Z.to_nat i' = Some r⌝ -∗
        (* sidecondition for other components *)
        ⌜lctx_place_update_kind_outlives E L1 bmin (mjoin ((λ lt, ltype_blocked_lfts lt.2) <$> (lts)))⌝ ∗
        typed_place π E L1 (l offsetst{ty_syn_type def}ₗ i') lt r (bmin ⊓ₚ RestrictWeak) (Shared κ) P (λ L3 κs' li bi bmin2 rti ltyi ri updcx,
        T L3 κs' li bi bmin2 rti ltyi ri
          (λ L4 upd cont, updcx L4 upd (λ upd',
            cont (mkPUpd _ bmin
              (listRT (place_rfnRT rt))
              (ArrayLtype def len ((Z.to_nat i', rew <-(opt_place_update_eq_use _ _ _ place_update_kind_rt_same_array upd'.(pupd_eq_2)) in upd'.(pupd_lt)) :: lts))
              (#(<[Z.to_nat i' := rew <-[place_rfnRT](opt_place_update_eq_use _ _ _ place_update_kind_rt_same_array upd'.(pupd_eq_2)) in upd'.(pupd_rfn)]> rs))
              upd'.(pupd_R)
              (upd'.(pupd_performed) ⊔ₚₖ UpdUniq (mjoin ((λ lt, ltype_blocked_lfts lt.2) <$> (lts))))
              opt_place_update_eq_refl
              opt_place_update_eq_refl
            )))
          )))
    ⊢ typed_place π E L l (ArrayLtype def len lts) (#rs) bmin (Shared κ) (BinOpPCtx (PtrOffsetOp ly) (IntOp it) π v rtv tyv i :: P) T.
  Proof.
    iIntros "(%i' & %Hst & HT)".
    iIntros (????) "#CTX #HE HL Hl Hcont".
    simpl. iIntros "Hv".
    iApply fupd_wp.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L' & %R2 & >(Hi & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(% & % & HT)".
    iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (array_ltype_acc_shared with "Hl") as "(%ly' & %Hst' & %Hly & %Hsz & #Hlb & >(Hb & Hcl))"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iMod "HclF" as "_".
    iEval (rewrite /ty_own_val/=) in "Hi".
    iDestruct "Hi" as "%Hi".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply wp_fupd.
    iApply wp_ptr_offset.
    { eapply val_to_of_loc. }
    { done. }
    { split; last nia.
      specialize (MinInt_le_0 ISize). lia. }
    { iPoseProof (loc_in_bounds_array_offset _ _ (Z.to_nat i') with "Hlb") as "Hlb'"; first lia.
      rewrite Z2Nat.id; last done.
      iApply loc_in_bounds_shorten_suf; last done. lia. }
    { iApply loc_in_bounds_shorten_suf; last done. lia. }
    iModIntro. iNext. iIntros "Hcred".
    iModIntro. iExists _. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite length_interpret_iml in Hlen_eq.
    clear i. set (i := Z.to_nat i').
    destruct (lookup_lt_is_Some_2 (interpret_iml (◁ def) len lts)%I i) as (lti & Hlook_lti).
    { rewrite length_interpret_iml. lia. }
    destruct (lookup_lt_is_Some_2 rs i) as (ri & Hlook_ri).
    { lia. }
    iPoseProof ("HT" $! lti ri with "[//] [//]") as "(%Houtl & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Houtl"; first apply Houtl.
    iPoseProof (big_sepL2_insert_acc with "Hb") as "((%Hsti & Hb) & Hcl_b)"; [done | done | ].
    iPoseProof ("HT" with "[//] [//] [$LFT $TIME $LLCTX] HE HL") as "Hc".
    rewrite /OffsetLocSt/use_layout_alg' Hst/=.
    rewrite /offset_loc.
    iApply ("Hc" with "[Hb]").
    { subst i. rewrite Z2Nat.id//. }
    iIntros (L2 κs l2 b2 bmin0 rti ltyi ri' updcx) "Hi Hc".
    iApply ("Hcont" with "Hi").

    iIntros (upd) "#Hincl Hl2 %Hsteq HR Hcond".
    iMod ("Hc" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hsteq2 & Hcond & #Hincl2 & ? & ? & HL & Hcont)".
    iFrame. simpl.
    generalize (opt_place_update_eq_use _ _ (pupd_rt upd') place_update_kind_rt_same_array upd'.(pupd_eq_2)).
    intros Heq.
    destruct upd' as [rt' lt' r' ? ? ? ?].  simpl in *.
    subst rt'.
    iPoseProof ("Hcl_b" with "[Hl]") as "Hl".
    { rewrite /i Z2Nat.id; last done. iFrame. rewrite -Hsteq2//. }
    rewrite insert_interpret_iml.
    iMod ("Hcl" with "[//] [] Hl") as "Hb ".
    { rewrite length_insert//. }
    iFrame. iR.

    iSplitL; first last.
    { iApply place_update_kind_incl_lub; last done.
      iApply place_update_kind_incl_trans; first done.
      iApply place_update_kind_restrict_incl. }
    iApply array_ltype_place_cond.
    { apply place_access_rt_rel_refl. }
    { done. }
    iApply typed_place_cond_array_lift; [ done | | ].
    { (* so now I need to show that I actually outlive the time when the lts become unblockable. *)
      iApply array_incl_blocked_lfts_unblock.
      iApply place_update_kind_max_incl_r. }
    { iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_l. }
  Qed.
  Definition typed_place_array_shared_inst := [instance @typed_place_array_shared].
  Global Existing Instance typed_place_array_shared_inst | 30.
End place.

Section place_cond.
  Context `{!typeGS Σ}.

  (** ** prove_place_cond instances *)
  (* TODO: should probably augment FoldableRelation to be able to pass something to the continuation. *)
  (*
  Program Definition prove_place_cond_list_interp {rt1 rt2} (k : bor_kind) (len : nat) : FoldableRelation :=
    {|
      fr_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2)) (T : iProp Σ) :=
        (prove_place_cond E L k lt1 lt2 (λ upd, T))%I;
      fr_cap := len;
      fr_inv := True;
      fr_core_rel (E : elctx) (L : llctx) (i : nat) (lt1 : (ltype rt1)) (lt2 : (ltype rt2))  :=
        (∃ upd : access_result rt1 rt2,
          match upd with
          | ResultWeak _ => typed_place_cond k lt1 lt2
          | ResultStrong => ⌜ltype_st lt1 = ltype_st lt2⌝%I
          end)%I
    |}.
  Next Obligation.
    iIntros (???? ? E L i a b T ?) "#CTX #HE HL Hcond".
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hincl)".
    iDestruct "Hincl" as "(%upd & ? & $)".
    iModIntro. eauto with iFrame.
  Qed.
  Global Typeclasses Opaque prove_place_cond_list_interp.
   *)

  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  (* TODO: similar unfolding for array
  Lemma prove_place_cond_unfold_mut_l E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (MutLtype (◁ ty) κ) lt T -∗
    prove_place_cond E L k (◁ (mut_ref ty κ)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_l_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k (◁ (mut_ref ty κ))%I lt | 10 := λ T, i2p (prove_place_cond_unfold_mut_l E L ty lt κ k T).
  Lemma prove_place_cond_unfold_mut_r E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (MutLtype (◁ ty) κ) T -∗
    prove_place_cond E L k lt (◁ (mut_ref ty κ)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply mut_ref_unfold_full_eqltype; done.
  Qed.
  Global Instance prove_place_cond_unfold_mut_r_inst E L {rt1 rt2} `{Inhabited rt1} (ty : type rt1) (lt : ltype rt2) κ k :
    ProvePlaceCond E L k lt (◁ (mut_ref ty κ))%I | 10 := λ T, i2p (prove_place_cond_unfold_mut_r E L ty lt κ k T).
   *)
  (*
  Lemma prove_place_cond_array_ltype E L {rt} (def1 def2 : type rt) (lts1 : ltype rt) (lts2 : ltype rt) len1 len2 κ1 κ2 k T :
    ⌜len1 = len2⌝ ∗ ⌜def1 = def2⌝ ∗
    (*prove_place_cond E L k lt1 lt2 (λ upd, T $ access_result_lift (λ rt, (place_rfn rt * gname)%type) upd) -∗*)
    prove_place_cond E L k (ArrayLtype def1 len1 lts1) (ArrayLtype def2 len2 lts2) T.
  Proof.
  Abort.
   *)
  (*Global Instance prove_place_cond_mut_ltype_inst E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ1 κ2 k :*)
    (*ProvePlaceCond E L k (MutLtype lt1 κ1) (MutLtype lt2 κ2) | 5 := λ T, i2p (prove_place_cond_mut_ltype E L lt1 lt2 κ1 κ2 k T).*)
End place_cond.
