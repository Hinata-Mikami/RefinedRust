From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def unfold subltype.
From refinedrust Require Import options.

(** ** Place instances for structs *)

Section place.
  Context `{!typeGS Σ}.

  (** Place lemmas for products *)
  (* NOTE: these lemmas require sideconditions for the unaffected components of the product that state that we can keep blocked subplaces blocked because the outer bor_kinds outlive the the blocking lifetimes.
    It would be good if we could remove this sidecondition with a smarter setup of ltypes... TODO
      But it's not clear that that is possible: We can arbitrarily shorten the lifetime of outer things -- then at the later point we just don't knwo anymore that really the lender expects it back at a later point.
    *)

  Local Lemma struct_lift_place_cond_homo {rts} (lts : hlist ltype rts) i (lto lto' : ltype (lnth (unit : RT) rts i)) bmin0 :
    hnth (UninitLtype UnitSynType) lts i = lto →
    i < length rts →
    ([∗ list] κ0 ∈ concat ((λ X : RT, ltype_blocked_lfts) +c<$> lts), bor_kind_outlives bmin0 κ0) -∗
    typed_place_cond bmin0 lto lto' -∗
    [∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts (hlist_insert_id (unit : RT) rts lts i lto'), typed_place_cond bmin0 (projT2 ty1) (projT2 ty2).
  Proof.
    iIntros (Hlto ?) "#Houtl Hcond".
    rewrite hzipl_hlist_insert_id.
    rewrite -(list_insert_id (hzipl rts lts) i (existT _ lto)).
    2: { rewrite -Hlto. apply hzipl_lookup_hnth. done. }
    rewrite (big_sepL2_insert _ _ _ _ _ (λ _ a b, typed_place_cond _ _ _) 0%nat); simpl.
    2: { rewrite length_hzipl. lia. }
    2: { rewrite length_insert length_hzipl. lia. }
    iSplitL "Hcond"; first done.
    iApply big_sepL2_intro. { rewrite length_insert; done. }
    iIntros "!>" (k [rt1 lt1] [rt2 lt2] Hlook1 Hlook2).
    case_decide as Heqki; first done.
    rewrite list_lookup_insert_ne in Hlook2; last done.
    rewrite Hlook2 in Hlook1. injection Hlook1 as [= -> Heq2].
    apply existT_inj in Heq2 as ->.
    iApply typed_place_cond_refl.
    iPoseProof (big_sepL_concat_lookup _ _ k with "Houtl") as "Ha".
    { eapply hcmap_lookup_hzipl. done. }
    simpl. done.
  Qed.

  Lemma typed_place_struct_owned {rts} (lts : hlist ltype rts) π E L (r : plist place_rfnRT rts) sls f wl bmin0 P l
    (T : place_cont_t (plist place_rfnRT rts)) :
    ((* sidecondition for other components *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (concat ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : RT) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L (l atst{sls}ₗ f) lto ro bmin0 (Owned false) P
        (λ L' κs l1 b2 bmin rti ltyi ri mstrong,
          T L' κs l1 b2 bmin rti ltyi ri
          (mk_mstrong (fmap (λ strong, mk_strong
            (λ rt', plist place_rfnRT (<[i := strong.(strong_rt) rt']> rts))
            (λ rt' lt' r', StructLtype (hlist_insert rts lts i _ (strong.(strong_lt) _ lt' r')) sls)
            (λ rt' (r' : place_rfn rt'), #(plist_insert rts r i _ (strong.(strong_rfn) _ r')))
            strong.(strong_R)) mstrong.(mstrong_strong))
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, StructLtype (hlist_insert_id (unit : RT) rts lts i (weak.(weak_lt) lti2 ri2)) sls)
            (λ (r' : place_rfn rti), #(plist_insert_id (unit : RT) rts r i (weak.(weak_rfn) r')))
            weak.(weak_R)) mstrong.(mstrong_weak))
          ))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Owned wl) (GetMemberPCtx sls f :: P) T.
  Proof.
    iIntros "(%Houtl & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL #Hincl0 Hl HΦ/=".
    iPoseProof (struct_ltype_acc_owned F with "Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".

    eapply (sls_field_index_of_lookup) in Hfield as (ly & Hfield).
    assert (i < length rts)%nat. { rewrite -Hmem. eapply lookup_lt_Some. done. }
    (* Note: if we later on want to allow the struct alg to change order of fields, then we need to change pad_struct (or use something else here), because it currently relies on the order of the types and the order of the sl members matching up *)
    assert (field_index_of (sl_members sl) f = Some i) as Hfield'.
    { eapply struct_layout_spec_has_layout_lookup; done. }
    iApply (wp_logical_step with "TIME Hcl"); [done | solve_ndisj.. | ].
    iApply (wp_get_member).
    { apply val_to_of_loc. }
    { done. }
    { by eapply field_index_of_to_index_of. }
    { done. }
    iModIntro. iNext. iIntros "Hcred Hcl". iExists _. iSplitR; first done.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : RT) (UninitLtype UnitSynType) (PlaceIn ()) _ r); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 [Hb]").
    { rewrite -Hlto -Hro. done. }
    iModIntro. iIntros (L' κs l2 b2 bmin rti ltyi ri [strong weak]) "#Hincl1 Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hincl1 Hli").
    simpl. iSplit.
    - (* strong *)
      destruct strong as [strong | ]; last done.
      iIntros (rti2 ltyi2 ri2) "Hli %Hst'".
      iDestruct "Hcont" as "(Hcont & _)".
      iMod ("Hcont" with "Hli [//]") as "(Hb1 & %Hst2 & HR)".
      iDestruct "Hc_close" as "[Hc_close _]".
      iPoseProof ("Hc_close" with "Hb1 []") as "Hb".
      { rewrite -Hst2. done. }
      iFrame.
      iMod ("Hcl" with "[] Hb") as "Hb".
      { rewrite length_insert //. }
      iFrame. iPureIntro. done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hcont" as "(_ & Hcont)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hli Hcond".
      iMod ("Hcont" $! _ _ bmin' with "Hincl2 Hli Hcond") as "(Hb1 & Hcond & HL & HR)".
      simpl. iDestruct "Hc_close" as "[_ Hc_close]".
      iPoseProof ("Hc_close" with "Hb1") as "Hb".
      iFrame "HL HR".
      iDestruct "Hcond" as "#Hcond".
      iMod ("Hcl" with "[] [Hb]") as "Hb".
      { done. }
      { iApply "Hb". iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "<-". done. }
      iFrame "Hb".
      iApply (typed_place_cond_struct_lift with "[] []").
      + iApply (struct_lift_place_cond_homo with "Houtl Hcond"); [done | lia].
      + iPureIntro. clear. induction rts; simpl; first done.
        constructor; first apply place_access_rt_rel_refl. done.
  Qed.
  Definition typed_place_struct_owned_inst := [instance @typed_place_struct_owned].
  Global Existing Instance typed_place_struct_owned_inst | 30.

  Lemma typed_place_struct_uniq {rts} (lts : hlist ltype rts) π E L (r : plist place_rfnRT rts) sls f κ γ bmin0 P l
    (T : place_cont_t (plist place_rfnRT rts)) :
    ((* sidecondition for other components *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (concat ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* get lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : RT) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L2 (l atst{sls}ₗ f) lto ro bmin0 (Owned false) P
        (λ L' κs' l1 b2 bmin rti ltyi ri mstrong,
          T L' (κs ++ κs') l1 b2 bmin rti ltyi ri
          (mk_mstrong
          None
          (* TODO allow strong by opening *)
          (*
          (fmap (λ strong, mk_strong
            (λ rt', plist place_rfn (<[i := strong.(strong_rt) rt']> rts))
            (λ rt' lt' r', StructLtype (hlist_insert rts lts i _ (strong.(strong_lt) _ lt' r')) sls)
            (λ rt' (r' : place_rfn rt'), #(plist_insert rts r i _ (strong.(strong_rfn) _ r')))
            strong.(strong_R)) strong)
            *)
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, StructLtype (hlist_insert_id (unit : RT) rts lts i (weak.(weak_lt) lti2 ri2)) sls)
            (λ (r' : place_rfn rti), #(plist_insert_id (unit : RT) rts r i (weak.(weak_rfn) r')))
            weak.(weak_R)) mstrong.(mstrong_weak))
          )))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Uniq κ γ) (GetMemberPCtx sls f :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%Houtl & %κs & %L' &  %Hal & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL #Hincl0 Hl HΦ/=".

    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".
    iApply fupd_wp.
    iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcltok & HL)"; [done.. | ].
    iMod "HclF" as "_".

    iPoseProof (struct_ltype_acc_uniq F with "[$LFT $TIME $LLCTX] Htok Hcltok Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.

    eapply (sls_field_index_of_lookup) in Hfield as (ly & Hfield).
    assert (i < length rts)%nat. { rewrite -Hmem. eapply lookup_lt_Some. done. }
    (* Note: if we later on want to allow the struct alg to change order of fields, then we need to change pad_struct (or use something else here), because it currently relies on the order of the types and the order of the sl members matching up *)
    assert (field_index_of (sl_members sl) f = Some i) as Hfield'.
    { eapply struct_layout_spec_has_layout_lookup; done. }
    iApply (wp_logical_step with "TIME Hcl"); [done | solve_ndisj.. | ].
    iApply (wp_get_member).
    { apply val_to_of_loc. }
    { done. }
    { by eapply field_index_of_to_index_of. }
    { done. }
    iModIntro. iModIntro. iNext. iIntros "Hcred Hcl". iExists _. iSplitR; first done.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : RT) (UninitLtype UnitSynType) (PlaceIn ()) _ r); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [Hincl0] [Hb]").
    { destruct bmin0; done. }
    { rewrite -Hlto -Hro. done. }
    iModIntro. iIntros (L2 κs' l2 b2 bmin rti ltyi ri [strong weak]) "#Hincl1 Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hincl1 Hli").
    simpl. iSplit.
    - (* strong *)
      destruct strong as [strong | ]; last done.
      done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hcont" as "(_ & Hcont)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hli Hcond".
      iMod ("Hcont" $! _ _ bmin' with "Hincl2 Hli Hcond") as "(Hb1 & Hcond & HL & HR)".
      simpl. iDestruct "Hc_close" as "[_ Hc_close]".
      iPoseProof ("Hc_close" with "Hb1") as "Hb".
      iFrame "HR".
      iDestruct "Hcond" as "#Hcond".
      iDestruct "Hcl" as "(Hcl & _)".
      iMod ("Hcl" with "[] [Hb] [] ") as "(Hb & Htoks & Hcond')".
      { done. }
      { iApply "Hb". iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "<-". done. }
      { iApply (struct_lift_place_cond_homo with "Houtl Hcond"); [done | lia]. }
      iFrame "Hb".
      rewrite llft_elt_toks_app. iFrame.
      iApply typed_place_cond_incl; last done.
      iApply bor_kind_min_incl_r.
  Qed.
  Definition typed_place_struct_uniq_inst := [instance @typed_place_struct_uniq].
  Global Existing Instance typed_place_struct_uniq_inst | 30.

  Lemma typed_place_struct_shared {rts} (lts : hlist ltype rts) π E L (r : plistRT rts) sls f κ bmin0 P l
    (T : place_cont_t (plistRT rts)) :
    ((* sidecondition for other components *)
    ⌜Forall (lctx_bor_kind_outlives E L bmin0) (concat ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : RT) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L (l atst{sls}ₗ f) lto ro bmin0 (Shared κ) P
        (λ L' κs l1 b2 bmin rti ltyi ri mstrong,
          T L' κs l1 b2 bmin rti ltyi ri
          (mk_mstrong
          None (* TODO *)
          (*(fmap (λ strong, mk_strong*)
            (*(λ rt', plist place_rfn (<[i := strong.(strong_rt) rt']> rts))*)
            (*(λ rt' lt' r', StructLtype (hlist_insert rts lts i _ (strong.(strong_lt) _ lt' r')) sls)*)
            (*(λ rt' (r' : place_rfn rt'), #(plist_insert rts r i _ (strong.(strong_rfn) _ r')))*)
            (*strong.(strong_R)) strong)*)
          (fmap (λ weak, mk_weak
            (λ lti2 ri2, StructLtype (hlist_insert_id (unit : RT) rts lts i (weak.(weak_lt) lti2 ri2)) sls)
            (λ (r' : place_rfn rti), #(plist_insert_id (unit : RT) rts r i (weak.(weak_rfn) r')))
            weak.(weak_R)) mstrong.(mstrong_weak))
          ))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Shared κ) (GetMemberPCtx sls f :: P) T.
  Proof.
    iIntros "(% & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL #Hincl0 Hl HΦ/=".
    iPoseProof (struct_ltype_acc_shared F with "Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iPoseProof (lctx_bor_kind_outlives_all_use with "[//] HE HL") as "#Houtl".

    eapply (sls_field_index_of_lookup) in Hfield as (ly & Hfield).
    assert (i < length rts)%nat. { rewrite -Hmem. eapply lookup_lt_Some. done. }
    (* Note: if we later on want to allow the struct alg to change order of fields, then we need to change pad_struct (or use something else here), because it currently relies on the order of the types and the order of the sl members matching up *)
    assert (field_index_of (sl_members sl) f = Some i) as Hfield'.
    { eapply struct_layout_spec_has_layout_lookup; done. }
    (*iApply (wp_logical_step with "TIME Hcl"); [done | solve_ndisj.. | ].*)
    iApply (wp_get_member).
    { apply val_to_of_loc. }
    { done. }
    { by eapply field_index_of_to_index_of. }
    { done. }
    iModIntro. iNext. iIntros "Hcred". iExists _. iR.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : RT) (UninitLtype UnitSynType) (PlaceIn ()) _ r); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hincl0 [Hb]").
    { rewrite -Hlto -Hro. done. }
    iIntros (L' κs l2 b2 bmin rti ltyi ri [strong weak]) "#Hincl1 Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hincl1 Hli").
    simpl. iSplit.
    - (* strong *)
      done.
    - (* weak *)
      destruct weak as [ weak | ]; last done.
      iDestruct "Hcont" as "(_ & Hcont)".
      iIntros (ltyi2 ri2 bmin') "#Hincl2 Hli Hcond".
      iMod ("Hcont" $! _ _ bmin' with "Hincl2 Hli Hcond") as "(Hb1 & Hcond & HL & HR)".
      simpl. iDestruct "Hc_close" as "[_ Hc_close]".
      iPoseProof ("Hc_close" with "Hb1") as "Hb".
      iFrame "HL HR".
      iDestruct "Hcond" as "#Hcond".
      iMod ("Hcl" with "[] [Hb]") as "Hb".
      { done. }
      { iApply "Hb". iPoseProof (typed_place_cond_syn_type_eq with "Hcond") as "<-". done. }
      iFrame "Hb".
      iApply (typed_place_cond_struct_lift with "[] []").
      + iApply (struct_lift_place_cond_homo with "Houtl Hcond"); [done | lia].
      + iPureIntro. clear. induction rts; simpl; first done.
        constructor; first apply place_access_rt_rel_refl. done.
  Qed.
  Definition typed_place_struct_shared_inst := [instance @typed_place_struct_shared].
  Global Existing Instance typed_place_struct_shared_inst | 30.

  (* TODO prove_place_cond *)
End place.


(* Need this for unification to figure out how to apply typed_place lemmas -- if the plist simplifies, unification will be stuck *)
Global Arguments plist : simpl never.
