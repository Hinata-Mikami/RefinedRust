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
  Local Lemma struct_lift_place_cond {rts} (lts : hlist ltype rts) i (lto : ltype (lnth (unit : RT) rts i)) rto' (lto' : ltype rto') bmin0 :
    hnth (UninitLtype UnitSynType) lts i = lto →
    i < length rts →
    ([∗ list] lt ∈ hzipl _ lts,
      place_kind_outlives_unblock_lt bmin0 (projT2 lt)) -∗
    typed_place_cond bmin0 lto lto' -∗
    [∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl _ (hlist_insert rts lts i _ lto'),
      typed_place_cond bmin0 (projT2 ty1) (projT2 ty2).
  Proof.
    iIntros (Hlto ?) "#Houtl #Hcond".
    iApply big_sepL2_intro. { rewrite !length_hzipl length_insert; done. }
    iIntros "!>" (k [rt1 lt1] [rt2 lt2] Hlook1 Hlook2).
    revert Hlook1 Hlook2.
    rewrite hzipl_hlist_insert.
    destruct (decide (k = i)) as [-> | Hneq]; simpl.
    - rewrite list_lookup_insert_eq; first last.
      { rewrite length_hzipl. done. }
      erewrite (hzipl_lookup_hnth _ _ _ _ (UninitLtype UnitSynType)), Hlto; last done.
      intros [= <- Heq1].
      apply existT_inj in Heq1 as <-.
      intros [= <- Heq1].
      apply existT_inj in Heq1 as <-.
      done.
    - rewrite list_lookup_insert_ne; last done.
      intros Hlook. rewrite Hlook. intros [= <- Heq1].
      apply existT_inj in Heq1 as <-.
      iApply typed_place_cond_refl.
      iPoseProof (big_sepL_lookup _ _ k with "Houtl") as "Ha"; first done.
      done.
  Qed.


  Local Lemma struct_lift_place_cond_homo {rts} (lts : hlist ltype rts) i (lto lto' : ltype (lnth (unit : RT) rts i)) bmin0 :
    hnth (UninitLtype UnitSynType) lts i = lto →
    i < length rts →
    ([∗ list] lt ∈ hzipl _ lts,
      place_kind_outlives_unblock_lt bmin0 (projT2 lt)) -∗
    typed_place_cond bmin0 lto lto' -∗
    [∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts (hlist_insert_id (unit : RT) rts lts i lto'),
      typed_place_cond bmin0 (projT2 ty1) (projT2 ty2).
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
    iApply (big_sepL_lookup _ _ k with "Houtl").
    rewrite list_lookup_insert_ne; last done. done.
  Qed.

  Lemma struct_opt_place_update_eq_lift {rts} i rt2 b :
    opt_place_update_eq b (lnth (unit : RT) rts i) rt2 →
    opt_place_update_eq b (plist place_rfnRT rts) (plist place_rfnRT (<[i := rt2]> rts)).
  Proof.
    unfold opt_place_update_eq. destruct b; simpl.
    - intros; exact I.
    - intros <-. rewrite list_insert_lnth//.
    - intros <-. rewrite list_insert_lnth//.
  Defined.

  (* TODO: sidecondition here is a bit tricky now.
     if another component is already blocked and we now make an UpdUniq [κ] change at a shorter lifetime, we get a problem.
     we should perform update at least at Uniq (blocked lfts).
     or we find a solution to not have this sidecondition :)

     I think upd' ⊔ Uniq (blocked_lfts) is a pretty reasonable thing though.
     We'll need a sidecondition to ensure that this is included in bmin.


     But let's think whether I can make this a bit more modular.
     We shouldn't need to do this weird stuff with including the blocked lifetimes.

     Internally, the pinned borrow has a view shift that takes the struct components and returns it to the original ownership.
     How about I make the shape of this viewshift more explicit?


     NOTE: for now, let's not try to change this up too much. This should be on my list to do, but it doesn't need to happen now.
   *)


  Local Lemma struct_incl_blocked_lfts_unblock {rts} (lts : hlist ltype rts) b :
    UpdUniq (mjoin (@ltype_blocked_lfts Σ typeGS0 +c<$> lts)) ⪯ₚ b -∗
    [∗ list] lt ∈ hzipl rts lts, place_kind_outlives_unblock_lt b (projT2 lt).
  Proof.
    iIntros "#Hincl".
    iApply big_sepL_intro. iModIntro. iIntros (k [? lt] Hlook).
    simpl. unfold place_kind_outlives_unblock_lt.
    iApply place_update_kind_outlives_incl; first done.
    simpl.
    iApply lft_list_incl_subset.
    apply list_subseteq_mjoin.
    rewrite hcmap_hzipl_fmap.
    apply list_elem_of_fmap.
    eexists; split; first last.
    { apply list_elem_of_lookup. eauto. }
    done.
  Qed.

  Lemma typed_place_struct_owned {rts} (lts : hlist ltype rts) π E L (r : plist place_rfnRT rts) sls f wl bmin0 P l
    (T : place_cont_t (plist place_rfnRT rts) bmin0) :
    ( (* sidecondition for other components *)
      ⌜lctx_place_update_kind_outlives E L bmin0 (mjoin ((@ltype_blocked_lfts  _ _) +c<$> lts))⌝ ∗
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : RT) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L (l atst{sls}ₗ f) lto ro bmin0 (Owned false) P
        (λ L' κs l1 b2 bmin rti ltyi ri updcx,
          T L' κs l1 b2 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
              (plist place_rfnRT (<[i := upd'.(pupd_rt)]> rts))
              (StructLtype (hlist_insert rts lts i _ upd'.(pupd_lt)) sls)
              (#(plist_insert rts r i _ upd'.(pupd_rfn)))
              upd'.(pupd_R)
              (upd'.(pupd_performed) ⊔ₚₖ UpdUniq (mjoin ((@ltype_blocked_lfts  _ _) +c<$> lts)))
              (opt_place_update_eq_lift_join _ _ $ struct_opt_place_update_eq_lift i upd'.(pupd_rt) _ upd'.(pupd_eq_1))
              (struct_opt_place_update_eq_lift i upd'.(pupd_rt) _ upd'.(pupd_eq_2)))))
          )))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Owned wl) (GetMemberPCtx sls f :: P) T.
  Proof.
    iIntros "(%Houtl & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL Hl HΦ/=".
    iPoseProof (lctx_place_update_kind_outlives_use _ _ _ _ Houtl with "HE HL") as "#Houtl".
    iPoseProof (struct_ltype_acc_owned F with "Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
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
    iModIntro. iNext. iIntros "Hcred Hcl". iExists _. iSplitR; first done.
    iPoseProof (focus_struct_component with "Hb") as "(%Heq & %ly' & %Hst & Hb & Hc_close)".
    { done. }
    { eapply (hnth_pnth_hpzipl_lookup _ (unit : RT) (UninitLtype UnitSynType) (PlaceIn ()) _ r); [ | done..].
      eapply field_index_of_leq in Hfield'.
      erewrite struct_layout_spec_has_layout_fields_length in Hfield'; last done. lia. }
    assert (l at{sl}ₗ f = l atst{sls}ₗ f) as Hleq.
    { rewrite /GetMemberLocSt /use_struct_layout_alg' Halg //. }
    rewrite Hleq.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [Hb]").
    { rewrite -Hlto -Hro. done. }
    iModIntro. iIntros (L' κs l2 bmin b2 rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" $! _ _ _ bmin with "Hli").

    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hcont" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl2 & %Hsteq2 & Hcond & #Hmin & ? & ? & HL & Hcont)".

    iFrame. simpl.
    iDestruct "Hc_close" as "[Hc_close _]".
    iPoseProof ("Hc_close" with "Hl2 []") as "Ha".
    { rewrite -Hsteq2. done. }
    iMod ("Hcl" with "[] Ha") as "Hl".
    { rewrite length_insert//. }
    iFrame "∗ #".
    iR.
    iSplitL; first last.
    { iApply place_update_kind_incl_lub; done. }
    iApply struct_ltype_place_cond.
    iApply struct_lift_place_cond.
    { done. }
    { done. }
    { (* so now I need to show that I actually outlive the time when the lts become unblockable. *)
      iApply struct_incl_blocked_lfts_unblock.
      iApply place_update_kind_max_incl_r. }
    { iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_l. }
  Qed.
  Definition typed_place_struct_owned_inst := [instance @typed_place_struct_owned].
  Global Existing Instance typed_place_struct_owned_inst | 30.

  Import EqNotations.

  Lemma typed_place_struct_uniq {rts} (lts : hlist ltype rts) π E L (r : plist place_rfnRT rts) sls f κ γ bmin0 P l
    (T : place_cont_t (plist place_rfnRT rts) bmin0) :
    ((* sidecondition for other components: the blocked lifetimes need to be included in the lifetime of the mutable reference *)
    ⌜lctx_place_update_kind_outlives E L (UpdUniq [κ]) (mjoin ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin0⌝ ∗
    (* get lifetime token *)
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : RT) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L2 (l atst{sls}ₗ f) lto ro bmin0 (Owned false) P
        (λ L' κs' l1 b2 bmin rti ltyi ri updcx,
          T L' (κs') l1 b2 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            li_tactic (check_llctx_place_update_kind_incl_uniq_goal E L2 upd'.(pupd_performed) [κ]) (λ oeq,
              match oeq with
              | Some Heq =>
                (* preserve type *)
                 cont (mkPUpd _ bmin0
                  (plist place_rfnRT rts)
                  (StructLtype (hlist_insert_id (unit : RT) rts lts i (rew <-[ltype] (opt_place_update_eq_use _ _ _ Heq upd'.(pupd_eq_1)) in upd'.(pupd_lt))) sls)
                  (#(plist_insert_id (unit : RT)  rts r i (rew <- (opt_place_update_eq_use _ _ _ Heq upd'.(pupd_eq_1)) in upd'.(pupd_rfn))))
                  (upd'.(pupd_R) ∗ llft_elt_toks κs)
                  (UpdUniq [κ])
                  opt_place_update_eq_refl
                  opt_place_update_eq_refl
                  )
              | None =>
                (* open *)
                ⌜bmin0 = UpdStrong⌝ ∗
                cont (mkPUpd _ bmin0
                  (plist place_rfnRT (<[i := upd'.(pupd_rt)]> rts))
                  (OpenedLtype (StructLtype (hlist_insert rts lts i _ upd'.(pupd_lt)) sls) (StructLtype lts sls) (StructLtype lts sls) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
                  (#(plist_insert rts r i _ upd'.(pupd_rfn)))
                  upd'.(pupd_R)
                  UpdStrong
                  I
                  (struct_opt_place_update_eq_lift i upd'.(pupd_rt) _ upd'.(pupd_eq_2)))
              end))
          )))))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Uniq κ γ) (GetMemberPCtx sls f :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%Houtl & %Hincl0 & %κs & %L' &  %Hal & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL Hl HΦ/=".

    iPoseProof (lctx_place_update_kind_outlives_use _ _ _ _ Houtl with "HE HL") as "#Houtl".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl0"; first apply Hincl0.
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
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [Hb]").
    { rewrite -Hlto -Hro. done. }
    iModIntro. iIntros (L2 κs' l2 b2 bmin rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" $! _ _ _ _ bmin with "Hli").

    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hcont" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl2 & %Hsteq2 & Hcond & #Hmin & ? & ? & HL & Hcont)".
    unfold check_llctx_place_update_kind_incl_uniq_goal.
    iDestruct "Hcont" as (b Hb) "Hcont".
    destruct b as [Heqb | ]; simpl in *.
    - (* weak *)
      iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hinclupd"; first apply Hb.
      iFrame. simpl.
      iDestruct "Hc_close" as "[_ Hc_close]".
      destruct upd' as [rt2 ??? perf Heq1 Heq2]. simpl in *.
      generalize (opt_place_update_eq_use perf (lnth unitRT rts i) rt2 Heqb Heq1) as Heqa.
      intros <-. simpl.
      iPoseProof ("Hc_close" with "Hl2 []") as "Ha".
      { rewrite -Hsteq2. done. }
      iDestruct "Hcl" as "[Hcl _]".
      iMod ("Hcl" $! (UpdUniq [κ]) with "[] Ha [Hcond]") as "(Hl & ? & ?)".
      { iApply place_update_kind_incl_refl. }
      { iApply struct_lift_place_cond_homo; [done.. | |  ].
        - iApply struct_incl_blocked_lfts_unblock. done.
        - iApply typed_place_cond_incl; done. }
      iFrame "∗ #".
      done.
    - (* strong *)
      iFrame. simpl.
      iDestruct "Hcont" as "(-> & Hcont)".
      iDestruct "Hc_close" as "[Hc_close _]".
      iPoseProof ("Hc_close" with "Hl2 []") as "Ha".
      { rewrite -Hsteq2. done. }
      iDestruct "Hcl" as "[_ Hcl]".
      iPoseProof ("Hcl" with "[] Ha") as "Hl".
      { rewrite length_insert//. }
      iFrame "∗ #". simpl. iFrame.
      done.
  Qed.
  Definition typed_place_struct_uniq_inst := [instance @typed_place_struct_uniq].
  Global Existing Instance typed_place_struct_uniq_inst | 30.

  Lemma typed_place_struct_shared {rts} (lts : hlist ltype rts) π E L (r : plistRT rts) sls f κ bmin0 P l
    (T : place_cont_t (plistRT rts) bmin0) :
    ((* sidecondition for other components *)
    ⌜lctx_place_update_kind_outlives E L bmin0 (mjoin ((λ _, ltype_blocked_lfts) +c<$> lts))⌝ ∗
    (* recursively check place *)
    (∃ i, ⌜sls_field_index_of sls.(sls_fields) f = Some i⌝ ∗
     ∃ lto (ro : place_rfn (lnth (unit : RT) rts i)),
      ⌜hnth (UninitLtype UnitSynType) lts i = lto⌝ ∗
      ⌜pnth (#tt) r i = ro⌝ ∗
      typed_place π E L (l atst{sls}ₗ f) lto ro bmin0 (Shared κ) P
        (λ L' κs l1 b2 bmin rti ltyi ri updcx,
          T L' κs l1 b2 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            (* sidecondition for other components *)
            cont (mkPUpd _ bmin0
              (plist place_rfnRT (<[i := upd'.(pupd_rt)]> rts))
              (StructLtype (hlist_insert rts lts i _ upd'.(pupd_lt)) sls)
              (#(plist_insert rts r i _ upd'.(pupd_rfn)))
              upd'.(pupd_R)
              (upd'.(pupd_performed) ⊔ₚₖ UpdUniq (mjoin ((@ltype_blocked_lfts  _ _) +c<$> lts)))
              (opt_place_update_eq_lift_join _ _ $ struct_opt_place_update_eq_lift i upd'.(pupd_rt) _ upd'.(pupd_eq_1))
              (struct_opt_place_update_eq_lift i upd'.(pupd_rt) _ upd'.(pupd_eq_2)))))

          )))
    ⊢ typed_place π E L l (StructLtype lts sls) (#r) bmin0 (Shared κ) (GetMemberPCtx sls f :: P) T.
  Proof.
    iIntros "(%Houtl & %i & %Hfield & %lto & %ro & %Hlto & %Hro & Hp)".
    iIntros (Φ F ??) "#(LFT & TIME & LLCTX) #HE HL Hl HΦ/=".
    iPoseProof (struct_ltype_acc_shared F with "Hl") as "(%sl & %Halg & %Hly & %Hmem & #Hlb & Hb)"; first done.
    iApply fupd_wp.
    iMod (fupd_mask_mono with "Hb") as "(Hb & Hcl)"; first done.
    iPoseProof (lctx_place_update_kind_outlives_use _ _ _ _ Houtl with "HE HL") as "#Houtl".

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
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL [Hb]").
    { rewrite -Hlto -Hro. done. }
    iIntros (L' κs l2 b2 bmin rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" with "Hli").

    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hcont" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl2 & %Hsteq2 & Hcond & #Hmin & ? & ? & HL &  Hcont)".
    iFrame. simpl.
    iDestruct "Hc_close" as "[Hc_close _]".
    iPoseProof ("Hc_close" with "Hl2 []") as "Ha".
    { rewrite -Hsteq2. done. }
    iMod ("Hcl" with "[] Ha") as "Hl".
    { rewrite length_insert//. }
    iFrame "∗ #".
    iR.
    iSplitL; first last.
    { iApply place_update_kind_incl_lub; done. }
    iApply struct_ltype_place_cond.
    iApply struct_lift_place_cond.
    { done. }
    { done. }
    { (* so now I need to show that I actually outlive the time when the lts become unblockable. *)
      iApply struct_incl_blocked_lfts_unblock.
      iApply place_update_kind_max_incl_r. }
    { iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_l. }
  Qed.
  Definition typed_place_struct_shared_inst := [instance @typed_place_struct_shared].
  Global Existing Instance typed_place_struct_shared_inst | 30.

  (* TODO prove_place_cond *)
End place.


(* Need this for unification to figure out how to apply typed_place lemmas -- if the plist simplifies, unification will be stuck *)
Global Arguments plist : simpl never.
