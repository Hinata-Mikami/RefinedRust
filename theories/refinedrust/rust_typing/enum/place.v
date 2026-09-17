From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype programs.
From refinedrust.enum Require Import def subltype unfold.
From refinedrust Require Import options.


Section rules.
  Context `{!typeGS Σ}.

  Lemma enum_place_cond_nonuniq {rt} (en : enum rt)
      (variant1 variant2 : option enum_ltype_variant) b :
    UpdWeak ⪯ₚ b -∗
    typed_place_cond b (EnumLtype en variant1) (EnumLtype en variant2).
  Proof.
    iIntros "Hincl".
    destruct b; simpl in *; rewrite /typed_place_cond /=.
    - rewrite !ltype_st_enum. done.
    - rewrite !ltype_st_enum. done.
    - rewrite !ltype_st_enum. done.
    - iDestruct "Hincl" as "[]".
  Qed.

  Lemma enum_place_cond_uniq_none {rt rte} (en : enum rt) tag
      (sem : enum_tag_sem rt) (Heq : sem.(enum_tag_sem_rt) = rte)
      (lt1 lt2 : ltype rte) κs :
    enum_tag_ty_inj en tag = Some sem →
    typed_place_cond (UpdUniq κs) lt1 lt2 -∗
    typed_place_cond (UpdUniq κs)
      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt1 None)))
      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt2 None))).
  Proof.
    destruct Heq. simpl. intros Hsem.
    iIntros "#Hcond".
    iPoseProof (typed_place_cond_uniq_core_eq with "Hcond") as "#Heq".
    iPoseProof (typed_place_cond_uniq_unblockable with "Hcond") as "#Hub".
    iDestruct "Hcond" as "(%Hst & _)".
    rewrite /typed_place_cond /= !ltype_st_enum. iR. iExists eq_refl. cbn.
    iSplitR.
    - iIntros (b r). rewrite !ltype_core_enum /=.
      iApply enum_ltype_eq. iIntros (r').
      destruct (decide (enum_tag en r' = Some tag)) as [Htag | Htag].
      + rewrite !interp_enum_ltype_variant_Some_match; try done.
        iSplit; first done. iSplit.
        { iPureIntro. intros _. pose proof (enum_tag_rt_eq en r' tag sem Htag Hsem) as Hrt.
          set (rv := eq_rect _ id (enum_r en r') _ (f_equal RT_rt (eq_sym Hrt))).
          split.
          - split; first done. eexists rv, (f_equal RT_rt (eq_sym Hrt)). split; last done.
            simpl. eexists (f_equal RT_rt (eq_sym Hrt)). done.
          - split; first done. eexists rv, (f_equal RT_rt (eq_sym Hrt)). split; last done.
            simpl. eexists (f_equal RT_rt (eq_sym Hrt)). done. }
        iSplit.
        { iPureIntro. rewrite !ltype_core_syn_type_eq. exact Hst. }
        iIntros (b' rv1 rv2) "%Hrfn1 %Hrfn2".
        have -> : rv1 = rv2 by eapply enum_ltype_variant_rfn_unique.
        cbn.
        iApply "Heq".
      + rewrite !interp_enum_ltype_variant_Some_mismatch; try done.
        iSplit; first done. iSplit.
        { iPureIntro. intros Hcompat. split;
            (split; first exact Hcompat; eexists (enum_r en r'), eq_refl; split; done). }
        iSplit; first done. iIntros (b' rv1 rv2) "%Hrfn1 %Hrfn2".
        have -> : rv1 = rv2 by eapply enum_ltype_variant_rfn_unique.
        iApply ltype_eq_refl.
    - iApply enum_ltype_imp_unblockable. done.
  Qed.

  Program Definition enum_tag_ty_inj' {rt} (en : enum rt) (r : rt) (tag : string) (Heq : enum_tag en r = Some tag) :
    sigT (λ e : enum_tag_sem rt, enum_tag_ty_inj en tag = Some e) :=
    (*match enum_tag_compat _ en r tag Heq with*)
    (*| existT vinj Heq' => existT (mk_enum_tag_sem (enum_rt en r) (enum_ty en r) vinj) Heq'*)
    (*end*)
    existT (mk_enum_tag_sem (enum_rt en r) (enum_ty en r)
      (match enum_tag_compat _ en r tag Heq with
      | existT vinj Heq' => vinj
      end))
      (match enum_tag_compat _ en r tag Heq with
      | existT vinj Heq' => Heq'
      end)
  .
  Next Obligation.
    simpl. intros. exact eq_refl.
  Defined.
  Definition enum_tag_rfn_inj {rt} (en : enum rt) (tag : string)
    (r_old : rt)
    (Heq : enum_tag en r_old = Some tag)
    : (enum_rt en r_old) → rt :=
    enum_tag_rt_inj (projT1 (enum_tag_ty_inj' en r_old tag Heq)).

  (*Definition enum_tag_rfn_inj' {rt} (en : enum rt) (tag : string)*)
    (*(r_old : rt)*)
    (*(Heq : enum_tag en r_old = Some tag)*)
    (*: (enum_tag_rt' en tag) → rt :=*)
    (*λ ri,*)
      (*enum_tag_rfn_inj en tag r_old Heq (rew <-[id] (enum_variant_rt_tag_rt_eq en r_old tag Heq) in ri).*)

  (*Definition placein_or_default {rt} (r : place_rfn rt) (def : rt) : rt :=*)
    (*match r with*)
    (*| PlaceIn r => r*)
    (*| _ => def*)
    (*end.*)

  Lemma typed_place_enum_data_field_owned {rt} E L f l (en : enum rt) (r : rt) bmin0 els tag'
      (variant : option enum_ltype_variant) P T :
    typed_place E L f l (EnumLtype en variant) (#r) bmin0 (Owned) (EnumDataPCtx els tag' :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜lctx_place_update_kind_incl E L UpdStrong bmin0⌝);
      return (let v := interp_enum_ltype_variant en variant r in
        ∀ rv, ⌜enum_ltype_variant_rfn en r v rv⌝ -∗
        typed_place E L f ((GetEnumDataLocSt l els)) v.(eltv_ltype) (PlaceIn rv) bmin0 (Owned ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            (* we cannot borrow the whole variant itself in Rust *)
            ∃ r', ⌜upd'.(pupd_rfn) = #r'⌝ ∗
            cont (mkPUpd _ bmin0
              _
              (EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag)
                upd'.(pupd_rt) upd'.(pupd_lt) (Some r'))))
              (* no update, as we are owned *)
               (#r)
              upd'.(pupd_R)
              UpdStrong
              opt_place_update_eq_refl
              opt_place_update_eq_refl)))
      )).
  Proof.
    iIntros "(%Hels & %Hstrong & Hp)".
    iIntros (Φ F ??) "#(LFT & LLCTX) #HE HL Hf Hl HΦ/=".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hstrong"; first apply Hstrong.
    iPoseProof (enum_ltype_acc_owned F with "Hl") as "(%el & %Halg & %Hly & #Hlb & Hb)"; first done.
    iApply fupd_wpe.
    iMod (fupd_mask_mono with "Hb") as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Hpayload & Hcl)"; first done.
    iDestruct "Hpayload" as "(%rv & %Hrfn_payload & Hpayload)".

    (*iApply (wpe_logical_step with "Hcl"); [done | solve_ndisj.. | ].*)
    rewrite -Hels.
    iApply (wp_enum_data _ _ _ _ el
      (interp_enum_ltype_variant en variant r).(eltv_tag) variant_ly with "Hlb"); [done | done | ].
    iApply physical_step_intro. iModIntro. iNext. iIntros (v Hv).
    iExists (GetEnumDataLocSt l (enum_els en)). iSplitR.
    { done. }
    iApply ("Hp" $! rv with "[] [//] [//] [$LFT $LLCTX] HE HL Hf [Hpayload]"); first done.
    { rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=. iExact "Hpayload". }
    iIntros (L' κs l2 bmin b2 rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" $! _ _ _ bmin with "Hli").
    iIntros (upd) "#Hincl Hl2 HR Hcond".
    iMod ("Hcont" with "Hincl Hl2 HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl2 & Hcond & #Hmin & HR & Hupd & HL & Hf & Hcont)".
    iDestruct "Hcont" as (re') "(%Hre' & Hcont)". subst. rewrite Hre'.
    iPoseProof (typed_place_cond_syn_type_compat with "Hcond") as "%Hst_compat".
    pose proof (Hst_compat _ Hst) as Hst_new.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "Hl2".
    iMod ("Hcl" $! _ upd'.(pupd_lt) (Some re') re' r with "[] [] [] Htag Hl2") as "Hl".
    { done. }
    { done. }
    { done. }
    iModIntro. iExists (mkPUpd _ bmin0 _
      (EnumLtype en (Some (mk_enum_ltype_variant
        (interp_enum_ltype_variant en variant r).(eltv_tag)
          upd'.(pupd_rt) upd'.(pupd_lt) (Some re')))) (#r)
      upd'.(pupd_R) UpdStrong opt_place_update_eq_refl opt_place_update_eq_refl).
    simpl. iFrame "Hl HR Hupd HL Hf Hcont".
    iSplitR.
     { simpl. iPureIntro. rewrite !ltype_st_enum //. }
    iFrame "Hstrong".
  Qed.
  Definition typed_place_enum_data_field_owned_inst := [instance @typed_place_enum_data_field_owned].
  Global Existing Instance typed_place_enum_data_field_owned_inst.

  Lemma typed_place_enum_data_field_shared {rt} E L f l (en : enum rt) (r : rt) bmin0 els tag'
      (variant : option enum_ltype_variant) κ P T :
    typed_place E L f l (EnumLtype en variant) (#r) bmin0 (Shared κ) (EnumDataPCtx els tag' :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜lctx_place_update_kind_incl E L UpdWeak bmin0⌝);
      return (let v := interp_enum_ltype_variant en variant r in
        ∀ rv, ⌜enum_ltype_variant_rfn en r v rv⌝ -∗
        typed_place E L f ((GetEnumDataLocSt l els)) v.(eltv_ltype) (#rv) bmin0 (Shared κ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            ∃ r', ⌜upd'.(pupd_rfn) = #r'⌝ ∗
            cont (mkPUpd _ bmin0
              _
              (EnumLtype en (Some (mk_enum_ltype_variant v.(eltv_tag)
                upd'.(pupd_rt) upd'.(pupd_lt) (Some r'))))
              (* no update, as we are shared *)
               (#r)
              upd'.(pupd_R)
              (*upd'.(pupd_performed)*)
              UpdWeak
              opt_place_update_eq_refl
              opt_place_update_eq_refl)))
       )).
  Proof.
    iIntros "(%Hels & %Hweak & Hp)".
    iIntros (Φ F ??) "#(LFT & LLCTX) #HE HL Hf Hl HΦ/=".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hweak"; first apply Hweak.
    iPoseProof (enum_ltype_acc_shared F with "Hl") as "(%el & %Halg & %Hly & #Hlb & Hb)"; first done.
    iApply fupd_wpe.
    iMod (fupd_mask_mono with "Hb") as "(%variant_ly & %Hcompat & %Hvariant & %Hst & #Htag & #Hpayload & Hcl)"; first done.
    iDestruct "Hpayload" as "(%rv & %Hrfn_payload & #Hpayload)".

    rewrite -Hels.
    iApply (wp_enum_data _ _ _ _ el
      (interp_enum_ltype_variant en variant r).(eltv_tag) variant_ly with "Hlb"); [done | done | ].
    iApply physical_step_intro. iModIntro. iNext. iIntros (v Hv).
    iExists (GetEnumDataLocSt l (enum_els en)). iSplitR.
    { done. }
    iApply ("Hp" $! rv with "[] [//] [//] [$LFT $LLCTX] HE HL Hf [Hpayload]"); first done.
    { rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=. iExact "Hpayload". }
    iIntros (L' κs l2 b2 bmin rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" with "Hli").
    iIntros (upd) "#Hincl Hl2 HR Hcond".
    iMod ("Hcont" with "Hincl Hl2 HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl2 & Hcond & #Hmin & HR & Hupd & HL & Hf & Hcont)".
    iDestruct "Hcont" as (re') "(%Hre' & Hcont)". subst. rewrite Hre'.
    iPoseProof (typed_place_cond_syn_type_compat with "Hcond") as "%Hst_compat".
    pose proof (Hst_compat _ Hst) as Hst_new.
    iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "Hl2".
    iMod ("Hcl" $! _ upd'.(pupd_lt) (Some re') re' r with "[] [] [] Htag Hl2") as "Hl".
    { done. }
    { done. }
    { done. }
    iModIntro. iExists (mkPUpd _ bmin0 _
      (EnumLtype en (Some (mk_enum_ltype_variant
        (interp_enum_ltype_variant en variant r).(eltv_tag)
          upd'.(pupd_rt) upd'.(pupd_lt) (Some re')))) (#r)
      upd'.(pupd_R) UpdWeak opt_place_update_eq_refl opt_place_update_eq_refl).
     simpl. iFrame "Hl HR Hupd HL Hf Hcont".
     iSplitR; last done.
     iApply enum_place_cond_nonuniq; done.
   Qed.
   Definition typed_place_enum_data_field_shared_inst := [instance @typed_place_enum_data_field_shared].
  Global Existing Instance typed_place_enum_data_field_shared_inst.

  (* Recurse with Owned payload ownership. Contract-preserving updates close
     under UpdUniq; strong updates temporarily move to an OpenedLtype. *)
  Lemma typed_place_enum_data_field_uniq_none {rt rte} E L f l
      (en : enum rt) (r : rt) bmin0 els tag (lte : ltype rte) κ γ P T :
    (⌜en.(enum_els) = els⌝ ∗
     ⌜enum_tag en r = Some tag⌝ ∗
     ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin0⌝ ∗
     ∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
     ∃ Heq : sem.(enum_tag_sem_rt) = rte,
     li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
       ∀ rv, ⌜enum_ltype_variant_rfn en r
         (mk_enum_ltype_variant tag rte lte None) rv⌝ -∗
       typed_place E L2 f (GetEnumDataLocSt l els) lte (#rv)
         (bmin0 ⊓ₚ RestrictStrong) Owned P
         (λ L' κs' l2 b2 bmin rti ltyi ri updcx,
          T L' κs' l2 b2 bmin rti ltyi ri
           (λ L3 upd cont, updcx L3 upd (λ upd',
             li_tactic (check_llctx_place_update_kind_incl_uniq_goal E L3 upd'.(pupd_performed) [κ]) (λ oeq,
               match oeq with
               | Some Heqb =>
                 let Hequ := opt_place_update_eq_use _ _ _ Heqb upd'.(pupd_eq_1) in
                 ∃ re', ⌜upd'.(pupd_rfn) = #re'⌝ ∗
                 cont (mkPUpd _ bmin0 rt
                   (EnumLtype en (Some (mk_enum_ltype_variant tag rte
                     (eq_rect _ ltype upd'.(pupd_lt) _ (eq_sym Hequ)) None)))
                   (#(sem.(enum_tag_rt_inj)
                     (eq_rect _ RT_rt (eq_rect _ RT_rt re' _ (eq_sym Hequ)) _ (eq_sym Heq))))
                   (upd'.(pupd_R) ∗ llft_elt_toks κs)
                   (UpdUniq [κ]) opt_place_update_eq_refl opt_place_update_eq_refl)
                | None =>
                  ⌜place_update_kind_allows_strong_updates bmin0⌝ ∗
                  ∃ re', ⌜upd'.(pupd_rfn) = #re'⌝ ∗
                  cont (mkPUpd _ bmin0 rt
                    (OpenedLtype
                      (EnumLtype en (Some (mk_enum_ltype_variant tag
                        upd'.(pupd_rt) upd'.(pupd_lt) (Some re'))))
                      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte None)))
                      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte None)))
                      (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs))
                    (#r) upd'.(pupd_R) UpdStrong I opt_place_update_eq_refl)
                end))))))
    ⊢ typed_place E L f l
      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lte None)))
      (#r) bmin0 (Uniq κ γ) (EnumDataPCtx els tag :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%Hels & %Htag & %Hincl0 & %sem & %Hsem & %Heq & %κs & %L' & %Hal & Hp)".
    destruct Heq. simpl.
    iIntros (Φ F ??) "#(LFT & LLCTX) #HE HL Hf Hl HΦ/=".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl0"; first apply Hincl0.
    iApply fupd_wpe.
    iMod (fupd_mask_subseteq lftE) as "HF"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcltok & HL)"; [done.. |].
    iMod "HF" as "_".
    iPoseProof (enum_ltype_acc_uniq_update F with "[$LFT $LLCTX] Htok Hcltok Hl")
      as "(%el & %Halg & %Hly & #Hlb & Hb)"; first done.
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iEval (rewrite interp_enum_ltype_variant_Some_match; last done) in "Hb".
    iDestruct "Hb" as "(%variant_ly & %Hcompat & %Hvariant & %Hst & Htagown & %rv & %Hrfn & Hpayload & Hcl)".
    rewrite -Hels.
    iApply (wpe_logical_step with "Hcl"); [done | solve_ndisj.. |].
    iApply (wp_enum_data _ _ _ _ el tag variant_ly with "Hlb"); [done | done |].
    iApply physical_step_intro. iModIntro. iNext. iIntros (v Hv) "Hcl".
    iExists (GetEnumDataLocSt l (enum_els en)). iSplitR; first done.
    iApply ("Hp" $! rv with "[] [//] [//] [$LFT $LLCTX] HE HL Hf [Hpayload]"); first done.
    { rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=. done. }
    iIntros (L2 κs' l2 b2 bmin rti ltyi ri updcx) "Hli Hcont".
    iApply ("HΦ" with "Hli").
    iIntros (upd) "#Hincl Hl2 HR Hcond".
    iMod ("Hcont" with "Hincl Hl2 HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl2 & Hcond & #Hmin & HR & Hupd & HL & Hf & Hcont)".
    unfold check_llctx_place_update_kind_incl_uniq_goal.
    iDestruct "Hcont" as (b Hb) "Hcont".
    destruct b as [Heqb |].
    - iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hinclupd"; first apply Hb.
      destruct upd' as [rt2 lt2 r2 R2 perf Heq1 Heq2]. simpl in *.
      generalize (opt_place_update_eq_use perf sem.(enum_tag_sem_rt) rt2 Heqb Heq1) as Hequ.
      intros <-. simpl.
      iDestruct "Hcont" as (re') "(%Hre & Hcont)". subst r2.
      iPoseProof (typed_place_cond_incl with "Hinclupd Hcond") as "#Hconduniq".
      iPoseProof (enum_place_cond_uniq_none en tag sem eq_refl lte lt2 [κ] Hsem with "Hconduniq") as "#Henumcond".
      iPoseProof (typed_place_cond_syn_type_compat with "Hcond") as "%Hstcompat".
      pose proof (Hstcompat _ Hst) as Hstnew.
      pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
      pose proof (enum_tag_inj_roundtrip en tag sem Hel re') as [Htagnew Hrtnew Hrnew].
      assert (enum_ltype_variant_rfn en (sem.(enum_tag_rt_inj) re')
        (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lt2 None) re') as Hrfnnew.
      { simpl. exists (f_equal RT_rt (eq_sym Hrtnew)).
        erewrite Hrnew. generalize Hrtnew. intros []. done. }
      assert (enum_ltype_variant_compat en (sem.(enum_tag_rt_inj) re')
        (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lt2 None)) as Hcompatnew.
      { split; first done. pose proof Hrfnnew as [He Hr]. exists re', He.
        split; first exact Hrfnnew. symmetry. exact Hr. }
      iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "Hl2".
      iDestruct "Hcl" as "[Hcl _]".
      iMod ("Hcl" $! (UpdUniq [κ]) _ lt2 None (sem.(enum_tag_rt_inj) re') with
        "[] [] [] [] [] [] Htagown Hl2 Henumcond") as "(Hl & Htoks & Hcondout)".
      { iApply place_update_kind_incl_refl. }
      { done. }
      { done. }
      { done. }
      { done. }
      { iPureIntro. intros r0. unfold interp_enum_ltype_variant; simpl.
        destruct (decide (enum_tag en r0 = Some tag)); done. }
      iModIntro. iExists (mkPUpd _ bmin0 rt
        (EnumLtype en (Some (mk_enum_ltype_variant tag _ lt2 None)))
        (#(sem.(enum_tag_rt_inj) re')) (R2 ∗ llft_elt_toks κs)
        (UpdUniq [κ]) opt_place_update_eq_refl opt_place_update_eq_refl).
      simpl. iFrame "Hl HR Htoks Hcondout Hupd HL Hf Hcont".
      done.
    - iDestruct "Hcont" as "(%Hstrong & %re' & %Hre & Hcont)".
      destruct upd' as [rt2 lt2 r2 R2 perf Heq1 Heq2]. simpl in *.
      subst r2.
      iPoseProof (typed_place_cond_syn_type_compat with "Hcond") as "%Hstcompat".
      pose proof (Hstcompat _ Hst) as Hstnew.
      assert (Hcompat_orig : ∀ r0,
        enum_ltype_variant_tag_compat en r0
          (interp_enum_ltype_variant en
            (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte None)) r0) →
        enum_ltype_variant_compat en r0
          (interp_enum_ltype_variant en
            (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt) lte None)) r0)).
      { intros r0 Htagcompat.
        destruct (decide (enum_tag en r0 = Some tag)) as [Htag0 | Htag0].
        - rewrite interp_enum_ltype_variant_Some_match; last done.
          pose proof (enum_tag_rt_eq en r0 tag sem Htag0 Hsem) as Hrt0.
          set (rv0 := eq_rect _ id (enum_r en r0) _ (f_equal RT_rt (eq_sym Hrt0))).
          split; first done. exists rv0, (f_equal RT_rt (eq_sym Hrt0)).
          split; last done. simpl. exists (f_equal RT_rt (eq_sym Hrt0)). done.
        - rewrite interp_enum_ltype_variant_Some_mismatch; last done.
          rewrite interp_enum_ltype_variant_Some_mismatch in Htagcompat; last done.
          split; first done. exists (enum_r en r0), eq_refl. split; done. }
      iEval (rewrite /GetEnumDataLocSt /use_enum_layout_alg' Halg /=) in "Hl2".
      iDestruct "Hcl" as "[_ Hcl]".
      iPoseProof ("Hcl" $! rt2 lt2 re' with "[] [] Htagown Hl2") as "Hl".
      { done. }
      { iPureIntro. exact Hcompat_orig. }
      iModIntro. iExists (mkPUpd _ bmin0 rt
        (OpenedLtype
          (EnumLtype en (Some (mk_enum_ltype_variant tag rt2 lt2 (Some re'))))
          (EnumLtype en (Some (mk_enum_ltype_variant tag _ lte None)))
          (EnumLtype en (Some (mk_enum_ltype_variant tag _ lte None)))
          (λ r1 r2, ⌜r1 = r2⌝)%I (λ _ _, llft_elt_toks κs))
        (#r) R2 UpdStrong I opt_place_update_eq_refl).
      simpl. iFrame "Hl HR Hupd HL Hf Hcont". iSplit.
      { rewrite /typed_place_cond /= !ltype_st_enum. done. }
      destruct bmin0; done.
  Qed.
  Definition typed_place_enum_data_field_uniq_none_inst := [instance @typed_place_enum_data_field_uniq_none].
  Global Existing Instance typed_place_enum_data_field_uniq_none_inst | 30.

  (* Select the canonical payload before applying the inherited-override rule. *)
  Lemma typed_place_enum_data_field_uniq {rt} E L f l (en : enum rt) r bmin0 els tag κ γ P T :
    (∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      typed_place E L f l
        (EnumLtype en (Some (mk_enum_ltype_variant tag sem.(enum_tag_sem_rt)
          (OfTy sem.(enum_tag_sem_ty)) None))) r bmin0 (Uniq κ γ)
        (EnumDataPCtx els tag :: P) T)
    ⊢ typed_place E L f l (EnumLtype en None) r bmin0 (Uniq κ γ)
        (EnumDataPCtx els tag :: P) T.
  Proof.
    iIntros "(%sem & %Hsem & Hp)".
    iApply typed_place_eqltype; last done.
    symmetry. eapply enum_ltype_some_none_full_eqltype with (Heq := eq_refl); first done.
    reflexivity.
  Qed.
  Definition typed_place_enum_data_field_uniq_inst := [instance @typed_place_enum_data_field_uniq].
  Global Existing Instance typed_place_enum_data_field_uniq_inst | 30.

  Lemma prove_place_cond_enum_uniq_none E L κs {rt rte} (en : enum rt) tag
      (lt1 lt2 : ltype rte) T :
    (∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ Heq : sem.(enum_tag_sem_rt) = rte,
      prove_place_cond E L (UpdUniq κs) lt1 lt2 (λ _,
        T (mkPUKRes (UpdUniq κs)
          opt_place_update_eq_refl opt_place_update_eq_refl)))
    ⊢ prove_place_cond E L (UpdUniq κs)
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt1 None)))
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt2 None))) T.
  Proof.
    iIntros "(%sem & %Hsem & %Heq & HT)" (F HF) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as
      "(HL & %upd & #Hincl & Hcond & %Hst & HT)".
    iPoseProof (typed_place_cond_incl with "Hincl Hcond") as "#Hconduniq".
    iPoseProof (enum_place_cond_uniq_none en tag sem Heq lt1 lt2 κs Hsem
      with "Hconduniq") as "#Henumcond".
    iModIntro. iFrame "HL HT Henumcond".
    iSplitR; first iApply place_update_kind_incl_refl.
    rewrite !ltype_st_enum. done.
  Qed.
  Definition prove_place_cond_enum_uniq_none_inst :=
    [instance @prove_place_cond_enum_uniq_none].
  Global Existing Instance prove_place_cond_enum_uniq_none_inst | 20.

  Lemma prove_place_cond_enum_none_l_uniq E L κs {rt rte} (en : enum rt)
      tag (lt2 : ltype rte) T :
    (∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ Heq : sem.(enum_tag_sem_rt) = rte,
      prove_place_cond E L (UpdUniq κs)
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte
          (OfTy (eq_rect _ type sem.(enum_tag_sem_ty) _ Heq)) None)))
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt2 None))) T)
    ⊢ prove_place_cond E L (UpdUniq κs) (EnumLtype en None)
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt2 None))) T.
  Proof.
    iIntros "(%sem & %Hsem & %Heq & HT)".
    iApply prove_place_cond_eqltype_l; last done.
    symmetry. eapply enum_ltype_some_none_full_eqltype with (Heq := Heq); first done.
    reflexivity.
  Qed.
  Definition prove_place_cond_enum_none_l_uniq_inst :=
    [instance @prove_place_cond_enum_none_l_uniq].
  Global Existing Instance prove_place_cond_enum_none_l_uniq_inst | 15.

  Lemma prove_place_cond_enum_none_r_uniq E L κs {rt rte} (en : enum rt)
      tag (lt1 : ltype rte) T :
    (∃ sem, ⌜enum_tag_ty_inj en tag = Some sem⌝ ∗
      ∃ Heq : sem.(enum_tag_sem_rt) = rte,
      prove_place_cond E L (UpdUniq κs)
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt1 None)))
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte
          (OfTy (eq_rect _ type sem.(enum_tag_sem_ty) _ Heq)) None))) T)
    ⊢ prove_place_cond E L (UpdUniq κs)
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt1 None)))
        (EnumLtype en None) T.
  Proof.
    iIntros "(%sem & %Hsem & %Heq & HT)".
    iApply prove_place_cond_eqltype_r; last done.
    symmetry. eapply enum_ltype_some_none_full_eqltype with (Heq := Heq); first done.
    reflexivity.
  Qed.
  Definition prove_place_cond_enum_none_r_uniq_inst :=
    [instance @prove_place_cond_enum_none_r_uniq].
  Global Existing Instance prove_place_cond_enum_none_r_uniq_inst | 15.

  Lemma prove_place_cond_enum_ofty_l_uniq E L κs {rt rte} (en : enum rt)
      tag (lt2 : ltype rte) T :
    prove_place_cond E L (UpdUniq κs) (EnumLtype en None)
      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt2 None))) T
    ⊢ prove_place_cond E L (UpdUniq κs) (OfTy (enum_t en))
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt2 None))) T.
  Proof.
    iApply prove_place_cond_eqltype_l.
    apply enum_t_unfold_full_eqltype.
  Qed.
  Definition prove_place_cond_enum_ofty_l_uniq_inst :=
    [instance @prove_place_cond_enum_ofty_l_uniq].
  Global Existing Instance prove_place_cond_enum_ofty_l_uniq_inst | 15.

  Lemma prove_place_cond_enum_ofty_r_uniq E L κs {rt rte} (en : enum rt)
      tag (lt1 : ltype rte) T :
    prove_place_cond E L (UpdUniq κs)
      (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt1 None)))
      (EnumLtype en None) T
    ⊢ prove_place_cond E L (UpdUniq κs)
        (EnumLtype en (Some (mk_enum_ltype_variant tag rte lt1 None)))
        (OfTy (enum_t en)) T.
  Proof.
    iApply prove_place_cond_eqltype_r.
    apply enum_t_unfold_full_eqltype.
  Qed.
  Definition prove_place_cond_enum_ofty_r_uniq_inst :=
    [instance @prove_place_cond_enum_ofty_r_uniq].
  Global Existing Instance prove_place_cond_enum_ofty_r_uniq_inst | 15.
End rules.
