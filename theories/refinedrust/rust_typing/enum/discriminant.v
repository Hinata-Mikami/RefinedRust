From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype programs.
From refinedrust.enum Require Import def subltype unfold.
From refinedrust Require Import options.

Section discriminant.
  Context `{!typeGS Σ}.

  Program Definition enum_discriminant_t {rt} (en : enum rt) : type rt := {|
    st_own π r v :=
      ∃ tag, ⌜en.(enum_tag) r = Some tag⌝ ∗
      v ◁ᵥ{π, MetaNone} (els_lookup_tag en.(enum_els) tag) @ int en.(enum_els).(els_tag_it);
    st_has_op_type ot := is_int_ot ot en.(enum_els).(els_tag_it);
    st_syn_type := IntSynType en.(enum_els).(els_tag_it);
  |}%I.
  Next Obligation.
    intros. apply populate. apply (enum_xt_inhabited en).
  Qed.
  Next Obligation.
    simpl. intros.
    iIntros "(%tag & %Htag & Hv)".
    iApply (ty_has_layout with "Hv").
  Qed.
  Next Obligation.
    simpl. intros rt en ot Hot.
    eapply (@ty_op_type_stable _ _ _ (int _) _).
    rewrite ty_has_op_type_unfold. done.
  Qed.
  Next Obligation.
    simpl. intros rt en ot Hot.
    destruct ot; done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. intros rt en ot st π r v Hot. iIntros "(%tag & %Htag & Hv)".
    iPoseProof (ty_decodable _ (int en.(enum_els).(els_tag_it)) ot st π _ v with "Hv") as (ov) "%Hdec"; [| ].
    { rewrite ty_has_op_type_unfold. exact Hot. }
    iExists ov. done.
  Qed.
  Next Obligation.
    simpl. intros rt en ot st π r v v' Hot Hsame. iIntros "(%tag & %Htag & Hv)".
    iExists tag. iSplit; first done.
    iApply (ty_decode_compat _ (int en.(enum_els).(els_tag_it)) ot st π _ v v' with "Hv"); [| done].
    rewrite ty_has_op_type_unfold. exact Hot.
  Qed.
  Next Obligation.
    intros ?? ly Hst.
    apply syn_type_has_layout_int_inv in Hst as ->.
    done.
  Qed.

  Definition typed_discriminant_end_cont_t : Type :=
    llctx → val → ∀ (rt : RT), type rt → rt → iProp Σ.
  Definition typed_discriminant_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt: RT} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (els : enum_layout_spec) (T : typed_discriminant_end_cont_t) :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      (* given ownership of the read location *)
      l ◁ₗ[π, b2] r @ lt ={F}=∗
      ∃ q v discr,
        ⌜GetEnumDiscriminantLocSt l els `has_layout_loc` els.(els_tag_it)⌝ ∗
        ⌜v `has_layout_val` els.(els_tag_it)⌝ ∗
        (GetEnumDiscriminantLocSt l els) ↦{q} v ∗
        ▷ v ◁ᵥ{π, MetaNone} discr @ (int els.(els_tag_it)) ∗
        (* prove the continuation after the client is done *)
        logical_step F (
          (* assuming that the client provides the ownership back... *)
          (GetEnumDiscriminantLocSt l els) ↦{q} v ={F}=∗
          ∃ (L' : llctx) (rt3 : RT) (ty3 : type rt3) (r3 : rt3),
            v ◁ᵥ{ π, MetaNone} r3 @ ty3 ∗
            llctx_interp L' ∗
            l ◁ₗ[π, b2] r @ lt ∗
            T L' v rt3 ty3 r3))%I.
  Class TypedDiscriminantEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (els : enum_layout_spec) : Type :=
    typed_discriminant_end_proof T : iProp_to_Prop (typed_discriminant_end π E L l lt r b2 els T).

  Local Lemma enum_ltype_refinement_back_owned {rt} π (en : enum rt) variant r l v :
    v = interp_enum_ltype_variant en variant r →
    enum_ltype_variant_tag_compat en r v →
    l ◁ₗ[π, Owned] #r @ EnumLtype en (Some v) -∗
    l ◁ₗ[π, Owned] #r @ EnumLtype en variant.
  Proof.
    intros -> Htag.
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & #Hlb & %r' & -> & Hb)".
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iExists r'. iSplitR; first done.
    iEval (rewrite /interp_enum_ltype_variant decide_True //) in "Hb".
    done.
  Qed.

  Local Lemma enum_ltype_refinement_back_shared {rt} π (en : enum rt) variant r l κ v :
    v = interp_enum_ltype_variant en variant r →
    enum_ltype_variant_tag_compat en r v →
    l ◁ₗ[π, Shared κ] #r @ EnumLtype en (Some v) -∗
    l ◁ₗ[π, Shared κ] #r @ EnumLtype en variant.
  Proof.
    intros -> Htag.
    rewrite !ltype_own_enum_unfold /enum_ltype_own.
    iIntros "(%el & %Halg & %Hly & #Hlb & %r' & -> & #Hb)".
    iExists el. do 2 (iSplitR; first done). iSplitR; first iFrame "Hlb".
    iExists r'. iSplitR; first done. iModIntro.
    iEval (rewrite /interp_enum_ltype_variant decide_True //) in "Hb".
    done.
  Qed.

  Lemma typed_discriminant_end_enum_ltype π E L l {rt} (en : enum rt)
      (variant : option enum_ltype_variant) r b2 els (T : typed_discriminant_end_cont_t) :
    typed_discriminant_end π E L l (EnumLtype en variant) (#r) b2 els T :-
    exhale (⌜en.(enum_els) = els⌝);
    exhale (⌜lctx_bor_kind_alive E L b2⌝);
    ∀ v,
    return (T L v rt  (enum_discriminant_t en) (r)).
  Proof.
    iIntros "(%Hels & %Hal & HT)" (F Hf1 Hf2 Hf3 Hf4) "#CTX #HE HL Hb".
    subst els.
    destruct b2 as [ | | ]; simpl.
    - iPoseProof (enum_ltype_acc_owned F with "Hb") as
        "(%el & %Halg & %Hly & #Hlb & >(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & Hpayload & Hclose))"; first done.
      iEval (rewrite /lty_of_ty_own) in "Htag".
      iDestruct "Htag" as "(%tag_ly & %Htag_st & %Htag_ly & #Htag_sc & #Htag_lb & %z & %Hz & Htag)".
      subst z.
      iMod (fupd_mask_mono with "Htag") as "(%v & Hl & Hv)"; first done.
      apply syn_type_has_layout_int_inv in Htag_st as ->.
      destruct (use_enum_layout_alg_inv _ _ Halg) as (variant_lys & Hel & _).
      pose proof (enum_layout_alg_has_variants _ _ _ _ _ Hel) as (Hel_tag & _).
      rewrite Hel_tag in Htag_ly |- *.
      iPoseProof (ty_has_layout with "Hv") as "(%tag_ly' & %Htag_st' & %Hvly)".
      apply syn_type_has_layout_int_inv in Htag_st' as ->.
      iPoseProof "Hv" as "#Hv'".
      iModIntro. iExists 1%Qp, v,
        (els_lookup_tag en.(enum_els) (interp_enum_ltype_variant en variant r).(eltv_tag)).
      rewrite /GetEnumDiscriminantLocSt.
      do 2 (iSplitR; first done). iFrame "Hl".
      iSplitR "Hclose Hpayload HL HT".
      { iNext. iFrame "Hv'". }
      iApply logical_step_intro.
      iIntros "Hl".
      iDestruct "Hpayload" as "(%rv & %Hrfn_payload & Hpayload)".
      iMod ("Hclose" $! _ _ (interp_enum_ltype_variant en variant r).(eltv_rfn) rv r with "[] [] [] [Hl] Hpayload") as "Hb".
      { done. }
      { done. }
      { done. }
      { rewrite /lty_of_ty_own. iExists (it_layout en.(enum_els).(els_tag_it)).
        iSplitR; first by iPureIntro; apply syn_type_has_layout_int.
        iSplitR; first done. iFrame "Htag_sc Htag_lb".
        iExists (els_lookup_tag en.(enum_els) (interp_enum_ltype_variant en variant r).(eltv_tag)).
        iSplitR; first done. iModIntro. iExists v. iFrame "Hl Hv'". }
      iModIntro. iExists L, rt, (enum_discriminant_t en), r.
      iSplitR "HL HT Hb".
      { rewrite /ty_own_val /=. iR.
        iExists (interp_enum_ltype_variant en variant r).(eltv_tag).
        iSplitR; first done. iFrame "Hv'". }
      iSpecialize ("HT" $! v). iFrame "HL HT".
      destruct (interp_enum_ltype_variant en variant r) eqn:Hev; simpl in *.
      iApply (enum_ltype_refinement_back_owned with "Hb").
      { symmetry. exact Hev. }
      exact Hcompat.
    - iPoseProof (enum_ltype_acc_shared F with "Hb") as
        "(%el & %Halg & %Hly & #Hlb & >(%variant_ly & %Hcompat & %Hvariant & %Hst & #Htag & #Hpayload & Hclose))"; first done.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q) "(Htok & HL & Htok_cl)"; [solve_ndisj | done | ].
      iPoseProof "Htag" as "#Htag_direct".
      iEval (rewrite -ltype_own_ofty_unfold) in "Htag".
      iPoseProof (ofty_ltype_acc_shared with "Htag") as
        "(%tag_ly0 & %Htag_alg & %Htag_ly0 & #Htag_lb & >#Htag_shr)"; first done.
      iMod (copy_shr_acc with "CTX Htag_shr Htok") as
        "(%tag_ly & >%Htag_st & >%Htag_loc & %q' & %v & >(Hl & #Hv) & Htag_cl)"; [solve_ndisj.. | ].
      apply syn_type_has_layout_int_inv in Htag_st as ->.
      iDestruct (ty_has_layout with "Hv") as "(%tag_ly' & %Htag_st' & %Hvly)".
      apply syn_type_has_layout_int_inv in Htag_st' as ->.
      destruct (use_enum_layout_alg_inv _ _ Halg) as (variant_lys & Hel & _).
      pose proof (enum_layout_alg_has_variants _ _ _ _ _ Hel) as (Hel_tag & _).
      rewrite Hel_tag in Htag_loc, Hvly |- *.
      iModIntro. iExists q', v,
        (els_lookup_tag en.(enum_els) (interp_enum_ltype_variant en variant r).(eltv_tag)).
      rewrite /GetEnumDiscriminantLocSt.
      do 2 (iSplitR; first done). iFrame "Hl".
      iSplitR "HL Htok_cl HL_cl Htag_cl Hclose HT".
      { iNext. iFrame "Hv". }
      iApply logical_step_intro. iIntros "Hl".
      iMod ("Htag_cl" with "[Hl]") as "Htok".
      { iNext. iFrame "Hl". }
      iMod ("Htok_cl" with "Htok HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iDestruct "Hpayload" as "(%rv & %Hrfn_payload & Hpayload)".
      iMod ("Hclose" $! _ _ (interp_enum_ltype_variant en variant r).(eltv_rfn) rv r with "[] [] [] Htag_direct Hpayload") as "Hb".
      { done. }
      { done. }
      { done. }
      iModIntro. iExists L, rt, (enum_discriminant_t en), r.
      iSplitR "HL Hb HT".
      { rewrite /ty_own_val /=. iR.
        iExists (interp_enum_ltype_variant en variant r).(eltv_tag).
        iSplitR; first done. iFrame "Hv". }
      iSpecialize ("HT" $! v). iFrame "HL HT".
      destruct (interp_enum_ltype_variant en variant r) eqn:Hev; simpl in *.
      iApply (enum_ltype_refinement_back_shared with "Hb").
      { symmetry. exact Hev. }
      exact Hcompat.
    - iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as (q) "(Htok & Htok_cl)"; [solve_ndisj | ].
      iPoseProof (enum_ltype_acc_uniq lftE with "CTX Htok Htok_cl Hb") as
        "(%el & %Halg & %Hly & #Hlb & >(%variant_ly & %Hcompat & %Hvariant & %Hst & Htag & (%rv & %Hrfn_payload & Hpayload & Hclose)))"; first done.
      destruct Hcompat as (Hcompat & _).
      iMod "HF_cl" as "_".
      iEval (rewrite /lty_of_ty_own) in "Htag".
      iDestruct "Htag" as "(%tag_ly & %Htag_st & %Htag_ly & #Htag_sc & #Htag_lb & %z & %Hz & Htag)".
      subst z.
      iMod (fupd_mask_mono with "Htag") as "(%v & Hl & Hv)"; first done.
      apply syn_type_has_layout_int_inv in Htag_st as ->.
      destruct (use_enum_layout_alg_inv _ _ Halg) as (variant_lys & Hel & _).
      pose proof (enum_layout_alg_has_variants _ _ _ _ _ Hel) as (Hel_tag & _).
      rewrite Hel_tag in Htag_ly |- *.
      iPoseProof (ty_has_layout with "Hv") as "(%tag_ly' & %Htag_st' & %Hvly)".
      apply syn_type_has_layout_int_inv in Htag_st' as ->.
      iPoseProof "Hv" as "#Hv'".
      iModIntro. iExists 1%Qp, v,
        (els_lookup_tag en.(enum_els) (interp_enum_ltype_variant en variant r).(eltv_tag)).
      rewrite /GetEnumDiscriminantLocSt.
      do 2 (iSplitR; first done). iFrame "Hl".
      iSplitR "Hclose Hpayload HL_cl HT".
      { iNext. iFrame "Hv'". }
      iApply (logical_step_mask_mono lftE); first done.
      iApply (logical_step_wand with "Hclose").
      iIntros "Hclose Hl".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod ("Hclose" with "[Hl] Hpayload") as "(Hb & HL)".
      { rewrite /lty_of_ty_own. iExists (it_layout en.(enum_els).(els_tag_it)).
        iSplitR; first by iPureIntro; apply syn_type_has_layout_int.
        iSplitR; first done. iFrame "Htag_sc Htag_lb".
        iExists (els_lookup_tag en.(enum_els) (interp_enum_ltype_variant en variant r).(eltv_tag)).
        iSplitR; first done. iModIntro. iExists v. iFrame "Hl Hv'". }
      iMod "HF_cl" as "_".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro. iExists L, rt, (enum_discriminant_t en), r.
      iSplitR "HL Hb HT".
      { rewrite /ty_own_val /=. iR.
        iExists (interp_enum_ltype_variant en variant r).(eltv_tag).
        iSplitR; first done. iFrame "Hv'". }
      iSpecialize ("HT" $! v). iFrame.
  Qed.
  Global Instance typed_discriminant_end_enum_ltype_inst π E L l {rt} (en : enum rt)
      (variant : option enum_ltype_variant) r b2 els:
    TypedDiscriminantEnd π E L l (EnumLtype en variant) (#r) b2 els :=
    λ T, i2p (typed_discriminant_end_enum_ltype π E L l en variant r b2 els T).

  Lemma typed_discriminant_end_enum π E L l {rt} (en : enum rt) r b2 els (T : typed_discriminant_end_cont_t) :
    typed_discriminant_end π E L l (◁ enum_t en) (#r) b2 els T :-
    return typed_discriminant_end π E L l (EnumLtype en None) (#r) b2 els T.
  Proof.
    iIntros "HT" (F Hf1 Hf2 Hf3 Hf4) "#CTX #HE HL Hl".
    iPoseProof (enum_t_unfold en b2 (#r)) as "#Heq".
    iDestruct "Heq" as "[Hto Hfrom]".
    iMod (ltype_incl_use with "Hto Hl") as "Hl"; first done.
    iMod ("HT" $! F with "[] [] [] [] CTX HE HL Hl") as
      "(%q & %v & %discr & %Hloc & %Hval & Hl & Hv & Hclose)"; [done.. | ].
    iModIntro. iExists q, v, discr. do 2 (iSplitR; first done). iFrame "Hl Hv".
    iApply (logical_step_wand with "Hclose").
    iIntros "Hclose Hl".
    iMod ("Hclose" with "Hl") as
      "(%L' & %rt3 & %ty3 & %r3 & Hv & HL & Hl & HT)".
    iMod (ltype_incl_use with "Hfrom Hl") as "Hl"; first done.
    iModIntro. iExists L', rt3, ty3, r3. iFrame.
  Qed.
  Global Instance typed_discriminant_end_enum_inst π E L l {rt} (en : enum rt) r b2 els:
    TypedDiscriminantEnd π E L l (◁ enum_t en)%I (#r) b2 els :=
    λ T, i2p (typed_discriminant_end_enum π E L l en r b2 els T).

  Lemma type_discriminant E L f e els T' (T : typed_val_expr_cont_t) :
    IntoPlaceCtx E f e T' →
    (** Decompose the expression *)
    T' L (λ L' K l,
      (** Find the type assignment *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      ⌜π = f.1⌝ ∗
      (** Check the place access *)
      typed_place E L' f l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto _ _),
        (** Stratify *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (** Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (** Finish reading *)
        typed_discriminant_end π E L2 l2 lt3 ri3 b2 els (λ L3 v rt3 ty3 r3,
        typed_place_finish π E L3 updcx upd (R ∗ llft_elt_toks κs) l b lt3 ri3 (λ L4, T L4 v MetaNone _ (ty3) r3))
      )))))%I
    ⊢ typed_val_expr E L f (EnumDiscriminant els e)%E T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ) "#CTX #HE HL Hf HΦ".
    rewrite /EnumDiscriminant /Use. wpe_bind.
    iApply (HT' with "CTX HE HL Hf HT'").
    iIntros (L' K l) "HL Hf". iDestruct 1 as ([rt ([[lt r] π] & ?)]) "(Hl & -> & HP)".
    iApply ("HP" $! _ ⊤ with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L1 κs l2 bmin b2 rti lt2 ri2 updcx) "Hl2 Hs HT HL Hf".
    iPoseProof ("HT" $! ⊤ with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply wpe_fupd.
    iMod "Hb" as "(%L2 & %R & %rt3 & %lt3 & %ri3 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" $! ⊤ with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & %Hst' & HT)".
    wpe_bind.
    iApply (wpe_logical_step with "Hl2"); [solve_ndisj.. | ].
    wpe_bind.
    iApply wp_skip. iApply physical_step_intro. iNext.
    iIntros "(Hl2 & HR)".
    iMod ("HT" $! ⊤ with "[//] [//] [//] [//] CTX HE HL Hl2") as "Hdisc".
    iDestruct "Hdisc" as (q v discr) "(%Hloc & %Hval & Hl2 & Hv & Hclose)".
    iEval (rewrite /ty_own_val /= int_own_val_unfold) in "Hv".
    iDestruct "Hv" as "#>(_ & %Hv)".
    have Hdecode : ∀ st, ∃ ov, decode_op_val v (IntOp (els_tag_it els)) st = Some ov.
    { intros st. simp decode_op_val. rewrite Hv. eauto. }
    rewrite /GetEnumDiscriminantLocSt in Hloc.
    iEval (rewrite /GetEnumDiscriminantLocSt) in "Hl2 Hclose".
    iPoseProof (heap_pointsto_loc_in_bounds with "Hl2") as "#Hlb".
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Haddr".
    iApply (wpe_logical_step with "Hclose"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl2") => //; try by eauto using val_to_of_loc.
    { intros. apply val_to_loc_decode. by apply val_to_loc_Some_l2v. }
    iApply physical_step_intro. iNext. iIntros (st ov) "%Hdecode' Hl2 Hclose".
    iMod ("Hclose" with "Hl2") as (L3 rt4 ty4 r4) "(Hv' & HL & Hl2 & HT)".

    set (upd_inner := typed_place_finish_upd upd lt3 ri3).
    iMod ("Hs" $! upd_inner with "[] Hl2 [] Hcond") as "Hs".
    { simpl. done. }
    { simpl. done. }
    iMod ("Hs" with "HL Hf HT") as (upd') "(Hl & Hcond' & ? & HR' & ? & HL & Hf & Hfin)".
    iPoseProof ("Hfin" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] [$] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    rewrite (encode_decode_id_int v ov (IntOp (els_tag_it els)) (els_tag_it els) discr st) => //.
    iModIntro. by iApply ("HΦ" with "HL Hf Hv' HT").
  Qed.

End discriminant.

Section subtype.
  Context `{!typeGS Σ}.

  Global Program Instance enum_discriminant_t_simplify_hyp {rt} (en : enum rt) v π r :
    SimplifyHyp (v ◁ᵥ{π, MetaNone} r @ enum_discriminant_t en) (Some 100%N) := {|
    simplify_hyp_Q := (∃ tag, ⌜enum_tag en r = Some tag⌝ ∗ v ◁ᵥ{π, MetaNone} els_lookup_tag (enum_els en) tag @ int (els_tag_it (enum_els en)))
  |}.
  Next Obligation.
    iIntros (?????) "Hv".
    iEval (rewrite /ty_own_val/=) in "Hv".
    iDestruct "Hv" as "(_ & %tag & %Htag & Hv)".
    by iFrame.
  Qed.

  Lemma type_incl_enum_discriminant_int {rt} (en : enum rt) r tag  :
    en.(enum_tag) r = Some tag →
    ⊢ type_incl r (els_lookup_tag (enum_els en) tag) (enum_discriminant_t en) (int (els_tag_it (enum_els en))).
  Proof.
    intros Htag.
    iApply type_incl_simple_type; simpl; last done.
    iIntros "!>" (??) "(%tag' & %Htag' & (_ & Hv))".
    assert (tag' = tag) as -> by congruence. done.
  Qed.

  Lemma weak_subtype_enum_discriminant_int E L {rt} (en : enum rt) r i it T :
    weak_subtype E L r i (enum_discriminant_t en) (int it) T :-
      ∃ tag,
      exhale (⌜en.(enum_tag) r = Some tag⌝);
      exhale (⌜i = els_lookup_tag en.(enum_els) tag⌝);
      exhale (⌜it = en.(enum_els).(els_tag_it)⌝);
      return T.
  Proof.
    iIntros "(%tag & %Htag & -> & -> & HT)".
    iIntros (??) "#CTX HE HL".
    iFrame.
    iR.
    by iApply type_incl_enum_discriminant_int.
  Qed.
  Definition weak_subtype_enum_discriminant_int_inst := [instance @weak_subtype_enum_discriminant_int].
  Global Existing Instance weak_subtype_enum_discriminant_int_inst.
End subtype.

Section ops.
  Context `{!typeGS Σ}.

  Lemma type_relop_discr_discr E L f {rt} (en : enum rt) it v1 v2 (x1 x2 : rt) op π (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ ∀ tag1 tag2,
    ⌜en.(enum_tag) x1 = Some tag1⌝ -∗
    ⌜en.(enum_tag) x2 = Some tag2⌝ -∗
    typed_bin_op E L f v1 (v1 ◁ᵥ{π, MetaNone} (els_lookup_tag en.(enum_els) tag1) @ int en.(enum_els).(els_tag_it))%I v2 (v2 ◁ᵥ{π, MetaNone} (els_lookup_tag en.(enum_els) tag2) @ int en.(enum_els).(els_tag_it)) op (IntOp it) (IntOp it) T) ⊢
    typed_bin_op E L f v1 (v1 ◁ᵥ{π, MetaNone} x1 @ enum_discriminant_t en) v2 (v2 ◁ᵥ{π, MetaNone} x2 @ enum_discriminant_t en) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "(-> & HT)".
    rewrite /ty_own_val/=.
    iIntros "(_ & %tag1 & % & Hv1) (_ & %tag2 & % & Hv2)".
    iApply ("HT" with "[//] [//] [$Hv1] [$Hv2]").
  Qed.
  Definition type_relop_discr_discr_inst := [instance @type_relop_discr_discr].
  Global Existing Instance type_relop_discr_discr_inst.
End ops.

Section switch.
  Context `{!typeGS Σ}.

  Inductive destruct_hint_switch_enum :=
  (* We did a case analysis *)
  | DestructHintSwitchEnumCase {rt} (r : rt) (n : string)
  (* The case was already known *)
  | DestructHintSwitchEnumKnown {rt} (r : rt) (n : string)
  .

  Lemma type_switch_enum E L f {rt} (en : enum rt) r (it : int_type) v m ss def fn R U ϝ :
    ⌜it = en.(enum_els).(els_tag_it)⌝ ∗
    case_destruct r (λ c b,
      ∃ tag, ⌜enum_tag en c = Some tag⌝ ∗
        li_trace (if b then DestructHintSwitchEnumCase c tag else DestructHintSwitchEnumKnown c tag) (
        li_tactic (compute_list_map_lookup_goal ((els_tag_int en.(enum_els))) tag) (λ idx,
        li_tactic (compute_map_lookup_goal m (default 0%Z idx) false) (λ o,
        match o with
        | Some mi =>
           ∃ s, ⌜ss !! mi = Some s⌝ ∗
           normalize_spatial_context E L True (λ L2, typed_stmt E L2 f s fn R U ϝ)
        | None =>
          normalize_spatial_context E L True (λ L2, typed_stmt E L2 f def fn R U ϝ)
        end))))
    ⊢ typed_switch E L f v (enum_discriminant_t en) r it m ss def fn R U ϝ.
  Proof.
    unfold li_trace.
    iIntros "HT".
    iIntros (??) "#CTX #HE HL Hit".
    rewrite /ty_own_val/=.
    iDestruct "Hit" as "(_ & %tag & %Htag & _ & Hown)".
    iPoseProof (int_own_val_to_eq with "Hown") as "%Hv".
    iDestruct "HT" as "(-> & Hc)".
    rewrite /compute_list_map_lookup_goal/compute_map_lookup_goal.
    iDestruct "Hc" as "(%b & %tag' & %Htag' & %idx & %Hidx & %res & <- & Ha)".
    rewrite lookup_iml_list_to_map_eq in Hidx; first last.
    { rewrite els_tag_int_agree. apply els_variants_nodup. }
    subst idx.
    assert (tag' = tag) as -> by congruence.
    iExists _. iFrame "HL". iR. iModIntro.
    unfold els_lookup_tag. case_match.
    - iDestruct "Ha" as "(%s & % & HT)".
      iExists _. iR.
      iIntros (Φ Φunwind) "_ _ HL Hf Hpost".
      iMod ("HT" with "[] CTX HE HL [//]") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "CTX HE HL Hf Hpost").
    - iIntros (Φ Φunwind) "_ _ HL Hf Hpost".
      iMod ("Ha" with "[] CTX HE HL [//]") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "CTX HE HL Hf Hpost").
  Qed.
  Definition type_switch_enum_inst := [instance @type_switch_enum].
  Global Existing Instance type_switch_enum_inst.
End switch.
