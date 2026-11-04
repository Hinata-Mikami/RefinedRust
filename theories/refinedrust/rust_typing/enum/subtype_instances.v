From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype.
From refinedrust.enum Require Import def subtype subltype unfold.
From refinedrust Require Import programs.
From refinedrust Require Import options.


Section subtype.
  Context `{!typeGS Σ}.
  Import EqNotations.

  (* Infer the payload first, then reconstruct a protected outer refinement. *)
  Lemma owned_subtype_enum_inj π E L pers {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) r1 r2 tag
      `{Htag1 : !TCDone (enum_tag en1 r1 = Some tag)}
      `{!IsConcreteEnumTag tag}
      T :
    (⌜fast_syntype_eq_hint (enum_els en1 = enum_els en2)⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 tag = Some sem⌝ ∗
    ⌜fast_syntype_eq_hint (ty_syn_type (enum_ty en1 r1) MetaNone =
      ty_syn_type sem.(enum_tag_sem_ty) MetaNone)⌝ ∗
    ∃ rp, owned_subtype π E L pers (enum_r en1 r1) rp
      (enum_ty en1 r1) sem.(enum_tag_sem_ty)
      (λ L2, ⌜r2 = sem.(enum_tag_rt_inj) rp⌝ ∗ T L2))
    ⊢ owned_subtype π E L pers r1 r2 (enum_t en1) (enum_t en2) T.
  Proof.
    iIntros "(%Hels & %sem & %Hsem & %Hst & %rp & HT)"
      (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & Hincl & $ & -> & $)".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 tag sem Hel rp) as [Htag2 Heq Hr].
    pose proof (enum_tag_type_eq' en2 _ _ _ Htag2 Hsem) as Hty.
    destruct pers; simpl.
    - iDestruct "Hincl" as "#Hincl". iModIntro. iModIntro.
      iSplitR; last iSplitR.
      + iPureIntro. simpl. rewrite Hels. apply syn_type_size_eq_refl.
      + done.
      + iIntros (v). iApply (enum_t_own_val_mono _ true).
        rewrite /enum_t_incl_precond /=. iR.
        iSplitR. { iPureIntro. by rewrite Htag1 Htag2. }
        iSplitR.
        { rewrite -Hty. generalize (enum_tag_rt_eq en2 _ _ _ Htag2 Hsem).
          intros Heq'. destruct Heq'. done. }
        rewrite Hr -Hty.
        generalize (enum_tag_rt_eq en2 _ _ _ Htag2 Hsem) as Heq'.
        intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
        rewrite (UIP_refl _ _ Heq0). done.
    - iModIntro. iSplitR; last iSplitR.
      + iPureIntro. simpl. rewrite Hels. apply syn_type_size_eq_refl.
      + done.
      + iIntros (v). iApply (enum_t_own_val_mono _ false).
        rewrite /enum_t_incl_precond /=. iR.
        iSplitR. { iPureIntro. by rewrite Htag1 Htag2. }
        iSplitR.
        { rewrite -Hty. generalize (enum_tag_rt_eq en2 _ _ _ Htag2 Hsem).
          intros Heq'. destruct Heq'. done. }
        rewrite Hr -Hty.
        generalize (enum_tag_rt_eq en2 _ _ _ Htag2 Hsem) as Heq'.
        intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
        rewrite (UIP_refl _ _ Heq0). done.
  Qed.
  Definition owned_subtype_enum_inj_inst := [instance @owned_subtype_enum_inj].
  Global Existing Instance owned_subtype_enum_inj_inst | 9.

  Lemma owned_subtype_enum_mut π E L pers {rt}
      (en1 en2 : enum rt) r1 r2 `{!ContainsProtected r2} T :
    ⌜r1 = r2⌝ ∗ mut_subtype E L (enum_t en1) (enum_t en2) (T L)
    ⊢ owned_subtype π E L pers r1 r2 (enum_t en1) (enum_t en2) T.
  Proof.
    iIntros "Hsub". iApply owned_subtype_strong_subtype.
    iApply weak_subtype_strong_subtype.
    by iApply weak_subtype_default.
  Qed.
  Definition owned_subtype_enum_mut_inst := [instance @owned_subtype_enum_mut].
  Global Existing Instance owned_subtype_enum_mut_inst | 10.

  Lemma weak_subtype_enum_inj E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) r1 r2 tag
      `{Htag1 : !TCDone (enum_tag en1 r1 = Some tag)}
      `{!IsConcreteEnumTag tag}
      T :
    (⌜enum_els en1 = enum_els en2⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 tag = Some sem⌝ ∗
    ∃ rp, weak_subtype E L (enum_r en1 r1) rp
      (enum_ty en1 r1) sem.(enum_tag_sem_ty)
      (⌜r2 = sem.(enum_tag_rt_inj) rp⌝ ∗ T))
    ⊢ weak_subtype E L r1 r2 (enum_t en1) (enum_t en2) T.
  Proof.
    iIntros "(%Hels & %sem & %Hsem & %rp & HT)"
      (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    pose proof (enum_tag_ty_find_elem _ _ _ Hsem) as Hel.
    destruct (enum_tag_inj_roundtrip en2 tag sem Hel rp) as [Htag2 Heq Hr].
    pose proof (enum_tag_type_eq' en2 _ _ _ Htag2 Hsem) as Hty.
    iModIntro. iSplitR.
    { iPureIntro. intros m. simpl. by rewrite Hels. }
    iApply enum_t_type_incl. iR.
    iSplitR. { iPureIntro. by rewrite Htag1 Htag2. }
    iSplitR.
    - iPureIntro. intros m. rewrite Hst -Hty.
      generalize (enum_tag_rt_eq en2 _ _ _ Htag2 Hsem).
      intros Heq'. destruct Heq'. done.
    - rewrite Hr -Hty.
      generalize (enum_tag_rt_eq en2 _ _ _ Htag2 Hsem) as Heq'.
      intros Heq'. generalize Heq. destruct Heq'. intros Heq0.
      rewrite (UIP_refl _ _ Heq0). done.
  Qed.
  Definition weak_subtype_enum_inj_inst := [instance @weak_subtype_enum_inj].
  Global Existing Instance weak_subtype_enum_inj_inst | 9.

  Lemma weak_subtype_enum_mut E L {rt}
      (en1 en2 : enum rt) r1 r2 `{!ContainsProtected r2} T :
    ⌜r1 = r2⌝ ∗ mut_subtype E L (enum_t en1) (enum_t en2) T
    ⊢ weak_subtype E L r1 r2 (enum_t en1) (enum_t en2) T.
  Proof.
    iApply weak_subtype_default.
  Qed.
  Definition weak_subtype_enum_mut_inst := [instance @weak_subtype_enum_mut].
  Global Existing Instance weak_subtype_enum_mut_inst | 10.

  Lemma mut_subtype_enum E L {rt} (en1 en2 : enum rt) T :
    prove_full_enum_incl E L en1 en2 T
    ⊢ mut_subtype E L (enum_t en1) (enum_t en2) T.
  Proof. iIntros "(%Hincl & $)". iPureIntro. by apply enum_full_subtype. Qed.
  Definition mut_subtype_enum_inst := [instance @mut_subtype_enum].
  Global Existing Instance mut_subtype_enum_inst | 20.

  Lemma prove_full_enum_incl_structural E L {rt} (en1 en2 : enum rt)
      `{Hrt : !TCDone (enum_rt en1 = enum_rt en2)} T :
    (⌜enum_els en1 = enum_els en2⌝ ∗ ⌜enum_tag en1 = enum_tag en2⌝ ∗ ⌜∀ r, is_Some (enum_tag en1 r)⌝ ∗
     ⌜∀ r, rew [RT_rt] (f_equal (λ f, f r) Hrt) in enum_r en1 r = enum_r en2 r⌝ ∗
    mut_subtype_enum_tag_tys E L en1.(enum_tag_ty) en2.(enum_tag_ty) T)
    ⊢ prove_full_enum_incl E L en1 en2 T.
  Proof.
    iIntros "(%Hels & %Htag & %Htotal & %Hr & %Htys & $)".
    iPureIntro. by eapply (full_enum_incl_intro_tag_tys E L en1 en2
      (λ r, f_equal (λ f, f r) Hrt)).
  Qed.
  Definition prove_full_enum_incl_structural_inst := [instance @prove_full_enum_incl_structural].
  Global Existing Instance prove_full_enum_incl_structural_inst | 20.

  Lemma mut_subtype_enum_tag_tys_nil E L {rt} T :
    T ⊢ mut_subtype_enum_tag_tys E L (@nil (var_name * enum_tag_sem (rt))) [] T.
  Proof. iIntros "$". iPureIntro. constructor. Qed.
  Definition mut_subtype_enum_tag_tys_nil_inst := [instance @mut_subtype_enum_tag_tys_nil].
  Global Existing Instance mut_subtype_enum_tag_tys_nil_inst | 10.

  Lemma mut_subtype_enum_tag_tys_cons E L {rt} tag1 tag2 (sem_rt : RT)
      (ty1 ty2 : type sem_rt) (inj1 inj2 : sem_rt → rt) tys1 tys2 T :
    (⌜tag1 = tag2⌝ ∗
      mut_subtype E L ty1 ty2 (mut_subtype_enum_tag_tys E L tys1 tys2 T))
    ⊢ mut_subtype_enum_tag_tys E L
      ((tag1, mk_enum_tag_sem sem_rt ty1 inj1) :: tys1)
      ((tag2, mk_enum_tag_sem sem_rt ty2 inj2) :: tys2) T.
  Proof.
    iIntros "(-> & %Hhead & %Htail & $)". iPureIntro. constructor; last done.
    split; first done. by exists eq_refl.
  Qed.
  Definition mut_subtype_enum_tag_tys_cons_inst := [instance @mut_subtype_enum_tag_tys_cons].
  Global Existing Instance mut_subtype_enum_tag_tys_cons_inst | 20.

  Lemma prove_full_enum_incl_refl E L {rt} (en : enum rt) T :
    T ⊢ prove_full_enum_incl E L en en T.
  Proof. iIntros "$". iPureIntro. apply full_enum_incl_refl. Qed.
  Definition prove_full_enum_incl_refl_inst := [instance @prove_full_enum_incl_refl].
  Global Existing Instance prove_full_enum_incl_refl_inst | 5.
End subtype.

Section subltype.
  Context `{!typeGS Σ}.

  Lemma weak_subltype_enum_owned_in E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2' in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
    ⌜enum_ltype_variant_compat en2 r2' v2⌝ ∗
    ∃ rv1 rv2,
    ⌜enum_ltype_variant_rfn en1 r1 v1 rv1⌝ ∗
    ⌜enum_ltype_variant_rfn en2 r2' v2 rv2⌝ ∗
    weak_subltype E L Owned (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype) T)
    ⊢ weak_subltype E L Owned (#r1) r2
      (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(%r2' & -> & %Hels & %Htag & %Hcompat & %rv1 & %rv2 & %Hrfn1 & %Hrfn2 & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_owned_in;
      [exact Hels | exact Htag | exact Hcompat | exact Hst |].
    iIntros (rv1' rv2') "%Hrfn1' %Hrfn2'".
    have -> : rv1' = rv1 by eapply enum_ltype_variant_rfn_unique.
    have -> : rv2' = rv2 by eapply enum_ltype_variant_rfn_unique.
    done.
  Qed.
  Definition weak_subltype_enum_owned_in_inst := [instance @weak_subltype_enum_owned_in].
  Global Existing Instance weak_subltype_enum_owned_in_inst | 20.

  Lemma weak_subltype_enum_owned_some_none E L {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) tag (lt : ltype rte) re r1 r2
      `{Ht1 : !TCDone (enum_tag en1 r1 = Some tag)} T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜enum_tag en2 r2' = Some tag⌝ ∗
    weak_subltype E L Owned (#re) (#(enum_r en2 r2')) lt (◁ enum_ty en2 r2') T)
    ⊢ weak_subltype E L Owned (#r1) r2
      (EnumLtype en1 (Some (mk_enum_ltype_variant tag rte lt (Some re)))) (EnumLtype en2 None) T.
  Proof.
    iIntros "(%r2' & -> & %Hels & %Ht2 & HT)".
    iApply weak_subltype_enum_owned_in.
    iExists r2'. iSplitR; first done.
    rewrite interp_enum_ltype_variant_Some_match; last done.
    rewrite /interp_enum_ltype_variant /canonical_enum_ltype_variant /=.
    rewrite (enum_tag'_Some en2 r2' tag Ht2).
    iSplit; first done. iSplit; first done. iSplit.
    { iPureIntro. split; first done.
      exists (enum_r en2 r2'), eq_refl. split; done. }
    iExists re, (enum_r en2 r2'). iFrame. done.
  Qed.
  Definition weak_subltype_enum_owned_some_none_inst := [instance @weak_subltype_enum_owned_some_none].
  Global Existing Instance weak_subltype_enum_owned_some_none_inst | 10.

  (* Infer the payload first, then reconstruct a protected outer refinement. *)
  Lemma weak_subltype_enum_owned_inj E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 r2
      `{!ContainsProtected r2} T :
    (let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 v1.(eltv_tag) = Some sem⌝ ∗
    ∃ rv, ⌜enum_ltype_variant_rfn en1 r1 v1 rv⌝ ∗
    ∃ rp, weak_subltype E L Owned (#rv) (#rp)
      v1.(eltv_ltype) (OfTy sem.(enum_tag_sem_ty))
      (⌜r2 = #(sem.(enum_tag_rt_inj) rp)⌝ ∗ T))
    ⊢ weak_subltype E L Owned (#r1) r2
      (EnumLtype en1 variant1) (EnumLtype en2 None) T.
  Proof.
    iIntros "(%Hels & %sem & %Hsem & %rv & %Hrfn & %rp & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_owned_in_inj;
      [exact Hels | exact Hsem | exact Hst | exact Hrfn |].
    done.
  Qed.
  Definition weak_subltype_enum_owned_inj_inst := [instance @weak_subltype_enum_owned_inj].
  Global Existing Instance weak_subltype_enum_owned_inj_inst | 9.

  Lemma weak_subltype_enum_owned_inj_none E L {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 r2 tag
      (lt : ltype rte) `{!ContainsProtected r2} T :
    (let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = tag⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 tag = Some sem⌝ ∗
    ∃ (Heq : sem.(enum_tag_sem_rt) = rte),
    ∃ rv, ⌜enum_ltype_variant_rfn en1 r1 v1 rv⌝ ∗
    ∃ rp, weak_subltype E L Owned (#rv)
      (#(eq_rect _ RT_rt rp _ Heq)) v1.(eltv_ltype) lt
      (⌜r2 = #(sem.(enum_tag_rt_inj) rp)⌝ ∗ T))
    ⊢ weak_subltype E L Owned (#r1) r2
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt None))) T.
  Proof.
    iIntros "(%Hels & %Htag & %sem & %Hsem & %Heq & %rv & %Hrfn & %rp & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_owned_in_inj_none;
      [exact Hels | exact Htag | exact Hsem | exact Hst | exact Hrfn |].
    done.
  Qed.
  Definition weak_subltype_enum_owned_inj_none_inst := [instance @weak_subltype_enum_owned_inj_none].
  Global Existing Instance weak_subltype_enum_owned_inj_none_inst | 9.

  Lemma weak_subltype_enum_owned_inj_some E L {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 r2 tag
      (lt : ltype rte) (re : rte) `{!ContainsProtected r2} T :
    (let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = tag⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 tag = Some sem⌝ ∗
    ∃ (Heq : sem.(enum_tag_sem_rt) = rte),
    ∃ rv, ⌜enum_ltype_variant_rfn en1 r1 v1 rv⌝ ∗
    weak_subltype E L Owned (#rv) (#re) v1.(eltv_ltype) lt
      (⌜r2 = #(sem.(enum_tag_rt_inj) (eq_rect _ RT_rt re _ (eq_sym Heq)))⌝ ∗ T))
    ⊢ weak_subltype E L Owned (#r1) r2
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt (Some re)))) T.
  Proof.
    iIntros "(%Hels & %Htag & %sem & %Hsem & %Heq & %rv & %Hrfn & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_owned_in_inj_some;
      [exact Hels | exact Htag | exact Hsem | exact Hst | exact Hrfn |].
    done.
  Qed.
  Definition weak_subltype_enum_owned_inj_some_inst := [instance @weak_subltype_enum_owned_inj_some].
  Global Existing Instance weak_subltype_enum_owned_inj_some_inst | 9.

  (* Unknown outer refinements must be preserved, including ghost refinements.
     The payload conversion therefore has to hold uniformly. *)
  Lemma weak_subltype_enum_owned E L {rt} (en1 en2 : enum rt)
      variant1 variant2 r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜enum_els en1 = enum_els en2⌝ ∗
    (* TODO: have dedicated sidecond solver for this *)
    ⌜∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
       (enum_ltype_variant_tag_compat en1 r v1 →
         v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_compat en2 r v2) ∧
       ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) ∧
       ∀ rv1 rv2, enum_ltype_variant_rfn en1 r v1 rv1 →
         enum_ltype_variant_rfn en2 r v2 rv2 →
         subltype E L Owned (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype)⌝ ∗ T
    ⊢ weak_subltype E L Owned r1 r2 (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(-> & %Hels & %Hsub & HT)" (??) "#CTX #HE HL".
    iAssert (∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
       ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
       enum_ltype_variant_ltype_incl Owned en1 r v1 en2 r v2)%I as "#Hu".
    { iIntros (r). iSplit.
      - iPureIntro. exact (proj1 (proj2 (Hsub r))).
      - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
        iPoseProof (subltype_acc with "CTX HE HL") as "Hu".
        { exact (proj2 (proj2 (Hsub r)) rv1 rv2 Hrfn1 Hrfn2). }
        iDestruct "Hu" as "(_ & $)". }
    iFrame. iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_owned; first done.
    iIntros (r). destruct (Hsub r) as [Hcompat Hpayload]. iSplitR; first done.
    iApply "Hu".
  Qed.
  Definition weak_subltype_enum_owned_inst := [instance @weak_subltype_enum_owned].
  Global Existing Instance weak_subltype_enum_owned_inst | 22.

  Lemma weak_subltype_enum_owned_none E L {rt} (en1 en2 : enum rt) r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜full_enum_incl E L en1 en2⌝ ∗ T
    ⊢ weak_subltype E L Owned r1 r2 (EnumLtype en1 None) (EnumLtype en2 None) T.
  Proof.
    iIntros "(-> & %Hsub & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subtype_acc with "HE HL") as "(%Hst & #Hincl)";
      first by apply enum_full_subtype.
    iFrame. iModIntro. iSplitR. { simp_ltypes. iPureIntro. apply (Hst MetaNone). }
    iApply (ltype_incl_trans with "[]"); first iApply enum_t_unfold_2.
    iApply (ltype_incl_trans with "[Hincl]"); last iApply enum_t_unfold_1.
    iApply (type_ltype_incl_owned (enum_t en1) (enum_t en2) with "[] Hincl").
    iPureIntro. rewrite Hst. apply syn_type_compat_refl.
  Qed.
  Definition weak_subltype_enum_owned_none_inst := [instance @weak_subltype_enum_owned_none].
  Global Existing Instance weak_subltype_enum_owned_none_inst | 21.

  Lemma weak_subltype_enum_shared_in E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 κ T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2' in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
    ⌜enum_ltype_variant_compat en2 r2' v2⌝ ∗
    ⌜∀ rv, enum_ltype_variant_rfn en2 r2' v2 rv → is_xrfn rv → is_xrfn r2'⌝ ∗
    ∃ rv1 rv2,
    ⌜enum_ltype_variant_rfn en1 r1 v1 rv1⌝ ∗
    ⌜enum_ltype_variant_rfn en2 r2' v2 rv2⌝ ∗
    weak_subltype E L (Shared κ) (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype) T)
    ⊢ weak_subltype E L (Shared κ) (#r1) r2
      (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(%r2' & -> & %Hels & %Htag & %Hcompat & %Hcanonical & %rv1 & %rv2 & %Hrfn1 & %Hrfn2 & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_shared_in;
      [exact Hels | exact Htag | exact Hcompat | exact Hst | exact Hcanonical |].
    iIntros (rv1' rv2') "%Hrfn1' %Hrfn2'".
    have -> : rv1' = rv1 by eapply enum_ltype_variant_rfn_unique.
    have -> : rv2' = rv2 by eapply enum_ltype_variant_rfn_unique.
    done.
  Qed.
  Definition weak_subltype_enum_shared_in_inst := [instance @weak_subltype_enum_shared_in].
  Global Existing Instance weak_subltype_enum_shared_in_inst | 20.

  Lemma weak_subltype_enum_shared_some_none E L {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) tag (lt : ltype rte) re r1 r2 κ
      `{Ht1 : !TCDone (enum_tag en1 r1 = Some tag)} T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜enum_tag en2 r2' = Some tag⌝ ∗
    weak_subltype E L (Shared κ) (#re) (#(enum_r en2 r2')) lt (◁ enum_ty en2 r2') T)
    ⊢ weak_subltype E L (Shared κ) (#r1) r2
      (EnumLtype en1 (Some (mk_enum_ltype_variant tag rte lt (Some re)))) (EnumLtype en2 None) T.
  Proof.
    iIntros "(%r2' & -> & %Hels & %Ht2 & HT)".
    iApply weak_subltype_enum_shared_in.
    iExists r2'. iSplitR; first done.
    rewrite interp_enum_ltype_variant_Some_match; last done.
    rewrite /interp_enum_ltype_variant /canonical_enum_ltype_variant /=.
    rewrite (enum_tag'_Some en2 r2' tag Ht2).
    iSplit; first done. iSplit; first done. iSplit.
    { iPureIntro. split; first done.
      exists (enum_r en2 r2'), eq_refl. split; done. }
    iSplitR.
    { iPureIntro. intros rv -> Hxr. exact (proj2 (enum_r_is_xrfn en2 r2') Hxr). }
    iExists re, (enum_r en2 r2'). iFrame. done.
  Qed.
  Definition weak_subltype_enum_shared_some_none_inst := [instance @weak_subltype_enum_shared_some_none].
  Global Existing Instance weak_subltype_enum_shared_some_none_inst | 10.

  Lemma weak_subltype_enum_shared_inj E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 r2 κ
      `{!ContainsProtected r2} T :
    (let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 v1.(eltv_tag) = Some sem⌝ ∗
    ∃ rv, ⌜enum_ltype_variant_rfn en1 r1 v1 rv⌝ ∗
    ∃ rp, weak_subltype E L (Shared κ) (#rv) (#rp)
      v1.(eltv_ltype) (OfTy sem.(enum_tag_sem_ty))
      (⌜r2 = #(sem.(enum_tag_rt_inj) rp)⌝ ∗ T))
    ⊢ weak_subltype E L (Shared κ) (#r1) r2
      (EnumLtype en1 variant1) (EnumLtype en2 None) T.
  Proof.
    iIntros "(%Hels & %sem & %Hsem & %rv & %Hrfn & %rp & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_shared_in_inj;
      [exact Hels | exact Hsem | exact Hst | exact Hrfn |].
    done.
  Qed.
  Definition weak_subltype_enum_shared_inj_inst := [instance @weak_subltype_enum_shared_inj].
  Global Existing Instance weak_subltype_enum_shared_inj_inst | 9.

  Lemma weak_subltype_enum_shared_inj_none E L {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 r2 tag κ
      (lt : ltype rte) `{!ContainsProtected r2} T :
    (let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = tag⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 tag = Some sem⌝ ∗
    ∃ (Heq : sem.(enum_tag_sem_rt) = rte),
    ∃ rv, ⌜enum_ltype_variant_rfn en1 r1 v1 rv⌝ ∗
    ∃ rp, weak_subltype E L (Shared κ) (#rv)
      (#(eq_rect _ RT_rt rp _ Heq)) v1.(eltv_ltype) lt
      (⌜r2 = #(sem.(enum_tag_rt_inj) rp)⌝ ∗ T))
    ⊢ weak_subltype E L (Shared κ) (#r1) r2
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt None))) T.
  Proof.
    iIntros "(%Hels & %Htag & %sem & %Hsem & %Heq & %rv & %Hrfn & %rp & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_shared_in_inj_none;
      [exact Hels | exact Htag | exact Hsem | exact Hst | exact Hrfn |].
    done.
  Qed.
  Definition weak_subltype_enum_shared_inj_none_inst := [instance @weak_subltype_enum_shared_inj_none].
  Global Existing Instance weak_subltype_enum_shared_inj_none_inst | 9.

  Lemma weak_subltype_enum_shared_inj_some E L {rt1 rt2 rte}
      (en1 : enum rt1) (en2 : enum rt2) variant1 r1 r2 tag κ
      (lt : ltype rte) (re : rte) `{!ContainsProtected r2} T :
    (let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = tag⌝ ∗
    ∃ sem, ⌜enum_tag_ty_inj en2 tag = Some sem⌝ ∗
    ∃ (Heq : sem.(enum_tag_sem_rt) = rte),
    ∃ rv, ⌜enum_ltype_variant_rfn en1 r1 v1 rv⌝ ∗
    weak_subltype E L (Shared κ) (#rv) (#re) v1.(eltv_ltype) lt
      (⌜r2 = #(sem.(enum_tag_rt_inj) (eq_rect _ RT_rt re _ (eq_sym Heq)))⌝ ∗ T))
    ⊢ weak_subltype E L (Shared κ) (#r1) r2
      (EnumLtype en1 variant1)
      (EnumLtype en2 (Some (mk_enum_ltype_variant tag rte lt (Some re)))) T.
  Proof.
    iIntros "(%Hels & %Htag & %sem & %Hsem & %Heq & %rv & %Hrfn & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & -> & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_shared_in_inj_some;
      [exact Hels | exact Htag | exact Hsem | exact Hst | exact Hrfn |].
    done.
  Qed.
  Definition weak_subltype_enum_shared_inj_some_inst := [instance @weak_subltype_enum_shared_inj_some].
  Global Existing Instance weak_subltype_enum_shared_inj_some_inst | 9.

  Lemma weak_subltype_enum_shared E L {rt} (en1 en2 : enum rt)
      variant1 variant2 r1 r2 κ T :
    ⌜r1 = r2⌝ ∗ ⌜enum_els en1 = enum_els en2⌝ ∗
    (* TODO: have dedicated sidecond solver for this *)
    ⌜∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
       (enum_ltype_variant_tag_compat en1 r v1 →
         v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_compat en2 r v2) ∧
       ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) ∧
       ∀ rv1 rv2, enum_ltype_variant_rfn en1 r v1 rv1 →
         enum_ltype_variant_rfn en2 r v2 rv2 →
         subltype E L (Shared κ) (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype)⌝ ∗ T
    ⊢ weak_subltype E L (Shared κ) r1 r2 (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(-> & %Hels & %Hsub & HT)" (??) "#CTX #HE HL".
    iAssert (∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
       ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
       enum_ltype_variant_ltype_incl (Shared κ) en1 r v1 en2 r v2)%I as "#Hu".
    { iIntros (r). iSplit.
      - iPureIntro. exact (proj1 (proj2 (Hsub r))).
      - iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
        iPoseProof (subltype_acc with "CTX HE HL") as "Hu".
        { exact (proj2 (proj2 (Hsub r)) rv1 rv2 Hrfn1 Hrfn2). }
        iDestruct "Hu" as "(_ & $)". }
    iFrame. iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    iApply enum_ltype_incl_shared; first done.
    iIntros (r). destruct (Hsub r) as [Hcompat Hpayload]. iSplitR; first done.
    iApply "Hu".
  Qed.
  Definition weak_subltype_enum_shared_inst := [instance @weak_subltype_enum_shared].
  Global Existing Instance weak_subltype_enum_shared_inst | 22.

  Lemma weak_subltype_enum_shared_none E L {rt} (en1 en2 : enum rt) r1 r2 κ T :
    ⌜r1 = r2⌝ ∗ ⌜full_enum_incl E L en1 en2⌝ ∗ T
    ⊢ weak_subltype E L (Shared κ) r1 r2 (EnumLtype en1 None) (EnumLtype en2 None) T.
  Proof.
    iIntros "(-> & %Hsub & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subtype_acc with "HE HL") as "(%Hst & #Hincl)";
      first by apply enum_full_subtype.
    iFrame. iModIntro. iSplitR. { simp_ltypes. iPureIntro. apply (Hst MetaNone). }
    iApply (ltype_incl_trans with "[]"); first iApply enum_t_unfold_2.
    iApply (ltype_incl_trans with "[Hincl]"); last iApply enum_t_unfold_1.
    iApply (type_ltype_incl_shared κ (enum_t en1) (enum_t en2) with "[] Hincl").
    iPureIntro. rewrite Hst. apply syn_type_compat_refl.
  Qed.
  Definition weak_subltype_enum_shared_none_inst := [instance @weak_subltype_enum_shared_none].
  Global Existing Instance weak_subltype_enum_shared_none_inst | 21.
  (* Mutable borrows retain their refinement and require invariant payloads. *)
  Lemma weak_subltype_enum_uniq E L {rt} (en1 en2 : enum rt)
      variant1 variant2 r1 r2 κ γ T :
    ⌜r1 = r2⌝ ∗ ⌜enum_els en1 = enum_els en2⌝ ∗
    (* TODO: have dedicated sidecond solver for this *)
    ⌜∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
      v1.(eltv_tag) = v2.(eltv_tag) ∧
      (enum_ltype_variant_compat en1 r v1 ↔ enum_ltype_variant_compat en2 r v2) ∧
      ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype) ∧
      ∀ rv1 rv2, enum_ltype_variant_rfn en1 r v1 rv1 →
        enum_ltype_variant_rfn en2 r v2 rv2 →
        eqltype E L Owned (#rv1) (#rv2) v1.(eltv_ltype) v2.(eltv_ltype)⌝ ∗ T
    ⊢ weak_subltype E L (Uniq κ γ) r1 r2 (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(-> & %Hels & %Hsub & HT)" (??) "#CTX #HE HL".
    iAssert (∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
      ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
      ⌜enum_ltype_variant_compat en1 r v1 ↔ enum_ltype_variant_compat en2 r v2⌝ ∗
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      enum_ltype_variant_ltype_eq Owned en1 r v1 en2 r v2)%I as "#Hu".
    { iIntros (r). destruct (Hsub r) as (Htag & Hcompat & Hst & Hpayload).
      iR. iR. iR. iIntros (rv1 rv2) "%Hrfn1 %Hrfn2".
      iPoseProof (eqltype_acc with "CTX HE HL") as "(_ & $)".
      exact (Hpayload rv1 rv2 Hrfn1 Hrfn2). }
    iFrame. iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    by iApply enum_ltype_incl_uniq.
  Qed.
  Definition weak_subltype_enum_uniq_inst := [instance @weak_subltype_enum_uniq].
  Global Existing Instance weak_subltype_enum_uniq_inst | 22.

  Lemma weak_subltype_enum_uniq_none E L {rt} (en1 en2 : enum rt) r1 r2 κ γ T :
    ⌜r1 = r2⌝ ∗ ⌜full_enum_incl E L en1 en2⌝ ∗ ⌜full_enum_incl E L en2 en1⌝ ∗ T
    ⊢ weak_subltype E L (Uniq κ γ) r1 r2 (EnumLtype en1 None) (EnumLtype en2 None) T.
  Proof.
    iIntros "(-> & %H12 & %H21 & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subtype_acc with "HE HL") as "(%Hst & #H12)";
      first exact (enum_full_subtype _ _ _ _ H12).
    iPoseProof (full_subtype_acc with "HE HL") as "(%Hst2 & #H21)";
      first exact (enum_full_subtype _ _ _ _ H21).
    iFrame. iModIntro. iSplitR. { simp_ltypes. iPureIntro. apply (Hst MetaNone). }
    iApply (ltype_incl_trans with "[]"); first iApply enum_t_unfold_2.
    iApply (ltype_incl_trans with "[H12 H21]"); last iApply enum_t_unfold_1.
    iApply (type_eq_ltype_incl_uniq κ γ (enum_t en1) (enum_t en2) with "[] H12 H21").
    iPureIntro. rewrite Hst. apply syn_type_compat_refl.
  Qed.
  Definition weak_subltype_enum_uniq_none_inst := [instance @weak_subltype_enum_uniq_none].
  Global Existing Instance weak_subltype_enum_uniq_none_inst | 21.
End subltype.

Section unfolding.
  Context `{!typeGS Σ}.

  Lemma weak_subltype_enum_ofty_l E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant k r1 r2 T :
    weak_subltype E L k r1 r2 (EnumLtype en1 None) (EnumLtype en2 variant) T
    ⊢ weak_subltype E L k r1 r2 (◁ enum_t en1) (EnumLtype en2 variant) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & $)".
    iSplitR; first done.
    iApply (ltype_incl_trans with "[] Hincl"). iApply enum_t_unfold_1.
  Qed.
  Definition weak_subltype_enum_ofty_l_inst := [instance @weak_subltype_enum_ofty_l].
  Global Existing Instance weak_subltype_enum_ofty_l_inst | 20.

  Lemma weak_subltype_enum_ofty_r E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant k r1 r2 T :
    weak_subltype E L k r1 r2 (EnumLtype en1 variant) (EnumLtype en2 None) T
    ⊢ weak_subltype E L k r1 r2 (EnumLtype en1 variant) (◁ enum_t en2) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & $)".
    iSplitR; first done.
    iApply (ltype_incl_trans with "Hincl"). iApply enum_t_unfold_2.
  Qed.
  Definition weak_subltype_enum_ofty_r_inst := [instance @weak_subltype_enum_ofty_r].
  Global Existing Instance weak_subltype_enum_ofty_r_inst | 20.

  (* Fallback for targets whose enum structure is not exposed. *)

  Lemma weak_subltype_enum_ofty_1 E L {rt rt2} (en : enum rt) variant k r1 r2 (ty2 : type rt2) T :
    cast_ltype_to_type E L (EnumLtype en variant) (λ ty1 ,
      weak_subltype E L k r1 r2 (◁ ty1) (◁ ty2) T)
    ⊢ weak_subltype E L k r1 r2 (EnumLtype en variant) (◁ ty2) T.
  Proof.
    iIntros "(%ty1 & %Heqt & HT)".
    iIntros (??) "#CTX #HE HL".
    iMod ("HT" with "[] CTX HE HL") as "(% & Hincl & HL & $)"; first done.
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "(% & #Heq)"; first apply Heqt.
    simp_ltypes. iR.
    iFrame. iApply ltype_incl_trans; last done.
    iApply ltype_eq_ltype_incl_l.
    done.
  Qed.
  Definition weak_subltype_enum_ofty_1_inst := [instance @weak_subltype_enum_ofty_1].
  Global Existing Instance weak_subltype_enum_ofty_1_inst | 30.

  Lemma mut_eqltype_enum_ofty_1 E L {rt} (en : enum rt) variant (ty2 : type rt) T :
    cast_ltype_to_type E L (EnumLtype en variant) (λ ty1 ,
      mut_eqltype E L (◁ ty1) (◁ ty2) T)
    ⊢ mut_eqltype E L (EnumLtype en variant) (◁ ty2) T.
  Proof.
    iIntros "(%ty1 & %Heqt & %Hsubt & $)".
    iPureIntro.
    etrans; last apply Hsubt.
    done.
  Qed.
  Definition mut_eqltype_enum_ofty_1_inst := [instance @mut_eqltype_enum_ofty_1].
  Global Existing Instance mut_eqltype_enum_ofty_1_inst.
End unfolding.
