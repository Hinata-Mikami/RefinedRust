From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype.
From refinedrust.enum Require Import def subtype subltype unfold.
From refinedrust Require Import programs.
From refinedrust Require Import options.


Section subtype.
  Context `{!typeGS Σ}.

  Lemma owned_subtype_enum π E L pers {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) r1 r2 T :
    ⌜fast_syntype_eq_hint (enum_els en1 = enum_els en2)⌝ ∗
    ⌜enum_tag en1 r1 = enum_tag en2 r2⌝ ∗
    ⌜fast_syntype_eq_hint (ty_syn_type (enum_ty en1 r1) MetaNone = ty_syn_type (enum_ty en2 r2) MetaNone)⌝ ∗
    owned_subtype π E L pers (enum_r en1 r1) (enum_r en2 r2)
      (enum_ty en1 r1) (enum_ty en2 r2) T
    ⊢ owned_subtype π E L pers r1 r2 (enum_t en1) (enum_t en2) T.
  Proof.
    iIntros "(%Hels & %Htag & %Hst & HT)" (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & Hincl & $ & $)".
    destruct pers; simpl.
    - iDestruct "Hincl" as "#Hincl". iModIntro. iModIntro.
      iSplitR; last iSplitR.
      + iPureIntro. simpl. rewrite Hels. apply syn_type_size_eq_refl.
      + done.
      + iIntros (v). iApply (enum_t_own_val_mono _ true).
        rewrite /enum_t_incl_precond /=. iR. iR. iR. done.
    - iModIntro. iSplitR; last iSplitR.
      + iPureIntro. simpl. rewrite Hels. apply syn_type_size_eq_refl.
      + done.
      + iIntros (v). iApply (enum_t_own_val_mono _ false).
        rewrite /enum_t_incl_precond /=. iR. iR. iR. done.
  Qed.
  Definition owned_subtype_enum_inst := [instance @owned_subtype_enum].
  Global Existing Instance owned_subtype_enum_inst | 20.

  Lemma weak_subtype_enum E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) r1 r2 T :
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜enum_tag en1 r1 = enum_tag en2 r2⌝ ∗
    weak_subtype E L (enum_r en1 r1) (enum_r en2 r2)
      (enum_ty en1 r1) (enum_ty en2 r2) T
    ⊢ weak_subtype E L r1 r2 (enum_t en1) (enum_t en2) T.
  Proof.
    iIntros "(%Hels & %Htag & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & $)".
    iModIntro. iSplitR.
    { iPureIntro. intros m. simpl. by rewrite Hels. }
    iApply enum_t_type_incl. iR. iR. iR. done.
  Qed.
  Definition weak_subtype_enum_inst := [instance @weak_subtype_enum].
  Global Existing Instance weak_subtype_enum_inst | 20.

  Lemma mut_subtype_enum E L {rt} (en1 en2 : enum rt) T :
    ⌜full_enum_incl E L en1 en2⌝ ∗ T
    ⊢ mut_subtype E L (enum_t en1) (enum_t en2) T.
  Proof. iIntros "(%Hincl & $)". iPureIntro. by apply enum_full_subtype. Qed.
  Definition mut_subtype_enum_inst := [instance @mut_subtype_enum].
  Global Existing Instance mut_subtype_enum_inst | 20.

  Lemma weak_subltype_enum_owned_in E L {rt1 rt2}
      (en1 : enum rt1) (en2 : enum rt2) variant1 variant2 r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗
    let v1 := interp_enum_ltype_variant en1 variant1 r1 in
    let v2 := interp_enum_ltype_variant en2 variant2 r2' in
    ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜v1.(eltv_tag) = v2.(eltv_tag)⌝ ∗
    ⌜enum_ltype_variant_tag_compat en2 r2' v2⌝ ∗
    weak_subltype E L Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn))
      v1.(eltv_ltype) v2.(eltv_ltype) T)
    ⊢ weak_subltype E L Owned (#r1) r2
      (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(%r2' & -> & %Hels & %Htag & %Hcompat & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(%Hst & Hincl & $ & $)".
    iModIntro. iSplitR. { simp_ltypes. by rewrite Hels. }
    by iApply enum_ltype_incl_owned_in.
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
      (EnumLtype en1 (Some (mk_enum_ltype_variant tag rte lt re))) (EnumLtype en2 None) T.
  Proof.
    iIntros "(%r2' & -> & %Hels & %Ht2 & HT)".
    iApply weak_subltype_enum_owned_in.
    iExists r2'. iSplitR; first done.
    rewrite interp_enum_ltype_variant_Some_match; last done.
    rewrite /interp_enum_ltype_variant /canonical_enum_ltype_variant /=.
    rewrite (enum_tag'_Some en2 r2' tag Ht2).
    iFrame. done.
  Qed.
  Definition weak_subltype_enum_owned_some_none_inst := [instance @weak_subltype_enum_owned_some_none].
  Global Existing Instance weak_subltype_enum_owned_some_none_inst | 10.

  (* Unknown outer refinements must be preserved, including ghost refinements.
     The payload conversion therefore has to hold uniformly. *)
  Lemma weak_subltype_enum_owned E L {rt} (en1 en2 : enum rt)
      variant1 variant2 r1 r2 T :
    ⌜r1 = r2⌝ ∗ ⌜enum_els en1 = enum_els en2⌝ ∗
    ⌜∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
      (enum_ltype_variant_tag_compat en1 r v1 →
        v1.(eltv_tag) = v2.(eltv_tag) ∧ enum_ltype_variant_tag_compat en2 r v2) ∧
      subltype E L Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype)⌝ ∗ T
    ⊢ weak_subltype E L Owned r1 r2 (EnumLtype en1 variant1) (EnumLtype en2 variant2) T.
  Proof.
    iIntros "(-> & %Hels & %Hsub & HT)" (??) "#CTX #HE HL".
    iAssert (∀ r, let v1 := interp_enum_ltype_variant en1 variant1 r in
      let v2 := interp_enum_ltype_variant en2 variant2 r in
      ⌜ltype_st v1.(eltv_ltype) = ltype_st v2.(eltv_ltype)⌝ ∗
      ltype_incl Owned (#v1.(eltv_rfn)) (#v2.(eltv_rfn)) v1.(eltv_ltype) v2.(eltv_ltype))%I as "#Hu".
    { iIntros (r). iApply (subltype_acc with "CTX HE HL"). exact (proj2 (Hsub r)). }
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
End subtype.

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
