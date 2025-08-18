From refinedrust Require Export type.
From refinedrust.struct Require Import def.
From refinedrust Require Import options.

(** ** Subtyping lemmas for struct *)

Section subtype.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Definition struct_t_incl_precond {rts1 rts2 : list RT} (tys1 : hlist type rts1) (tys2 : hlist type rts2) (rs1 : plist place_rfnRT rts1) (rs2 : plist place_rfnRT rts2) :=
    ([∗ list] t1; t2 ∈ hpzipl _ tys1 rs1; hpzipl _ tys2 rs2,
      match (projT2 t1).2, (projT2 t2).2 with
      | #r1, #r2 => type_incl r1 r2 (projT2 t1).1 (projT2 t2).1
      | _, _ => ∃ (Heq : projT1 t1 = projT1 t2), ⌜(projT2 t1).2 = rew <- [place_rfnRT] Heq in (projT2 t2).2⌝ ∗ ∀ (r : (projT1 t1 : RT)), type_incl r (rew [RT_rt] Heq in r) (projT2 t1).1 (projT2 t2).1
      end)%I.
  Global Instance struct_t_incl_precond_pers {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 :
    Persistent (struct_t_incl_precond tys1 tys2 rs1 rs2).
  Proof.
    apply big_sepL2_persistent. intros ? [? [? []]] [? [? []]]; simpl; apply _.
  Qed.

  Lemma struct_t_own_val_mono {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls v π :
    struct_t_incl_precond tys1 tys2 rs1 rs2 -∗
    v ◁ᵥ{π} rs1 @ struct_t sls tys1 -∗
    v ◁ᵥ{π} rs2 @ struct_t sls tys2.
  Proof.
    iIntros "#Hincl Hv".
    iPoseProof (big_sepL2_length with "Hincl") as "%Hlen".
    rewrite !length_hpzipl in Hlen.
    iDestruct "Hv" as "(%sl & %Halg & %Hlen1 & %Hly & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR.
    iApply (big_sepL2_impl' with "Hb").
    { done. }
    { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k v1 [rt1 [ty1 r1]] v2 [rt2 [ty2 r2]] Hlook_v1 Hlook_ty1 Hlook_v2 Hlook_ty2) "Hv".
    iDestruct "Hv" as "(%r' & %ly & Hrfn & %Hly' & %Hst' & Hv)".
    rewrite Hlook_v2 in Hlook_v1. injection Hlook_v1 as ->.
    apply pad_struct_lookup_Some in Hlook_ty1 as (n & ly' & Hly'' & Hlook_ty1).
    2: { rewrite length_hpzipl Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    rewrite Hly'' in Hly'. injection Hly' as ->.
    eapply pad_struct_lookup_Some_1' in Hlook_ty2; last done; first last.
    { rewrite length_hpzipl -Hlen Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    destruct Hlook_ty1 as [ [? Hlook_ty1] | (-> & Hlook_ty1)]; first last.
    { (* padding *)
      destruct Hlook_ty2 as [ [? ?] | [_ Hlook_ty2]]; first congruence.
      injection Hlook_ty1 => _ _ ?; subst.
      injection Hlook_ty2 => _ _ ?; subst.
      apply existT_inj in Hlook_ty1. injection Hlook_ty1 as -> ->.
      apply existT_inj in Hlook_ty2. injection Hlook_ty2 as -> ->.
      iExists r', ly. rewrite Hly''. iFrame. done. }
    (* element *)
    destruct Hlook_ty2 as [[_ Hlook_ty2] | [? _]]; last congruence.
    rewrite /struct_own_el_val.
    iPoseProof (big_sepL2_lookup with "Hincl") as "Ha"; [apply Hlook_ty1 | apply Hlook_ty2 | ]; simpl.
    destruct r1 as [r1 | ]; first destruct r2 as [r2 | ].
    + iDestruct "Hrfn" as "<-".
      iDestruct "Ha" as "(%Hst & _ & #Ha & _)". iPoseProof ("Ha" with "Hv") as "Hv".
      rewrite Hly'' -Hst. eauto with iFrame.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst.
      iDestruct "Hrfn" as "<-". done.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst. cbn in Heq'. subst.
      iDestruct ("Ha" $! r') as "(%Hst & _ & #Ha' & _)". iPoseProof ("Ha'" with "Hv") as "Hv".
      rewrite Hly'' -Hst. eauto with iFrame.
  Qed.

  Lemma struct_t_shr_mono {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls l κ π :
    struct_t_incl_precond tys1 tys2 rs1 rs2 -∗
    l ◁ₗ{π, κ} rs1 @ struct_t sls tys1 -∗
    l ◁ₗ{π, κ} rs2 @ struct_t sls tys2.
  Proof.
    iIntros "#Hincl Hl".
    iPoseProof (big_sepL2_length with "Hincl") as "%Hlen".
    rewrite !length_hpzipl in Hlen.
    iDestruct "Hl" as "(%sl & %Halg & %Hlen1 & %Hly & #Hlb & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR. iR.
    iApply (big_sepL_impl' with "Hb").
    { rewrite !pad_struct_length //. }
    iModIntro.
    iIntros (k [rt1 [ty1 r1]] [rt2 [ty2 r2]] Hlook_ty1 Hlook_ty2) "Hl".
    iDestruct "Hl" as "(%r' & %ly & Hrfn & %Hly' & %Hst' & #Hsc1 & Hl)".
    apply pad_struct_lookup_Some in Hlook_ty1 as (n & ly' & Hly'' & Hlook_ty1).
    2: { rewrite length_hpzipl Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    rewrite Hly'' in Hly'. injection Hly' as ->.
    eapply pad_struct_lookup_Some_1' in Hlook_ty2; last done; first last.
    { rewrite length_hpzipl -Hlen Hlen1. symmetry. by apply struct_layout_spec_has_layout_fields_length. }
    destruct Hlook_ty1 as [ [? Hlook_ty1] | (-> & Hlook_ty1)]; first last.
    { (* padding *)
      destruct Hlook_ty2 as [ [? ?] | [_ Hlook_ty2]]; first congruence.
      injection Hlook_ty1 => _ _ ?; subst.
      injection Hlook_ty2 => _ _ ?; subst.
      apply existT_inj in Hlook_ty1. injection Hlook_ty1 as -> ->.
      apply existT_inj in Hlook_ty2. injection Hlook_ty2 as -> ->.
      iExists r', ly. rewrite Hly''. iFrame. simpl. done. }
    (* element *)
    destruct Hlook_ty2 as [[_ Hlook_ty2] | [? _]]; last congruence.
    iPoseProof (big_sepL2_lookup with "Hincl") as "Ha"; [apply Hlook_ty1 | apply Hlook_ty2 | ]; simpl.
    rewrite /struct_own_el_shr.
    destruct r1 as [r1 | ]; first destruct r2 as [r2 | ].
    + iDestruct "Hrfn" as "<-".
      iDestruct "Ha" as "(%Hst & #Hsc & _ & #Ha)". iPoseProof ("Ha" with "Hl") as "Hl".
      iPoseProof ("Hsc" with "Hsc1") as "Hsc2".
      rewrite Hly'' -Hst. iFrame "#". eauto with iFrame.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst.
      iDestruct "Hrfn" as "<-". done.
    + iDestruct "Ha" as "(%Heq & %Heq' & Ha)". subst. cbn in Heq'. subst.
      iDestruct ("Ha" $! r') as "(%Hst & #Hsc & _ & #Ha')". iPoseProof ("Ha'" with "Hl") as "Hl".
      iPoseProof ("Hsc" with "Hsc1") as "Hsc2".
      rewrite Hly'' -Hst. iFrame "#". eauto with iFrame.
  Qed.

  Lemma struct_t_type_incl {rts1 rts2} (tys1 : hlist type rts1) (tys2 : hlist type rts2) rs1 rs2 sls :
    struct_t_incl_precond tys1 tys2 rs1 rs2 -∗
    type_incl rs1 rs2 (struct_t sls tys1) (struct_t sls tys2).
  Proof.
    iIntros "#Hincl".
    iPoseProof (big_sepL2_length with "Hincl") as "%Hlen".
    rewrite !length_hpzipl in Hlen.
    iSplitR; first done. iSplitR. { simpl. rewrite Hlen. done. }
    iSplit; iModIntro.
    - iIntros (??). by iApply struct_t_own_val_mono.
    - iIntros (???). by iApply struct_t_shr_mono.
  Qed.

  Lemma struct_t_full_subtype E L {rts} (tys1 : hlist type rts) (tys2 : hlist type rts) sls :
    Forall (λ '(existT _ (ty1, ty2)), full_subtype E L ty1 ty2) (hzipl2 _ tys1 tys2) →
    full_subtype E L (struct_t sls tys1) (struct_t sls tys2).
  Proof.
    intros Hsubt r. iIntros (?) "HL #HE".
    iApply struct_t_type_incl.
    iApply big_sepL2_forall.
    { intros ? [? [? []]] [? [? []]]; apply _. }
    iSplit. { iPureIntro. rewrite !length_hpzipl. done. }
    iIntros (? [rt1 [ty1 r1]] [rt2 [ty2 r2]] Hlook1 Hlook2); simpl.
    specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook1) as Hlook1'.
    specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook2) as Hlook2'.
    rewrite Hlook2' in Hlook1'. injection Hlook1' as ->.
    apply (hpzipl_lookup_inv_hzipl_pzipl _ _ r) in Hlook1 as (Hlook11 & Hlook12).
    apply (hpzipl_lookup_inv_hzipl_pzipl _ _ r) in Hlook2 as (Hlook21 & Hlook22).
    rewrite Hlook22 in Hlook12. injection Hlook12 as [= <-%existT_inj].
    opose proof* (hzipl_hzipl2_lookup _ tys1 tys2) as Hlook; [done.. | ].
    specialize (Forall_lookup_1 _ _ _ _ Hsubt Hlook) as Hx.
    iPoseProof (full_subtype_acc_noend with "HE HL") as "Ha"; first apply Hx.
    destruct r2.
    - iApply "Ha".
    - iExists eq_refl. iR. done.
  Qed.
End subtype.


