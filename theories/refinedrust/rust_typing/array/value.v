From refinedrust.base Require Export type ltypes.
From refinedrust.base Require Import value programs.
From refinedrust.array Require Import def.
From refinedrust Require Import options.

Section value.
  Context `{!typeGS Σ}.

  Lemma value_t_untyped_to_array' π v vs n st ly m :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} vs @ value_t false (ArraySynType st n) -∗
    v ◁ᵥ{π, m} (fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ (array_t n (value_t false st)).
  Proof.
    iIntros (Hst1) "Hv".
    rewrite /ty_own_val/= array_t_own_val_unfold.
    iDestruct "Hv" as "(-> & %ot & %Hot & %Hmv & %Hv & %Hst)".
    unfold use_op_alg_typed in Hot.
    apply use_op_alg_untyped_inv in Hot as (ot1 & Hot & ->).
    simpl in *.
    apply is_memcast_val_untyped_inv in Hmv as <-.
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & Hot_eq & Hsz).
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iExists ly.
    iR.
    iSplitR. { iPureIntro. by apply value_syn_type. }
    iSplitR. { iPureIntro. rewrite Hot_eq in Hsz. rewrite ly_size_mk_array_layout in Hsz. lia. }
    iSplitR. { rewrite length_fmap length_reshape length_replicate //. }
    iSplitR. { rewrite Hot_eq in Hv. done. }
    iApply big_sepL2_intro.
    { rewrite length_fmap length_reshape !length_replicate//. }
    iModIntro. iIntros (k ?? Hlook1 Hlook2).
    rewrite list_lookup_fmap in Hlook1.
    rewrite Hlook2 in Hlook1.  simpl in Hlook1. injection Hlook1 as [= <-].
    iExists _. iR.
    rewrite /ty_own_val/=. iR.
    iExists (UntypedOp ly).
    simpl.
    iSplitR. { iPureIntro.
      apply syn_type_has_layout_op_alg in Hst as (ot2 & Hot2 & <-).
      eapply use_op_alg_untyped; first done.
      by apply syn_type_has_layout_untyped. }
    iSplitR. { iPureIntro. by left. }
    iSplitR. {
      destruct (decide (ly_size ly = 0)) as [Hzero | ].
      - (* size is 0 *)
        rewrite Hzero reshape_replicate_0 in Hlook2.
        apply lookup_replicate_1 in Hlook2 as (-> & ?).
        rewrite /has_layout_val Hzero //.
      - rewrite sublist_lookup_reshape in Hlook2.
        { rewrite sublist_lookup_Some' in Hlook2. destruct Hlook2 as (-> & ?).
          iPureIntro. rewrite /has_layout_val length_take length_drop. lia. }
        { lia. }
        { rewrite Hv Hot_eq ly_size_mk_array_layout. lia. }
    }
    iPureIntro. done.
  Qed.
  Lemma value_t_untyped_to_array  π v vs n st ly m :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} vs @ value_t false (ArraySynType st n) -∗
    v ◁ᵥ{π, m} (fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ (array_t n (value_t false st)).
  Proof.
    iIntros (?) "Hv".
    iApply (value_t_untyped_to_array' with "Hv").
    done.
  Qed.

  (* TODO move *)
  Lemma value_t_untyped_equiv π v v' st :
    v ◁ᵥ{π, MetaNone} v' @ value_t false st ⊣⊢
    ∃ ly, ⌜v = v'⌝ ∗ ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝.
  Proof.
    rewrite /ty_own_val/=.
    iSplit.
    - iIntros "(_ & (%ot & %Hot & %Hmc & % & %))".
      iPureIntro.
      apply use_op_alg_untyped_inv in Hot as (ot1 & Hot & ->).
      destruct Hmc as [-> | (st' & ->)].
      + eauto.
      + rewrite mem_cast_UntypedOp. eauto.
    - iIntros "(%ly & <- & %Hst & %Hly)".
      iR. opose proof* syn_type_has_layout_op_alg as (ot & Hot & heq); first apply Hst.
      subst ly. iExists (UntypedOp (ot_layout ot)).
      iPureIntro. split_and!.
      + eapply use_op_alg_untyped; first done.
        by apply syn_type_has_layout_untyped.
      + by left.
      + done.
      + done.
  Qed.


  Lemma value_t_untyped_from_array' π v vs (vs' : list val) vs'' n st m :
    vs = fmap PlaceIn vs' →
    vs'' = (mjoin vs') →
    v ◁ᵥ{π, m} vs @ (array_t n (value_t false st)) -∗
    v ◁ᵥ{π, m} vs'' @ value_t false (ArraySynType st n).
  Proof.
    iIntros (-> ->) "Hv".
    rewrite /ty_own_val/= array_t_own_val_unfold.
    iDestruct "Hv" as "(%ly & -> & %Hst & %Hsz & <- & %Hv & Hl)".
    iR.
    simpl in Hst.
    (*apply syn_type_has_layout_untyped_inv in Hst as (-> & Hwf & Hsz' & Hal).*)
    rewrite length_fmap. rewrite length_fmap in Hv.
    rewrite length_fmap in Hsz.
    opose proof* (syn_type_has_layout_array st (length vs')) as Hst'; [ done | | done | ].
    { by apply syn_type_has_layout_untyped_inv. }
    iExists (UntypedOp (mk_array_layout ly (length vs'))).
    iSplitR. {
      iPureIntro.
      specialize (syn_type_has_layout_op_alg _ _ Hst') as (ot & Hot & Hot_eq).
      eapply use_op_alg_untyped; first last.
      - apply syn_type_has_layout_untyped. done.
      - done. }

    rewrite big_sepL2_fmap_l.
    (* have: agreement between the values *)
    iSplitL. {
      iAssert ([∗ list] x1; x2 ∈ vs'; (reshape (replicate (length vs') (ly_size ly)) v), ⌜x1 = x2⌝ ∗ ⌜x1 `has_layout_val` ly⌝)%I with "[Hl]" as "Hl".
      { iApply (big_sepL2_impl with "Hl"). iModIntro.
        iIntros (? v1 v2 _ _) "(%v3 & -> & Ha)".
        rewrite value_t_untyped_equiv.
        iDestruct "Ha" as "(%ly' & <- & % & %)".
        apply syn_type_has_layout_untyped_inv in Hst.
        assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
        done. }
      rewrite big_sepL2_sep. iDestruct "Hl" as "(Hl1 & Hl)".
      iPoseProof (big_sepL2_Forall2 with "Hl1") as "%Hl1".
      apply Forall2_eq in Hl1 as ->.
      iClear "Hl1". rewrite big_sepL2_elim_r.
      rewrite length_reshape length_replicate.
      rewrite join_reshape.
      - iPureIntro. left. done.
      - rewrite sum_list_replicate Hv ly_size_mk_array_layout.
        lia. }
    iSplitR. { iPureIntro. rewrite /has_layout_val Hv /= //. }
    iPureIntro. simpl.
    eapply syn_type_has_layout_array.
    - done.
    - by apply syn_type_has_layout_untyped_inv.
    - done.
  Qed.
  Lemma value_t_untyped_from_array π v vs n k st m :
    length vs = n * k →
    v ◁ᵥ{π, m} (fmap (M:=list) PlaceIn $ (reshape (replicate n k) vs : list val)) @ (array_t n (value_t false st)) -∗
    v ◁ᵥ{π, m} vs @ value_t false (ArraySynType st n).
  Proof.
    iIntros (?) "Hv". iApply value_t_untyped_from_array'; last done.
    - done.
    - rewrite join_reshape; first done.
      rewrite sum_list_replicate. lia.
  Qed.

  Lemma ofty_value_untyped_to_array π l vs st ly n :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned] #vs @ ◁ value_t false (ArraySynType st n))%I -∗
    l ◁ₗ[π, Owned] #(fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ ◁ (array_t n (value_t false st)).
  Proof.
    iIntros (?) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly' & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    (*apply syn_type_has_layout_untyped_inv in Hst as (-> & Hwf & Hsz & Hal).*)
    iApply (ofty_mono_ly_strong_in with "[] [] Ha").
    - simpl. done.
    - simpl. apply syn_type_has_layout_untyped_inv in Hst.
      eapply syn_type_compat_array; last done; first done.
      by apply syn_type_compat_untyped_r.
    - done.
    - done.
    - iIntros (v) "Ha".
      iApply value_t_untyped_to_array; first done. done.
    - simpl. eauto.
  Qed.
  Lemma ofty_value_untyped_from_array' π l (vs : list (place_rfn val)) (vs' : list val) (vs'' : val) st n :
    vs = fmap PlaceIn vs' →
    vs'' = (mjoin vs') →
    (l ◁ₗ[π, Owned] #vs @ ◁ (array_t n (value_t false st)))%I -∗
    (l ◁ₗ[π, Owned] #vs'' @ ◁ value_t false (ArraySynType st n))%I.
  Proof.
    iIntros (??) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly1 & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    specialize (syn_type_has_layout_array_inv _ _ _ Hst) as (ly2 & Hst' & -> & Hsz).
    iApply (ofty_mono_ly_strong_in with "[] [] Ha").
    - simpl. done.
    - simpl. apply syn_type_has_layout_untyped.
      eapply syn_type_compat_array; last done; first done.
      by apply syn_type_compat_untyped_l.
    - done.
    - done.
    - iIntros (v) "Ha".
      iApply value_t_untyped_from_array'; done.
    - simpl. eauto.
  Qed.
  Lemma ofty_value_untyped_from_array  π l (vs : val) st k n :
    length vs = n * k →
    (l ◁ₗ[π, Owned] #(fmap (M:=list) PlaceIn $ (reshape (replicate n k) vs : list val)) @ ◁ (array_t n (value_t false st)))%I -∗
    (l ◁ₗ[π, Owned] #vs @ ◁ value_t false (ArraySynType st n))%I.
  Proof.
    iIntros (?) "Hv". iApply ofty_value_untyped_from_array'; last done.
    - done.
    - rewrite join_reshape; first done. rewrite sum_list_replicate. lia.
  Qed.

End value.
