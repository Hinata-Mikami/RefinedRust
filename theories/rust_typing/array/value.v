From refinedrust Require Export type ltypes.
From refinedrust Require Import value programs.
From refinedrust.array Require Import def.
From refinedrust Require Import options.

Section value.
  Context `{!typeGS Σ}.

  Lemma value_t_untyped_to_array' π v vs n ly ly' :
    ly_size ly' = ly_size ly * n →
    syn_type_has_layout (UntypedSynType ly) ly →
    v ◁ᵥ{π} vs @ value_t (UntypedSynType ly') -∗
    v ◁ᵥ{π} (fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ (array_t n (value_t (UntypedSynType ly))).
  Proof.
    iIntros (Hsz ?) "Hv". rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%ot & %Hot & %Hmv & %Hv & %Hst)".
    apply use_op_alg_untyped_inv in Hot as ->.
    simpl in *.
    apply is_memcast_val_untyped_inv in Hmv as <-.
    apply (syn_type_has_layout_untyped_inv) in Hst as (_ & Hwf & Hsz' & Hal).
    iExists ly.
    iSplitR. { done. }
    iSplitR. { iPureIntro. rewrite Hsz in Hsz'. lia. }
    iSplitR. { rewrite length_fmap length_reshape length_replicate //. }
    iSplitR. { rewrite /has_layout_val /mk_array_layout /ly_mult /= Hv Hsz. done. }
    iApply big_sepL2_intro.
    { rewrite length_fmap length_reshape !length_replicate//. }
    iModIntro. iIntros (k ?? Hlook1 Hlook2).
    rewrite list_lookup_fmap in Hlook1.
    rewrite Hlook2 in Hlook1.  simpl in Hlook1. injection Hlook1 as [= <-].
    iExists _. iR.
    iExists (UntypedOp ly).
    simpl.
    iSplitR. { iPureIntro. apply use_op_alg_untyped; done. }
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
        { rewrite Hv. lia. }
    }
    iPureIntro. done.
  Qed.
  Lemma value_t_untyped_to_array  π v vs n ly :
    syn_type_has_layout (UntypedSynType ly) ly →
    v ◁ᵥ{π} vs @ value_t (UntypedSynType (mk_array_layout ly n)) -∗
    v ◁ᵥ{π} (fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ (array_t n (value_t (UntypedSynType ly))).
  Proof.
    iIntros (?) "Hv".
    iApply (value_t_untyped_to_array' with "Hv").
    - done.
    - done.
  Qed.

  Lemma value_t_untyped_from_array' π v vs (vs' : list val) vs'' n ly ly' :
    ly' = mk_array_layout ly n →
    vs = fmap PlaceIn vs' →
    vs'' = (mjoin vs') →
    v ◁ᵥ{π} vs @ (array_t n (value_t (UntypedSynType ly))) -∗
    v ◁ᵥ{π} vs'' @ value_t (UntypedSynType ly').
  Proof.
    iIntros (-> -> ->) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%ly'' & %Hst & %Hsz & <- & %Hv & Hl)".
    apply syn_type_has_layout_untyped_inv in Hst as (-> & Hwf & Hsz' & Hal).
    rewrite length_fmap. rewrite length_fmap in Hv.
    iExists (UntypedOp (mk_array_layout ly (length vs'))).
    iSplitR. { iPureIntro. apply use_op_alg_untyped; done. }

    rewrite big_sepL2_fmap_l.
    (* have: agreement between the values *)
    iSplitL. {
      iAssert ([∗ list] x1; x2 ∈ vs'; (reshape (replicate (length vs') (ly_size ly)) v), ⌜x1 = x2⌝ ∗ ⌜x1 `has_layout_val` ly⌝)%I with "[Hl]" as "Hl".
      { iApply (big_sepL2_impl with "Hl"). iModIntro.
        iIntros (? v1 v2 _ _) "(%v3 & -> & Ha)".
        rewrite {1}/ty_own_val/=.
        iDestruct "Ha" as "(%ot & %Hot & %Hv1 & ? & ?)".
        apply use_op_alg_untyped_inv in Hot as ->.
        apply is_memcast_val_untyped_inv in Hv1 as ->.
        simpl. iFrame. done. }
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
    iPureIntro.
    apply syn_type_has_layout_untyped.
    - done.
    - by apply array_layout_wf.
    - rewrite ly_size_mk_array_layout.
      move: Hsz. rewrite length_fmap MaxInt_eq. lia.
    - rewrite /ly_align_in_bounds ly_align_mk_array_layout //.
  Qed.
  Lemma value_t_untyped_from_array π v vs n ly :
    length vs = n * ly_size ly →
    v ◁ᵥ{π} (fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ (array_t n (value_t (UntypedSynType ly))) -∗
    v ◁ᵥ{π} vs @ value_t (UntypedSynType (mk_array_layout ly n)).
  Proof.
    iIntros (?) "Hv". iApply value_t_untyped_from_array'; last done.
    - done.
    - done.
    - rewrite join_reshape; first done.
      rewrite sum_list_replicate. lia.
  Qed.

  Lemma ofty_value_untyped_to_array π l vs ly n :
    syn_type_has_layout (UntypedSynType ly) ly →
    (l ◁ₗ[π, Owned false] #vs @ ◁ value_t (UntypedSynType (mk_array_layout ly n)))%I -∗
    l ◁ₗ[π, Owned false] #(fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ ◁ (array_t n (value_t (UntypedSynType ly))).
  Proof.
    iIntros (?) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly' & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    apply syn_type_has_layout_untyped_inv in Hst as (-> & Hwf & Hsz & Hal).
    iApply (ofty_mono_ly_strong_in with "[] [] Ha").
    - simpl. apply syn_type_has_layout_untyped; done.
    - simpl. apply (syn_type_has_layout_array _ _ ly); first done; first last.
      { move: Hsz. rewrite ly_size_mk_array_layout. lia. }
      done.
    - done.
    - done.
    - iIntros (v) "Ha".
      iApply value_t_untyped_to_array; first done. done.
    - simpl. eauto.
  Qed.
  Lemma ofty_value_untyped_from_array' π l (vs : list (place_rfn val)) (vs' : list val) (vs'' : val) ly ly' n :
    ly' = mk_array_layout ly n →
    vs = fmap PlaceIn vs' →
    vs'' = (mjoin vs') →
    (l ◁ₗ[π, Owned false] #vs @ ◁ (array_t n (value_t (UntypedSynType ly))))%I -∗
    (l ◁ₗ[π, Owned false] #vs'' @ ◁ value_t (UntypedSynType ly'))%I.
  Proof.
    iIntros (???) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly1 & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    specialize (syn_type_has_layout_array_inv _ _ _ Hst) as (ly2 & Hst' & -> & Hsz).
    specialize (syn_type_has_layout_untyped_inv _ _ Hst') as (-> & ? & ? & ?).
    iApply (ofty_mono_ly_strong_in with "[] [] Ha").
    - simpl. apply (syn_type_has_layout_array _ _ ly); [done.. | ].
      move: Hsz. rewrite ly_size_mk_array_layout. lia.
    - simpl. subst ly'. eapply syn_type_has_layout_make_untyped; done.
    - done.
    - subst ly'. done.
    - iIntros (v) "Ha".
      iApply value_t_untyped_from_array'; done.
    - simpl. eauto.
  Qed.
  Lemma ofty_value_untyped_from_array  π l (vs : val) ly n :
    length vs = n * ly_size ly →
    (l ◁ₗ[π, Owned false] #(fmap (M:=list) PlaceIn $ (reshape (replicate n (ly_size ly)) vs : list val)) @ ◁ (array_t n (value_t (UntypedSynType ly))))%I -∗
    (l ◁ₗ[π, Owned false] #vs @ ◁ value_t (UntypedSynType (mk_array_layout ly n)))%I.
  Proof.
    iIntros (?) "Hv". iApply ofty_value_untyped_from_array'; last done.
    - done.
    - done.
    - rewrite join_reshape; first done. rewrite sum_list_replicate. lia.
  Qed.

End value.
