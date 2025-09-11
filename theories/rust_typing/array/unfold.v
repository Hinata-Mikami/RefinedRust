From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit_def.
From refinedrust Require Import programs.
From refinedrust.array Require Import def.
From refinedrust Require Import options.

(** ** Unfolding [array_t] into [ArrayLtype]. *)
Section lemmas.
  Context `{!typeGS Σ}.

  Lemma array_t_rfn_length_eq π {rt} (ty : type rt) len r v :
    v ◁ᵥ{π} r @ array_t len ty -∗ ⌜length r = len⌝.
  Proof.
    rewrite /ty_own_val/=. iIntros "(%ly & %Hst & % & $ & _)".
  Qed.

  (** Learnable *)
  Global Program Instance learn_from_hyp_val_array {rt} (ty : type rt) xs len :
    LearnFromHypVal (array_t len ty) xs :=
    {| learn_from_hyp_val_Q := ⌜length xs = len⌝ |}.
  Next Obligation.
    iIntros (????????) "Hv".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    by iFrame.
  Qed.

  (* TODO: possibly also prove these lemmas for location ownership? *)
End lemmas.

Section split.
  Context `{!typeGS Σ}.

  Lemma array_t_own_val_split_reshape {rt} (ty : type rt) π (n : nat) v rs (num size : nat) ly :
    n = (num * size)%nat →
    syn_type_has_layout (st_of ty) ly →
    v ◁ᵥ{π} rs @ array_t n ty -∗
    ⌜mjoin (reshape (replicate num (ly_size ly * size)%nat) v) = v⌝ ∗
    [∗ list] v'; r' ∈ reshape (replicate num (ly_size ly * size)%nat) v; reshape (replicate num size) rs,
      v' ◁ᵥ{π} r' @ array_t size ty.
  Proof.
    iIntros (-> Hst) "Hv".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Hst' & %Hlyv)".
    apply syn_type_has_layout_array_inv in Hst' as (ly'' & Hst'' & -> & Hsz).
    assert (ly'' = ly) as -> by by eapply syn_type_has_layout_inj.
    opose proof (join_reshape (replicate num (ly_size ly * size)) v _) as Hv_eq.
    { rewrite sum_list_replicate. rewrite Hlyv {2}/ly_size/=. lia. }
    opose proof (join_reshape (replicate num size) rs _) as Hrs_eq.
    { rewrite sum_list_replicate Hlen//. }
    rewrite -{1}Hv_eq -{1}Hrs_eq.
    iSplitR; first done.
    iInduction num as [ | num] "IH" forall (v rs Hlyv Hv_eq Hrs_eq Hlen); simpl; first done.
    iPoseProof (array_t_own_val_split with "Hv") as "($ & Hv2)".
    { rewrite length_take. lia. }
    { rewrite length_join.
      rewrite fmap_length_reshape; rewrite sum_list_replicate; first done.
      rewrite length_drop. lia. }
    { rewrite length_take /size_of_st.
      rewrite /use_layout_alg' Hst/=.
      rewrite Hlyv. rewrite ly_size_mk_array_layout. lia. }
    { rewrite length_join. rewrite fmap_length_reshape.
      { rewrite sum_list_replicate. rewrite /size_of_st /use_layout_alg' Hst/=. lia. }
      rewrite sum_list_replicate.
      rewrite length_drop.
      rewrite Hlyv ly_size_mk_array_layout. lia. }
    iApply "IH"; last done; iPureIntro.
    { rewrite ly_size_mk_array_layout. rewrite ly_size_mk_array_layout in Hsz. lia. }
    { rewrite /has_layout_val length_drop Hlyv !ly_size_mk_array_layout. lia. }
    { rewrite join_reshape; first done.
      rewrite sum_list_replicate length_drop.
      rewrite Hlyv ly_size_mk_array_layout. lia. }
    { rewrite join_reshape; first done. rewrite sum_list_replicate length_drop Hlen. lia. }
    { rewrite length_drop Hlen. lia. }
  Qed.
  (* TODO: corresponding merge lemma *)



  Lemma array_t_ofty_split_reshape {rt} (ty : type rt) F π n num size l rs :
    lftE ⊆ F →
    n = num * size →
    (l ◁ₗ[π, Owned false] #rs @ ◁ array_t n ty) ={F}=∗
    [∗ list] i ↦ v ∈ (reshape (replicate num size) rs),
    (l offsetst{st_of ty}ₗ (i * size)) ◁ₗ[π, Owned false] #v @ (◁ array_t size ty).
  Proof.
    intros ? ->.
    rewrite !ltype_own_ofty_unfold; simpl.
    iIntros "(%ly & %Hst & %Hly & _ & #Hlb & _ & %r' & <- & Hx)".
    simpl in *.
    iMod (fupd_mask_mono with "Hx") as "Hx"; first done.
    iDestruct "Hx" as "(%v & Hl & Hv)".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iPoseProof (array_t_own_val_split_reshape _ _ _ _ _ num size with "Hv") as "(%Heq & Hv)"; [done.. | ].
    rewrite -{1}Heq.
    iPoseProof (heap_pointsto_mjoin_uniform _ _ (ly_size ly' * size) with "Hl") as "(Hlb' & Hl)".
    { intros v'. intros Hlen'%reshape_replicate_elem_length; first done.
      rewrite Hlyv. rewrite ly_size_mk_array_layout. lia. }
    iPoseProof (big_sepL2_length with "Hv") as "%Hlen_eq".
    iPoseProof (big_sepL_extend_r with "Hl") as "Hl"; first done.
    iPoseProof (big_sepL2_sep with "[$Hv $Hl]") as "Ha".
    iApply big_sepL2_elim_l.
    iApply (big_sepL2_wand with "Ha"). iApply big_sepL2_intro. { done. }
    iModIntro. iModIntro.
    iIntros (? ? ? Hlook1 Hlook2) "(Hv & Hl)".
    rewrite !ltype_own_ofty_unfold; simpl.
    iExists (mk_array_layout ly' size).
    assert (num > 0).
    { destruct num; last lia. simpl in *. naive_solver. }
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; [done.. | ].
      move: Hsz. rewrite ly_size_mk_array_layout. nia. }
    simpl.
    iSplitR. { iPureIntro.
      rewrite /has_layout_loc ly_align_mk_array_layout.
      rewrite /has_layout_loc ly_align_mk_array_layout in Hly.
      eapply has_layout_loc_offset_loc'.
      - rewrite /use_layout_alg' Hst//.
      - rewrite /use_layout_alg' Hst//. by eapply use_layout_alg_wf.
      - rewrite /use_layout_alg' Hst//. }
    iR. iSplitR.
    { iApply (loc_in_bounds_offset with "Hlb").
      - done.
      - simpl. lia.
      - rewrite /OffsetLocSt/offset_loc/use_layout_alg' Hst/=.
        rewrite !ly_size_mk_array_layout.
        apply lookup_lt_Some in Hlook2.
        move: Hlook2. rewrite length_reshape length_replicate.
        nia. }
    iR. iExists _. iR. iModIntro.
    iExists _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst/=.
    rewrite /offset_loc.
    assert ((ly_size ly' * (k * size))%Z = ((ly_size ly' * size)%nat * k)%Z) as -> by lia.
    done.
  Qed.
End split.

Section unfold.
  Context `{!typeGS Σ}.

  Local Lemma ofty_owned_array_extract_pointsto π F {rt} (ty : type rt) ly len l rs :
    lftE ⊆ F →
    length rs = len →
    syn_type_has_layout ty.(ty_syn_type) ly →
    loc_in_bounds l 0 (ly_size ly * len) -∗
    ([∗ list] k ↦ r ∈ rs, (l offset{ly}ₗ k) ◁ₗ[ π, Owned false] r @ (◁ ty)) -∗
    |={F}=> ∃ v, l ↦ v ∗
      ⌜v `has_layout_val` mk_array_layout ly len⌝ ∗
      [∗ list] k ↦ r; v' ∈ rs; reshape (replicate len (ly_size ly)) v, array_own_el_val π ty r v'.
  Proof.
    iIntros (? ? ?) "Hlb Hown".
    setoid_rewrite ltype_own_ofty_unfold. rewrite /lty_of_ty_own.
    simpl. iEval (rewrite /ty_own_val/=).
    iPoseProof (array_own_val_extract_pointsto_fupd with "Hlb [Hown]") as "Ha"; [done.. | | ].
    { iApply (big_sepL_wand with "Hown").
      iApply big_sepL_intro. iModIntro. iIntros (k r Hlook).
      rewrite /array_own_el_loc.
      iIntros "(%ly' & %Hst & %Hly & Hsc & Hlb & _ & %r' & Hrfn & Ha)".
      iMod "Ha" as "(%v & ? & ?)".
      iModIntro. iExists _. eauto with iFrame. }
    iApply (fupd_mask_mono with "Ha"); done.
  Qed.

  Local Lemma ofty_owned_array_join_pointsto π {rt} (ty : type rt) ly len l rs v :
    length rs = len →
    v `has_layout_val` mk_array_layout ly len →
    syn_type_has_layout ty.(ty_syn_type) ly →
    l `has_layout_loc` ly →
    l ↦ v -∗
    ([∗ list] k ↦ r; v' ∈ rs; reshape (replicate len (ly_size ly)) v, array_own_el_val π ty r v') -∗
    ([∗ list] k ↦ r ∈ rs, (l offset{ly}ₗ k) ◁ₗ[ π, Owned false] r @ (◁ ty)).
  Proof.
    iIntros (? ? ? ?) "Hl Ha".
    iPoseProof (array_own_val_join_pointsto with "Hl Ha") as "Ha"; [done.. | ].
    iApply (big_sepL_wand with "Ha").
    iApply big_sepL_intro. iModIntro.
    rewrite /array_own_el_loc.
    iIntros (k r ?) "(%v' & %r' & Hl & Hrfn & Hv)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. iR.
    iSplitR. { iPureIntro. apply has_layout_loc_offset_loc; last done. by eapply use_layout_alg_wf. }
    iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    rewrite Hv. iR. iR. iExists _. by iFrame.
  Qed.

  Lemma array_t_unfold_1_owned {rt} wl (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Owned wl) rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hsz & % & #Hlb & Hcreds & %r' & Hrfn & Hb)".
    iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly len). iFrame "% ∗".
    simpl. iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    iR. iR.
    iNext. iMod "Hb" as "(%Hlen & Hb)".
    rewrite big_sepL2_replicate_l; last done.
    iMod (ofty_owned_array_extract_pointsto with "Hlb [Hb]") as "(%v & Hl & % & Ha)"; [done.. | | ].
    { iApply (big_sepL_impl with "Hb"). iModIntro. iIntros (k r Hlook). iIntros "(_ & $)". }
    iModIntro. iExists v. iFrame.
    iR. done.
  Qed.

  Lemma array_t_unfold_1_shared {rt} κ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Shared κ) rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hsz & % & #Hlb & %r' & Hrfn & #Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly len). simpl.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    iR. iR. iR. iExists _. iFrame.
    iModIntro. iMod "Hb" as "(%Hlen & Hb)".
    rewrite big_sepL2_replicate_l; last done.
    rewrite /ty_shr/=.
    iExists ly. iR. iR. iR. iR.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hb").
    iModIntro. iIntros (k r'' Hlook) "(_ & Hl)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Hst' & %Hloc & Hst & Hlb' & %r2 & Hrfn & #>Ha)".
    iModIntro. rewrite /array_own_el_shr. eauto with iFrame.
  Qed.

  Lemma array_t_unfold_1_uniq {rt} κ γ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Uniq κ γ) rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hsz & % & #Hlb & Hcreds & Hrfn & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly len). iFrame "% ∗".
    simpl. iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    iR. iR.
    iMod "Hb".
    (* TODO refactor *)
    set (R := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗ [∗ list] i↦r'' ∈ r', (l offset{ly}ₗ i) ◁ₗ[ π, Owned false] r'' @ ◁ ty))%I).
    iPoseProof (pinned_bor_iff _ _ R _ R with "[] [] Hb") as "Hb".
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "(_ & $)".
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "$".
        simp_ltypes. done.
    }
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty. iIntros "(_ & $)".
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty.
        iIntros "$". simp_ltypes. done.
    }
    iApply (pinned_bor_iff' with "[] Hb").
    iModIntro. iModIntro.
    iSplit.
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame. iMod "Ha" as "(%Hlen & Ha)".
      iMod (ofty_owned_array_extract_pointsto with "Hlb Ha") as "(%v & Hl & % & Ha)"; [done.. | ].
      iModIntro. iExists v. iFrame.
      iR. done.
    }
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame.
      iMod "Ha" as "(%v & Hl & Hv)".
      rewrite /ty_own_val/=.
      iDestruct "Hv" as "(%ly' & %Hst' & _ & %Hlen & %Hvly & Ha)".
      assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      iR. iApply (ofty_owned_array_join_pointsto with "Hl Ha"); done.
    }
  Qed.

  Local Lemma array_t_unfold_1' {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' k rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    destruct k.
    - by apply array_t_unfold_1_owned.
    - by apply array_t_unfold_1_shared.
    - by apply array_t_unfold_1_uniq.
  Qed.

  Lemma array_t_unfold_1 {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl k rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro.
    iSplitR. { simp_ltypes. rewrite {2}/ty_syn_type /array_t //. }
    iSplitR.
    - by iApply array_t_unfold_1'.
    - simp_ltypes. by iApply array_t_unfold_1'.
  Qed.

  Lemma array_t_unfold_2_owned {rt} wl (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Owned wl) rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hl & _ & Hlb & Hcreds & %rs' & Hrfn & Ha)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iModIntro. iExists _. iR.
    iSplitR. { iPureIntro. move: Hsz. rewrite ly_size_mk_array_layout MaxInt_eq. lia. }
    iR. rewrite ly_size_mk_array_layout. iFrame.
    iNext. iMod "Ha" as "(%v & Hl & Hv)".
    rewrite /ty_own_val /=.
    iDestruct "Hv" as "(%ly & %Hst' & % & %Hlen & %Hvly & Ha)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iR.
    rewrite big_sepL2_replicate_l; last done.
    iPoseProof (ofty_owned_array_join_pointsto with "Hl Ha") as "Ha"; [done.. | ].
    iApply (big_sepL_wand with "Ha"). iApply big_sepL_intro.
    iModIntro. iModIntro. iIntros (k r Hlook) "$".
    simp_ltypes. done.
  Qed.

  Lemma array_t_unfold_2_shared {rt} κ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Shared κ) rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & % & Hsc & #Hlb & %r' & Hrfn & #Hb)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iExists ly'. iR.
    iSplitR. { iPureIntro. move: Hsz. rewrite ly_size_mk_array_layout MaxInt_eq. lia. }
    iR. rewrite ly_size_mk_array_layout. iR.
    iExists _. iFrame.
    iModIntro. iMod "Hb" as "Hb". iModIntro.
    rewrite /ty_shr/=.
    iDestruct "Hb" as "(%ly & %Hst' & % & % & % & Hb)".
    iR.
    rewrite big_sepL2_replicate_l; last done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iModIntro. iIntros (k r'' Hlook) "Hl".
    simp_ltypes. iR.
    rewrite /array_own_el_shr.
    iDestruct "Hl" as "(%r1 & ? & #Hl)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. iR.
    iSplitR. { iPureIntro. apply has_layout_loc_offset_loc; last done. by eapply use_layout_alg_wf. }
    iPoseProof (ty_shr_sidecond with "Hl") as "#Hsc".
    iR. iSplitR. { iApply loc_in_bounds_array_offset; last done. apply lookup_lt_Some in Hlook.
      simpl in *. lia. }
    iExists _. iFrame. eauto.
  Qed.

  Lemma array_t_unfold_2_uniq {rt} κ γ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Uniq κ γ) rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & % & % & #Hlb & Hcreds & Hrfn & Hb)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iExists ly'. iFrame "% ∗".
    rewrite ly_size_mk_array_layout in Hsz.
    iSplitR. { iPureIntro. lia. }
    iR. iR. iMod "Hb".
    set (R := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗ [∗ list] i↦r'' ∈ r', (l offset{ly'}ₗ i) ◁ₗ[ π, Owned false] r'' @ ◁ ty))%I).
    iApply (pinned_bor_iff _ R _ R with "[] []").
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "$".
        simp_ltypes. done.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "(_ & $)".
    }
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty.
        iIntros "$". simp_ltypes. done.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty. iIntros "(_ & $)".
    }
    iApply (pinned_bor_iff' with "[] Hb").
    iModIntro. iModIntro.
    iSplit.
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame.
      iMod "Ha" as "(%v & Hl & Hv)".
      rewrite /ty_own_val/=.
      iDestruct "Hv" as "(%ly'' & %Hst' & _ & %Hlen & %Hvly & Ha)".
      assert (ly'' = ly') as -> by by eapply syn_type_has_layout_inj.
      iR. iApply (ofty_owned_array_join_pointsto with "Hl Ha"); done.
    }
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame. iMod "Ha" as "(%Hlen & Ha)".
      iMod (ofty_owned_array_extract_pointsto with "Hlb Ha") as "(%v & Hl & % & Ha)"; [done.. | ].
      iModIntro. iExists v. iFrame.
      iR. iSplitR. { iPureIntro. lia. } iR. done.
    }
  Qed.

  Local Lemma array_t_unfold_2' {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' k rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    destruct k.
    - by apply array_t_unfold_2_owned.
    - by apply array_t_unfold_2_shared.
    - by apply array_t_unfold_2_uniq.
  Qed.

  Lemma array_t_unfold_2 {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl k rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro.
    iSplitR. { simp_ltypes. rewrite {2}/ty_syn_type /array_t //. }
    iSplitR.
    - by iApply array_t_unfold_2'.
    - simp_ltypes. by iApply array_t_unfold_2'.
  Qed.

  Lemma array_t_unfold {rt} k (ty : type rt) (len : nat) rs:
    ⊢ ltype_eq k rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iSplit.
    - by iApply array_t_unfold_2.
    - by iApply array_t_unfold_1.
  Qed.

  Lemma array_t_unfold_full_eqltype E L {rt} (ty : type rt) (len : nat) :
    full_eqltype E L (◁ (array_t len ty))%I (ArrayLtype ty len []).
  Proof.
    iIntros (?) "HL CTX HE". iIntros (??). iApply array_t_unfold.
  Qed.
End unfold.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_array_unfold π E L l {rt} (def : type rt) len rs bmin k P T :
    typed_place π E L l (ArrayLtype def len []) rs bmin k P T
    ⊢ typed_place π E L l (◁ array_t len def) rs bmin k P T.
  Proof.
    iIntros "HT". iApply typed_place_eqltype; last done.
    apply array_t_unfold_full_eqltype.
  Qed.
  Global Instance typed_place_array_unfold_inst π E L l {rt} (def : type rt) len rs bmin k P :
    TypedPlace E L π l (◁ array_t len def)%I rs bmin k P | 20 :=
    λ T, i2p (typed_place_array_unfold π E L l def len rs bmin k P T).
End place.
