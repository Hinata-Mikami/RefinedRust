From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def subltype.
From refinedrust Require Import options.

(** ** Unfolding [struct_t] into [StructLtype] *)

Section unfold.
  Context `{!typeGS Σ}.
  Lemma struct_t_unfold_1_owned {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) wl r :
    ⊢ ltype_incl' (Owned wl) r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%ly & %Halg & %Hly & %Hsc & #Hlb & ? & %r' & Hrfn & Hv)".
    eapply use_layout_alg_struct_Some_inv in Halg as (sl & Halg & ->).
    (*assert (ly = sl) as ->. { eapply syn_type_has_layout_inj; first done.*)
      (*eapply use_struct_layout_alg_Some_inv. done. }*)
    iExists sl. do 4 iR. iFrame.
    iModIntro. iNext. iMod "Hv" as "(%v & Hl & Hv)".
    iDestruct "Hv" as "(%sl' & %Halg' & _ & %Hly' & Hb)".
    assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }
    rewrite hpzipl_hmap.
    set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
    rewrite (pad_struct_ext _ _ _ (λ ly, f (struct_make_uninit_type ly))); last done.
    rewrite pad_struct_fmap big_sepL_fmap.
    rewrite /struct_own_el_val heap_pointsto_reshape_sl; last done.
    iDestruct "Hl" as "(_ & Hl)".
    iPoseProof (big_sepL2_sep_sepL_l with "[$Hl $Hb]") as "Ha".

    iApply (big_sepL2_elim_l). iApply big_sepL2_fupd.
    iApply (big_sepL2_wand with "Ha").
    iApply big_sepL2_intro.
    { rewrite length_reshape pad_struct_length length_fmap length_fmap //. }
    iIntros "!>" (k w [rt [ty r0]] Hlook1 Hlook2) => /=.
    iIntros "(Hl & %r0' & %ly & Hrfn & %Hmem & %st & Hty)".
    iExists ly. iSplitR; first done. simp_ltypes.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iSplitR; first done.
    iExists ly. iSplitR; first done.
    iSplitR. { iPureIntro. eapply struct_layout_field_aligned; done. }
    iPoseProof (ty_own_val_sidecond with "Hty") as "#$".
    iSplitR. { iApply loc_in_bounds_sl_offset; done. }
    iSplitR; first done.
    iExists _. by iFrame.
  Qed.

  Lemma struct_t_unfold_1_shared {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) κ r :
    ⊢ ltype_incl' (Shared κ) r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%ly & %Halg & %Hly & %Hsc & #Hlb & %r' & Hrfn & #Hb)".
    apply use_layout_alg_struct_Some_inv in Halg as (sl & Halg & ->).
    iExists sl. iSplitR; first done.
    iSplitR; first done. iSplitR; first done. iFrame "Hlb".
    iExists r'. iFrame "Hrfn". iModIntro. iMod "Hb".
    iDestruct "Hb" as "(%sl' & %Halg' & _ & %Hly' & Hlb' & Hb)".
    assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }

    rewrite hpzipl_hmap.
    set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
    rewrite (pad_struct_ext _ _ _ (λ ly, f $ struct_make_uninit_type ly)); last done.
    rewrite pad_struct_fmap big_sepL_fmap.
    iModIntro. iApply (big_sepL_wand with "Hb").
    iApply big_sepL_intro. iIntros "!>" (k [rt0 [ty0 r0]] Hlook).
    iIntros "(%r0' & %ly & Hrfn & %Hmem & %Hst & #Hsc & #Hb)".
    iExists ly. iSplitR; first done. iSplitR; first done.
    simpl in *. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. iSplitR; first done.
    iSplitR.
    { iPureIntro. eapply struct_layout_field_aligned; done. }
    iSplitR; first done.
    iSplitR. { iApply loc_in_bounds_sl_offset; done. }
    iExists r0'. iFrame "Hrfn". iModIntro. iModIntro. done.
  Qed.

  (* The lemma stating the main unfolding condition for the Uniq case *)
  (* TODO: maybe we can refactor this a bit *)
  Local Lemma unfold_case_uniq {rts} π (tys : hlist type rts) sls sl l γ wl (b : bool) :
    wl = false →
    use_struct_layout_alg sls = Some sl →
    l `has_layout_loc` sl →
    length rts = length (sls_fields sls) →
    ⊢ loc_in_bounds l 0 (ly_size sl) -∗
      (∃ r' : plist place_rfnRT rts, gvar_auth γ r' ∗
        (|={lftE}=> ∃ v : val, l ↦ v ∗ v ◁ᵥ{ π} r' @ struct_t sls tys)) ↔
      (∃ r' : plist place_rfnRT rts, gvar_auth γ r' ∗ (|={lftE}=>
        [∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts ((λ X : RT, OfTy) +<$> tys) r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗
            ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, Owned wl] (projT2 ty).2 @ if b then ltype_core (projT2 ty).1 else (projT2 ty).1)).
  Proof.
    intros -> Hst Hly Hsc. iIntros "#Hlb".
    iSplit.
    * iIntros "(%r' & Hauth & Hb)". iExists _. iFrame. iDestruct "Hb" as ">(%v & Hl & Hb)".
      iApply big_sepL_fupd.
      iDestruct "Hb" as "(%sl' & %Halg & %Hlen & %Hly' & Hb)".
      assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }
      rewrite hpzipl_hmap.
      set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
      rewrite (pad_struct_ext _ _ _ (λ ly, f $ struct_make_uninit_type ly)); last done.
      rewrite pad_struct_fmap big_sepL_fmap.
      rewrite heap_pointsto_reshape_sl; last done. iDestruct "Hl" as "(_ & Hl)".
      iPoseProof (big_sepL2_sep_sepL_l with "[$Hl $Hb]") as "Ha".

      iApply big_sepL2_elim_l.
      iApply (big_sepL2_wand with "Ha").
      iApply big_sepL2_intro.
      { rewrite length_reshape pad_struct_length length_fmap length_fmap //. }
      iIntros "!>" (k w [rt [ty r0]] Hlook1 Hlook2) => /=.
      iIntros "(Hl & %r0' & %ly & Hrfn & %Hmem & %st & Hty)".
      iExists ly. iSplitR; first done. simp_ltypes.
      rewrite Tauto.if_same.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iSplitR; first done.
      iExists ly. iSplitR; first done.
      iSplitR. { iPureIntro. eapply struct_layout_field_aligned; done. }
      iPoseProof (ty_own_val_sidecond with "Hty") as "#$".
      iSplitR. { iApply loc_in_bounds_sl_offset; done. }
      iSplitR; first done.
      iExists _. by iFrame.
    * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
      iMod "Hb".
      specialize (struct_layout_field_aligned _ _ Hly) as Hfield_ly.
      (* generalize sl_members before initiating induction *)
      rewrite /ty_own_val /=.
      setoid_rewrite bi.sep_exist_l. rewrite bi_exist_comm.
      iExists sl. iFrame "%".
      rewrite /has_layout_val {1 2}/ly_size {1 2}/layout_of /=.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Hst).
      remember (sl_members sl) as slm eqn:Heqslm.
      remember (sls_fields sls) as slsm eqn:Heqslsm.
      clear Heqslsm Heqslm Hst sls sl Hly => Hlen.

      iInduction (slm) as [ | [m ly] slm] "IH" forall (l slsm rts tys r' Hlen Hsc Hfield_ly); simpl.
      { iExists [].
        iSplitR. { iApply heap_pointsto_nil. iApply loc_in_bounds_shorten_suf; last done. lia. }
        iSplitR; first done. done. }
      rewrite -Hsc in Hlen.
      iDestruct "Hb" as "(Hb0 & Hb)".
      destruct m as [ m | ].
      --  simpl in Hlen. destruct rts as [ | rt rts]; first done.
          simpl in Hsc, Hlen. destruct slsm as [ | st slsm]; first done.
          inv_hlist tys => ty tys. destruct r' as [r0 r]. simpl.
          (* use the IH *)
          iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r).
          simpl in *.
          iSpecialize ("IH" with "[] [] [] [] [Hb]").
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. intros k ly' Hlook.
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eapply (Hfield_ly (S k)). done. }
          { iModIntro.
            iApply loc_in_bounds_offset; last done.
            - done.
            - simpl. lia.
            - simpl. rewrite /fmap. lia. }
          { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
            iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eauto. }
          iMod "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
          (* destruct the head *)
          iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
          injection Heq0 as [= <-].
          simp_ltypes. rewrite Tauto.if_same.
          rewrite ltype_own_ofty_unfold /lty_of_ty_own.
          iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & Hb0)".
          (* TODO need the v also under there. *)
          iMod "Hb0" as "(%v0 & Hl0 & Hb0)".
          move: Halg0. simp_ltypes. intros Halg0.
          assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
          iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
          iExists (v0 ++ v1). rewrite heap_pointsto_app.
          iSplitL "Hl0 Hl1".
          { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
            rewrite Hly0'. done. }
          iSplitR. { iPureIntro. rewrite length_app Hv1_len Hly0'. done. }
          iSplitL "Hb0 Hrfn0".
          { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
            rewrite -Hly0'. rewrite take_app_length. done. }
          rewrite -Hly0'. rewrite drop_app_length. done.
      -- simpl in Hlen. simpl.
         (* use the iH *)
          iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r').
          simpl in *.
          iSpecialize ("IH" with "[] [] [] [] [Hb]").
          { iPureIntro. lia. }
          { iPureIntro. lia. }
          { iPureIntro. intros k ly' Hlook.
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eapply (Hfield_ly (S k)). done. }
          { iModIntro.
            iApply loc_in_bounds_offset; last done.
            - done.
            - simpl. lia.
            - simpl. rewrite /fmap. lia. }
          { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
            iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
            rewrite shift_loc_assoc.
            replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
            eauto. }
          iMod "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
          (* destruct the head *)
          iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
          injection Heq0 as [= <-].
          rewrite /UninitLtype. simp_ltypes. rewrite Tauto.if_same.
          rewrite ltype_own_ofty_unfold /lty_of_ty_own.
          iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & >(%v0 & Hl0 & Hb0))".
          move: Halg0. simp_ltypes. intros Halg0.
          assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
          iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
          iExists (v0 ++ v1). rewrite heap_pointsto_app.
          iSplitL "Hl0 Hl1".
          { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
            rewrite Hly0'. done. }
          iSplitR. { iPureIntro. rewrite length_app Hv1_len Hly0'. done. }
          iSplitL "Hb0 Hrfn0".
          { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
            rewrite -Hly0'. rewrite take_app_length. done. }
          rewrite -Hly0'. rewrite drop_app_length. done.
  Qed.

  Lemma struct_t_unfold_1_uniq {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%ly & %Hst & %Hly & %Hsc & #Hlb & Hrfn & ? & Hb)". simpl in Hst.
    apply use_layout_alg_struct_Some_inv in Hst as (sl & Hst & ->).
    iExists sl. iSplitR; first done.
    (* NOTE: here we really need the ty_sidecond; we would not be able to just extract this info out from under the borrow! *)
    iSplitR. { rewrite Hsc. done. }
    iSplitR; first done.
    iSplitR; first done.
    iFrame. iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv.
    iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false false with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false true with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
  Qed.

  Local Lemma struct_t_unfold_1' {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl' k r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    destruct k.
    - iApply struct_t_unfold_1_owned.
    - iApply struct_t_unfold_1_shared.
    - iApply struct_t_unfold_1_uniq.
  Qed.

  Local Lemma ltype_core_hmap_ofty {rts : list RT} (tys : hlist type rts) :
    @ltype_core _ _ +<$> ((λ _, OfTy) +<$> tys) = ((λ _, OfTy) +<$> tys).
  Proof.
    induction tys as [ | rt rts ty tys IH]; simpl; first done. f_equiv. { simp_ltypes. done. } eapply IH.
  Qed.

  Lemma struct_t_unfold_1 {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl k r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    + iApply struct_t_unfold_1'.
    + simp_ltypes. rewrite ltype_core_hmap_ofty. by iApply struct_t_unfold_1'.
  Qed.

  Lemma struct_t_unfold_2_owned {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) wl r :
    ⊢ ltype_incl' (Owned wl) r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hsc & %Hly & #Hlb & ? & %r' & Hrfn & Hb)".
    iExists sl. iSplitR. { iPureIntro. eapply use_struct_layout_alg_Some_inv. done. }
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iModIntro. iFrame. iNext. iMod "Hb".
    specialize (struct_layout_field_aligned _ _ Hly) as Hfield_ly.
    (* generalize *)
    (* TODO mostly duplicated with the Uniq lemma above *)
    rewrite /ty_own_val /=.
    setoid_rewrite bi.sep_exist_l. rewrite bi_exist_comm.
    iExists sl. symmetry in Hsc. iFrame "%".
    rewrite /has_layout_val {1 2}/ly_size {1 2}/layout_of /=.
    specialize (struct_layout_spec_has_layout_fields_length _ _ Halg).
    remember (sl_members sl) as slm eqn:Heqslm.
    remember (sls_fields sls) as slsm eqn:Heqslsm.
    clear Heqslsm Heqslm Halg sls r sl Hly => Hlen.

    iInduction (slm) as [ | [m ly] slm] "IH" forall (l slsm rts tys r' Hsc Hlen Hfield_ly); simpl.
    { iExists [].
      iSplitR. { iApply heap_pointsto_nil. iApply loc_in_bounds_shorten_suf; last done. lia. }
      iSplitR; first done. iModIntro. done. }
    rewrite -Hsc in Hlen.
    iDestruct "Hb" as "(Hb0 & Hb)".
    destruct m as [ m | ].
    --  simpl in Hlen. destruct rts as [ | rt rts]; first done.
        simpl in Hsc, Hlen. destruct slsm as [ | st slsm]; first done.
        inv_hlist tys => ty tys. destruct r' as [r0 r]. simpl.
        (* use the IH *)
        iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r).
        simpl in *.
        iSpecialize ("IH" with "[] [] [] [] [Hb]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. intros k ly' Hlook.
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eapply (Hfield_ly (S k)). done. }
        { iModIntro.
          iApply loc_in_bounds_offset; last done.
          - done.
          - simpl. lia.
          - simpl. rewrite /fmap. lia. }
        { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
          iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eauto. }
        iMod "IH".
        iDestruct "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
        (* destruct the head *)
        iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
        injection Heq0 as [= <-].
        simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & >(%v0 & Hl0 & Hb0))".
        move: Halg0. simp_ltypes. intros Halg0.
        assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
        iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
        iModIntro.
        iExists (v0 ++ v1). rewrite heap_pointsto_app.
        iSplitL "Hl0 Hl1".
        { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
          rewrite Hly0'. done. }
        iSplitR. { iPureIntro. rewrite length_app Hv1_len Hly0'. done. }
        iSplitL "Hb0 Hrfn0".
        { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
          rewrite -Hly0'. rewrite take_app_length. done. }
        rewrite -Hly0'. rewrite drop_app_length. done.
    -- simpl in Hlen. simpl.
       (* use the iH *)
        iSpecialize ("IH" $! (l +ₗ ly_size ly) slsm rts tys r').
        simpl in *.
        iSpecialize ("IH" with "[] [] [] [] [Hb]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. intros k ly' Hlook.
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eapply (Hfield_ly (S k)). done. }
        { iModIntro.
          iApply loc_in_bounds_offset; last done.
          - done.
          - simpl. lia.
          - simpl. rewrite /fmap. lia. }
        { iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
          iIntros "!>" (k [rt1 [lt1 r1]] Hlook).
          rewrite shift_loc_assoc.
          replace ((ly_size ly + offset_of_idx slm k)%Z) with (Z.of_nat (ly_size ly + offset_of_idx slm k)%nat)by lia.
          eauto. }
        iMod "IH".
        iDestruct "IH" as "(%v1 & Hl1 & %Hv1_len & Hb)".
        (* destruct the head *)
        iDestruct "Hb0" as "(%ly0 & %Heq0 & %Halg0 & Hb0)".
        injection Heq0 as [= <-].
        rewrite /UninitLtype. simp_ltypes.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iDestruct "Hb0" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & _ & %r0' & Hrfn0 & >(%v0 & Hl0 & Hb0))".
        move: Halg0. simp_ltypes. intros Halg0.
        assert (ly0 = ly) as -> by by eapply syn_type_has_layout_inj.
        iPoseProof (ty_own_val_has_layout with "Hb0") as "#%Hly0'"; first done.
        iExists (v0 ++ v1). rewrite heap_pointsto_app.
        iSplitL "Hl0 Hl1".
        { rewrite /offset_of_idx. simpl. rewrite shift_loc_0_nat. iFrame "Hl0".
          rewrite Hly0'. done. }
        iSplitR. { iPureIntro. rewrite length_app Hv1_len Hly0'. done. }
        iSplitL "Hb0 Hrfn0".
        { iExists _, ly. iFrame. iSplitR; first done. iSplitR; first done.
          rewrite -Hly0'. rewrite take_app_length. done. }
        rewrite -Hly0'. rewrite drop_app_length. done.
  Qed.

  Lemma struct_t_unfold_2_shared {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) κ r :
    ⊢ ltype_incl' (Shared κ) r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iModIntro. iIntros (π l).
    rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & #Hlb & %r' & Hrfn & #Hb)".
    iExists sl. iSplitR. { iPureIntro. by eapply use_struct_layout_alg_Some_inv. }
    iSplitR; first done. iSplitR; first done. iFrame "Hlb".
    iExists r'. iFrame "Hrfn". iModIntro. iMod "Hb".

    rewrite /ty_shr /=. do 3 iR.
    rewrite -big_sepL_fupd.
    rewrite hpzipl_hmap.
    set (f := (λ '(existT x (a, b)), existT x (◁ a, b))%I).
    rewrite (pad_struct_ext _ _ _ (λ ly, f $ struct_make_uninit_type ly)); last done.
    rewrite pad_struct_fmap big_sepL_fmap.
    iApply (big_sepL_wand with "Hb").
    iApply big_sepL_intro. iIntros "!>" (k [rt0 [ty0 r0]] Hlook).
    iIntros "(%ly & %Hmem & %Hst & Hb)". simpl in *.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly0 & %Hst0 & %Hly0 & Hsc0 & Hlb0 & %r0' & Hrfn0 & #>#Hb)".
    iModIntro. iExists r0', ly0.
    move: Hst. simp_ltypes => Hst. assert (ly0 = ly) as ->. { by eapply syn_type_has_layout_inj. }
    iFrame "# ∗". iSplit; done.
  Qed.

  Lemma struct_t_unfold_2_uniq {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iModIntro. iIntros (π l). rewrite ltype_own_struct_unfold ltype_own_ofty_unfold /lty_of_ty_own /struct_ltype_own.
    iIntros "(%sl & %Hst & %Hlen & %Hly & #Hlb & Hrfn & ? & Hb)".
    iExists sl.
    iSplitR. { iPureIntro. eapply use_struct_layout_alg_Some_inv; done. }
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    iFrame "∗". iMod "Hb". iModIntro.
    setoid_rewrite ltype_own_core_equiv.
    iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false false with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
    + iNext. iModIntro.
      iPoseProof (unfold_case_uniq _ _ _ _ _ _ false true with "Hlb") as "[Ha1 Ha2]"; [reflexivity | done.. | ].
      iSplit; done.
  Qed.

  Local Lemma struct_t_unfold_2' {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl' k r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    destruct k.
    - iApply struct_t_unfold_2_owned.
    - iApply struct_t_unfold_2_shared.
    - iApply struct_t_unfold_2_uniq.
  Qed.
  Lemma struct_t_unfold_2 {rts : list RT} (tys : hlist type rts) (sls : struct_layout_spec) k r :
    ⊢ ltype_incl k r r (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    + iApply struct_t_unfold_2'.
    + simp_ltypes. rewrite ltype_core_hmap_ofty. iApply struct_t_unfold_2'.
  Qed.

  Lemma struct_t_unfold {rts} (tys : hlist type rts) sls k r :
    ⊢ ltype_eq k r r (◁ (struct_t sls tys))%I (StructLtype (hmap (λ _, OfTy) tys) sls).
  Proof.
    iSplit.
    - iApply struct_t_unfold_1.
    - iApply struct_t_unfold_2.
  Qed.

  Lemma struct_t_unfold_full_eqltype' E L {rts} (tys : hlist type rts) lts sls :
    (Forall (λ ltp, full_eqltype E L (projT2 ltp).1 (◁ (projT2 ltp).2)%I) (hzipl2 rts lts tys)) →
    full_eqltype E L (StructLtype lts sls) (◁ (struct_t sls tys))%I.
  Proof.
    iIntros (Heq ?) "HL #CTX #HE".
    iAssert ([∗ list] ltp ∈ hzipl2 rts lts tys, ∀ k r, ltype_eq k r r (projT2 ltp).1 (◁ (projT2 ltp).2)%I)%I with "[HL]" as "Ha".
    { iInduction rts as [ | rt rts] "IH"; first done.
      inv_hlist tys. inv_hlist lts. intros lt lts ty tys.
      rewrite hzipl2_cons. rewrite Forall_cons. intros [Heq Heqs].
      iPoseProof (Heq with "HL CTX HE") as "#Heq".
      iPoseProof ("IH" with "[//] HL") as "Heqs".
      iFrame. simpl. done. }
    iIntros (b r).
    iApply (ltype_eq_trans with "[Ha]"); last (iApply ltype_eq_sym; iApply struct_t_unfold).
    iApply (struct_ltype_eq lts).
    iIntros (k). rewrite hzipl2_fmap_r big_sepL_fmap.
    iApply (big_sepL_impl with "Ha").
    iModIntro. iIntros (? [? []] ?) "Ha".
    iIntros (r'). iApply "Ha".
  Qed.

  Lemma struct_t_unfold_full_eqltype E L {rts} (tys : hlist type rts) sls :
    (*full_eqltype E L lt (◁ ty)%I →*)
    full_eqltype E L (StructLtype (hmap (λ _, OfTy) tys) sls) (◁ (struct_t sls tys))%I.
  Proof.
    iIntros (?) "HL #CTX #HE". iIntros (b r).
    iApply ltype_eq_sym.
    iApply struct_t_unfold.
  Qed.
End unfold.

Section place.
  Context `{!typeGS Σ}.

  (* needs to have lower priority than the id instance *)
  Lemma typed_place_ofty_struct {rts} π E L l (tys : hlist type rts) (r : place_rfnRT (plistRT rts)) sls bmin0 b P T :
    typed_place π E L l (StructLtype (hmap (λ _, OfTy) tys) sls) r bmin0 b P T
    ⊢ typed_place π E L l (◁ (struct_t sls tys)) r bmin0 b P T.
  Proof.
    iIntros "Hp". iApply typed_place_eqltype; last iFrame.
    iIntros (?) "HL CTX HE".
    iIntros (??). iApply struct_t_unfold.
  Qed.
  Definition typed_place_ofty_struct_inst := [instance @typed_place_ofty_struct].
  Global Existing Instance typed_place_ofty_struct_inst | 30.
End place.

Section stratify.
  Context `{!typeGS Σ}.

  Lemma stratify_ltype_ofty_struct {rts} π E L mu ma {M} (ml : M) l (tys : hlist type rts) (r : place_rfn (plist place_rfnRT rts)) sls b T :
    stratify_ltype π E L mu StratDoUnfold ma ml l (StructLtype (hmap (λ _, OfTy) tys) sls) r b T
    ⊢ stratify_ltype π E L mu StratDoUnfold ma ml l (◁ (struct_t sls tys)) r b T.
  Proof.
    iIntros "Hp". iApply stratify_ltype_eqltype; iFrame.
    iPureIntro. iIntros (?) "HL CTX HE".
    iApply struct_t_unfold.
  Qed.
  Global Instance stratify_ltype_ofty_struct_inst {rts} π E L mu ma {M} (ml : M) l (tys : hlist type rts) (r : place_rfn (plist place_rfnRT rts)) sls b :
    StratifyLtype π E L mu StratDoUnfold ma ml l (◁ (struct_t sls tys))%I r b | 30 :=
        λ T, i2p (stratify_ltype_ofty_struct π E L mu ma ml l tys r sls b T).
End stratify.

Section cast.
  Context `{!typeGS Σ}.

  (** CastLtypeToType *)
  Definition hlist_list_of {A} {F : A → RT} (l : list A) (hl : hlist F l) := l.
  Fixpoint cast_ltype_to_type_iter (E : elctx) (L : llctx) {rts : list RT} (lts : hlist ltype rts) : (hlist type rts → iProp Σ) → iProp Σ :=
    match lts with
    | +[] => λ T, T +[]
    | lt +:: lts => λ T,
        cast_ltype_to_type E L lt (λ ty,
          cast_ltype_to_type_iter E L lts (λ tys, T (ty +:: tys)))
    end.

  Local Lemma cast_ltype_to_type_iter_elim E L {rts} (lts : hlist ltype rts) T :
    cast_ltype_to_type_iter E L lts T -∗
    ∃ tys : hlist type rts, T tys ∗ ⌜Forall (λ '(existT x (lt1, lt2)), full_eqltype E L lt1 lt2) (hzipl2 rts lts ((λ X : RT, OfTy) +<$> tys))⌝.
  Proof.
    iIntros "HT".
    iInduction rts as [ | rt rts] "IH"; inv_hlist lts; simpl.
    { iExists _. iFrame. iPureIntro. done. }
    intros lt lts. simpl.
    iDestruct "HT" as "(%ty & %Heqt & HT)".
    iPoseProof ("IH" with "HT") as "(%tys & HT & %Heqts)".
    iExists _. iFrame. iPureIntro. simpl. econstructor; done.
  Qed.
  Lemma cast_ltype_to_type_struct E L {rts} (lts : hlist ltype rts) sls T :
    cast_ltype_to_type_iter E L lts (λ tys, T (struct_t sls tys))
    ⊢ cast_ltype_to_type E L (StructLtype lts sls) T.
  Proof.
    iIntros "HT".
    (*Search "struct" "eq".*)
    iPoseProof (cast_ltype_to_type_iter_elim with "HT") as "(%tys & HT & %Heqts)".
    iExists _. iFrame. iPureIntro.
    etrans; first last.
    { refine (struct_t_unfold_full_eqltype _ _ _ _). }
    refine (struct_full_eqltype _ _ lts _ _ _).
    eapply Forall_impl; first apply Heqts. intros [? []]; done.
  Qed.
  Global Instance cast_ltype_to_type_struct_inst E L {rts} (lts : hlist ltype rts) sls  :
    CastLtypeToType E L (StructLtype lts sls) := λ T, i2p (cast_ltype_to_type_struct E L lts sls T).
End cast.

Global Typeclasses Opaque cast_ltype_to_type_iter.
