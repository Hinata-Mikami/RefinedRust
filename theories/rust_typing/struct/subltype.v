From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** ** Lemmas about [StructLtype] *)

Section subltype.
  Context `{!typeGS Σ}.
  Local Lemma pad_struct_hpzipl_2_inv {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) (rs1 : plist place_rfnRT rts1) (rs2 : plist place_rfnRT rts2) sl f k lt1 lt2 :
    length rts1 = length rts2 →
    pad_struct (sl_members sl) (hpzipl rts1 lts1 rs1) f !! k = Some lt1 →
    pad_struct (sl_members sl) (hpzipl rts2 lts2 rs2) f !! k = Some lt2 →
    (∃ rt1 rt2 lt1' lt2' r1 r2,
      lt1 = existT rt1 (lt1', r1) ∧ lt2 = existT rt2 (lt2', r2) ∧
      hpzipl _ lts1 rs1 !! field_idx_of_idx (sl_members sl) k = Some (existT rt1 (lt1', r1)) ∧
      hpzipl _ lts2 rs2 !! field_idx_of_idx (sl_members sl) k = Some (existT rt2 (lt2', r2))) ∨
    (∃ ly, lt1 = f ly ∧ lt2 = f ly).
  Proof.
    intros Hlen Hlook1 Hlook2.
    apply pad_struct_lookup_Some_1 in Hlook1.
    destruct Hlook1 as (n & ly & Hmem & Hlook1).
    destruct Hlook1 as [ [ ? Hlook1] | Hlook1].
    - apply pad_struct_lookup_Some_1 in Hlook2.
      destruct Hlook2 as (n' & ly' & Hmem' & Hlook2). simplify_eq.
      destruct Hlook2 as [ (_ & Hlook2) | (Hc & _) ]; first last.
      { destruct Hc as [ | Hc]; first done.
        exfalso. apply lookup_lt_Some in Hlook1.
        move: Hc Hlook1. rewrite !length_hpzipl. lia. }
      destruct lt1 as [rt1 [lt1 r1]]. destruct lt2 as [rt2 [lt2 r2]].
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook1) as Hrt1.
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook2) as Hrt2.
      left. eauto 10.
    - destruct Hlook1 as (Hnone & ->).
      erewrite pad_struct_lookup_field_None_2 in Hlook2; [ | done | reflexivity | ]; first last.
      { move : Hnone. rewrite !length_hpzipl Hlen. done. }
      injection Hlook2 as [= <-]. eauto.
  Qed.
  Local Lemma pad_struct_hpzipl_2_inv' {rts} (lts1 lts2 : hlist ltype rts) (rs : plist place_rfnRT rts) sl f k lt1 lt2 :
    pad_struct (sl_members sl) (hpzipl rts lts1 rs) f !! k = Some lt1 →
    pad_struct (sl_members sl) (hpzipl rts lts2 rs) f !! k = Some lt2 →
    (∃ rt lt1' lt2' r,
      lt1 = existT rt (lt1', r) ∧ lt2 = existT rt (lt2', r) ∧
      hzipl2 rts lts1 lts2 !! field_idx_of_idx (sl_members sl) k = Some (existT rt (lt1', lt2'))) ∨
    (∃ ly, lt1 = f ly ∧ lt2 = f ly).
  Proof.
    intros Hlook1 Hlook2.
    apply pad_struct_lookup_Some_1 in Hlook1.
    destruct Hlook1 as (n & ly & Hmem & Hlook1).
    destruct Hlook1 as [ [ ? Hlook1] | Hlook1].
    - apply pad_struct_lookup_Some_1 in Hlook2.
      destruct Hlook2 as (n' & ly' & Hmem' & Hlook2). simplify_eq.
      destruct Hlook2 as [ (_ & Hlook2) | (Hc & _) ]; first last.
      { destruct Hc as [ | Hc]; first done.
        exfalso. apply lookup_lt_Some in Hlook1.
        move: Hc Hlook1. rewrite !length_hpzipl. lia. }
      destruct lt1 as [rt1 [lt1 r1]]. destruct lt2 as [rt2 [lt2 r2]].
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook1) as Hrt1.
      specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook2) as Hrt2.
      rewrite Hrt1 in Hrt2. injection Hrt2 as [= <-].
      specialize (hpzipl_hzipl2_lookup _ _ _ _ _ _ _ _ _ Hlook1 Hlook2) as Hlook. simpl in Hlook.
      specialize (hpzipl_hpzipl_lookup_2_eq _ _ _ _ _ _ _ _ _ _ Hlook1 Hlook2) as ->.
      eauto 10.
    - destruct Hlook1 as (Hnone & ->).
      erewrite pad_struct_lookup_field_None_2 in Hlook2; [ | done | reflexivity | ]; first last.
      { move : Hnone. rewrite !length_hpzipl. done. }
      injection Hlook2 as [= <-]. eauto.
  Qed.

  Local Lemma struct_ltype_incl'_shared_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) κ' rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2,
      ltype_incl (Shared κ') (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl' (Shared κ') #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iPoseProof (big_sepL2_length with "Heq") as "%Hlen".
    rewrite !length_hpzipl in Hlen.
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen1 & %Hly & Hlb & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)". iExists rs2. iFrame.
    iDestruct "Hb" as "#Hb". iDestruct "Hrfn" as "<-". iSplitR; first done.
    iModIntro. iMod "Hb". iModIntro.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv _ _ _ _ _ _ _ _ _ Hlen Hlook1 Hlook2) as
      [ (rt1 & rt2 & lt1' & lt2' & r1 & r2 & -> & -> & Hlook1' & Hlook2') | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL2_lookup with "Heq") as "Hb"; [done.. | ]. simpl.
    iDestruct "Hb" as "(%Hst & #Hb & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iApply "Hb".
  Qed.
  Lemma struct_ltype_incl_shared_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) κ' rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2,
      ltype_incl (Shared κ') (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl (Shared κ') #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_shared_in).
    - done.
    - rewrite !hpzipl_hmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
        iIntros (k [rt1 [lt1 r1]] [rt2 [lt2 r2]] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_shared {rts} (lts1 lts2 : hlist ltype rts) κ' rs sls :
    (([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Shared κ') r r (projT2 ltp).1 (projT2 ltp).2)) -∗
    ltype_incl' (Shared κ') rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & Hb)".
    iExists sl. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)". iExists r'. iFrame.
    iDestruct "Hb" as "#Hb".
    iModIntro. iMod "Hb". iModIntro.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
      [ (rt & lt1' & lt2' & r & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
    iDestruct ("Hb" $! r) as "(%Hst & #Hb' & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iApply "Hb'".
  Qed.
  Lemma struct_ltype_incl_shared {rts} (lts1 lts2 : hlist ltype rts) κ' rs sls :
    ([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Shared κ') r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl (Shared κ') rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_shared).
    - done.
    - rewrite hzipl2_fmap big_sepL_fmap. iApply (big_sepL_mono with "Heq").
      iIntros (k [rt [lt1 lt2]] ?). simpl.
      iIntros "Heq" (r). iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_owned_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) wl rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ (hpzipl _ lts1 rs1); hpzipl _ lts2 rs2,
      ltype_incl (Owned false) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl' (Owned wl) #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iPoseProof (big_sepL2_length with "Heq") as "%Hlen". rewrite !length_hpzipl in Hlen.
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen1 & %Hly & Hlb & ? & Hb)".
    iExists sl. iR. rewrite -Hlen. iR. iR. iFrame.
    iDestruct "Hb" as "(%r' & <- & Hb)". iExists rs2. iSplitR; first done.
    iModIntro. iNext. iMod "Hb". rewrite -big_sepL_fupd.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv _ _ _ _ _ _ _ _ _ Hlen Hlook1 Hlook2) as
      [ (rt1 & rt2 & lt1' & lt2' & r1 & r2 & -> & -> & Hlook1' & Hlook2') | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL2_lookup with "Heq") as "Hb"; [done.. | ]. simpl.
    iDestruct "Hb" as "(%Hst & #Hb & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iMod ("Hb" with "Hc").
  Qed.
  Lemma struct_ltype_incl_owned_in {rts1 rts2} (lts1 : hlist ltype rts1) (lts2 : hlist ltype rts2) wl rs1 rs2 sls :
    ([∗ list] lt1; lt2 ∈ hpzipl _ lts1 rs1; hpzipl _ lts2 rs2,
      ltype_incl (Owned false) (projT2 lt1).2 (projT2 lt2).2 (projT2 lt1).1 (projT2 lt2).1) -∗
    ltype_incl (Owned wl) #rs1 #rs2 (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_owned_in).
    - done.
    - rewrite !hpzipl_hmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
        iIntros (k [rt1 [lt1 r1]] [rt2 [lt2 r2]] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_owned {rts} (lts1 lts2 : hlist ltype rts) wl rs sls :
    (([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Owned false) r r (projT2 ltp).1 (projT2 ltp).2)) -∗
    ltype_incl' (Owned wl) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & ? & Hb)".
    iExists sl. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iDestruct "Hb" as "(%r' & Hrfn & Hb)". iExists r'. iFrame.
    iModIntro. iNext. iMod "Hb". rewrite -big_sepL_fupd.
    iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
    iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
    destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
      [ (rt & lt1' & lt2' & r & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
    simpl. iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
    iDestruct ("Hb" $! r) as "(%Hst & #Hb' & _)".
    iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
    by iApply "Hb'".
  Qed.
  Lemma struct_ltype_incl_owned {rts} (lts1 lts2 : hlist ltype rts) wl rs sls :
    ([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_incl (Owned false) r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl (Owned wl) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_owned).
    - done.
    - rewrite hzipl2_fmap big_sepL_fmap. iApply (big_sepL_mono with "Heq").
      iIntros (k [rt [lt1 lt2]] ?). simpl.
      iIntros "Heq" (r). iApply ltype_incl_core; done.
  Qed.

  Local Lemma struct_ltype_incl'_uniq {rts} (lts1 lts2 : hlist ltype rts) κ γ rs sls :
    (([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq (Owned false) r r (projT2 ltp).1 (projT2 ltp).2)) -∗
    ltype_incl' (Uniq κ γ) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iModIntro.
    iIntros (π l).
    rewrite !ltype_own_struct_unfold /struct_ltype_own.
    iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & ? & Hrfn & Hb)".
    iExists sl. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iMod "Hb". iModIntro. iApply (pinned_bor_iff with "[] [] Hb").
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "((%Hst & #Hb' & _) & _)".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        by iApply "Hb'".
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook2 Hlook1) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "(_ & (%Hst & #Hb' & _))".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        by iApply "Hb'".
    + iNext. iModIntro. iSplit.
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook1 Hlook2) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "((%Hst & _ & #Hb') & _)".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        rewrite !ltype_own_core_equiv. by iApply "Hb'".
      * iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "Hb".
        iApply big_sepL_fupd.
        iApply (big_sepL_impl' with "Hb"). { rewrite !pad_struct_length //. }
        iModIntro. iIntros (k lt1 lt2 Hlook1 Hlook2).
        destruct (pad_struct_hpzipl_2_inv' _ _ _ _ _ _ _ _ Hlook2 Hlook1) as
          [ (rt & lt1' & lt2' & r0 & -> & -> & Hlook) | (ly & -> & ->)]; last by eauto.
        simpl.
        iPoseProof (big_sepL_lookup with "Heq") as "Hb"; first done. simpl.
        iDestruct ("Hb" $! _) as "(_ & (%Hst & _ & #Hb'))".
        iIntros "(%ly & ? & ? & Hc)". iExists ly. rewrite Hst. iFrame.
        rewrite !ltype_own_core_equiv. by iApply "Hb'".
  Qed.
  Lemma struct_ltype_incl_uniq {rts} (lts1 lts2 : hlist ltype rts) κ γ rs sls :
    ([∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq (Owned false) r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl (Uniq κ γ) rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplitR; first done. iModIntro.
    simp_ltypes.
    iSplit; (iApply struct_ltype_incl'_uniq).
    - done.
    - rewrite hzipl2_fmap big_sepL_fmap. iApply (big_sepL_mono with "Heq").
      iIntros (k [rt [lt1 lt2]] ?). simpl.
      iIntros "Heq" (r). iApply ltype_eq_core; done.
  Qed.

  Lemma struct_ltype_incl {rts} (lts1 lts2 : hlist ltype rts) k rs sls :
    (∀ k, [∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_incl k rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    destruct k.
    - iApply (struct_ltype_incl_owned lts1 lts2) .
      iApply (big_sepL_wand with "Heq"). iApply big_sepL_intro.
      iIntros "!>" (? [rt [lt1 lt2]] ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply struct_ltype_incl_shared.
      iApply (big_sepL_wand with "Heq"). iApply big_sepL_intro.
      iIntros "!>" (? [rt [lt1 lt2]] ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply struct_ltype_incl_uniq. done.
  Qed.
  Lemma struct_ltype_eq {rts} (lts1 lts2 : hlist ltype rts) k rs sls :
    (∀ k, [∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2) -∗
    ltype_eq k rs rs (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    iIntros "#Heq".
    iSplit.
    - iApply (struct_ltype_incl lts1 lts2); done.
    - iApply struct_ltype_incl. iIntros (k').
      iSpecialize ("Heq" $! k').
      rewrite hzipl2_swap big_sepL_fmap.
      iApply (big_sepL_wand with "Heq").
      iApply big_sepL_intro. iIntros "!>" (? [? []] ?) "Heq'".
      iIntros (?). iApply ltype_eq_sym. done.
  Qed.

  Lemma struct_full_subltype E L {rts} (lts1 lts2 : hlist ltype rts) sls :
    Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2) →
    full_subltype E L (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    intros Hsub.
    iIntros (qL) "HL #CTX #HE".
    iAssert (∀ k, [∗ list] ltp ∈ (hzipl2 rts lts1 lts2),
      ∀ r, ltype_eq k r r (projT2 ltp).1 (projT2 ltp).2)%I with "[HL]" as "#Heq".
    { iIntros (k). iInduction rts as [ | rt rts] "IH"; first done.
      inv_hlist lts1 => lt1 lts1. inv_hlist lts2 => lt2 lts2.
      rewrite hzipl2_cons. rewrite Forall_cons.
      intros [Heq Heqs].
      iPoseProof (Heq with "HL CTX HE") as "#Heq".
      iPoseProof ("IH" with "[//] HL") as "Heqs".
      iApply big_sepL_cons. iFrame. done.
    }
    iIntros (k r). iApply (struct_ltype_incl lts1 lts2). done.
  Qed.
  Lemma struct_full_eqltype E L {rts} (lts1 lts2 : hlist ltype rts) sls :
    Forall (λ lts, full_eqltype E L (projT2 lts).1 (projT2 lts).2) (hzipl2 rts lts1 lts2) →
    full_eqltype E L (StructLtype lts1 sls) (StructLtype lts2 sls).
  Proof.
    intros Hsub.
    apply full_subltype_eqltype. { refine (struct_full_subltype _ _ lts1 lts2 _ _). done. }
    apply (struct_full_subltype _ _ lts2 lts1).
    rewrite hzipl2_swap. rewrite Forall_fmap.
    eapply Forall_impl; first done.
    intros [rt []]; naive_solver.
  Qed.
End subltype.


Section lemmas.
  Context `{!typeGS Σ}.

  (** Focusing lemmas for pad_struct big_seps *)
  Lemma focus_struct_component {rts} (lts : hlist ltype rts) (r : plist place_rfnRT rts) sl π k l i x rto lto ro :
    field_index_of (sl_members sl) x = Some i →
    hpzipl rts lts r !! i = Some (existT rto (lto, ro)) →
    (* assume the big sep of components *)
    ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) (λ ly, existT (unit : RT) (UninitLtype (UntypedSynType ly), PlaceIn ())),
      ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
      (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1) -∗
    ⌜rto = lnth (unit : RT) rts i⌝ ∗
    (* get the component *)
    ∃ ly : layout, ⌜syn_type_has_layout (ltype_st lto) ly⌝ ∗ (l at{sl}ₗ x) ◁ₗ[ π, k] ro @ lto ∗
    (* for any strong update, get the corresponding big_sep back *)
    (∀ rt' lt' r',
      (l at{sl}ₗ x) ◁ₗ[ π, k] r' @ lt' -∗
      ⌜syn_type_has_layout (ltype_st lt') ly⌝ -∗
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl (<[i := rt']> rts) (hlist_insert rts lts i rt' lt') (plist_insert rts r i rt' r')) (λ ly, existT (unit : RT) (UninitLtype (UntypedSynType ly), PlaceIn ())),
        ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
        (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1)) ∧
    (* alternatively, for any weak (non-rt-changing) update: *)
    (∀ (lt' : ltype (lnth (unit : RT) rts i)) (r' : place_rfn (lnth (unit : RT) rts i)),
      (l at{sl}ₗ x) ◁ₗ[ π, k] r' @ lt' -∗
       ⌜syn_type_has_layout (ltype_st lt') ly⌝ -∗
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl (rts) (hlist_insert_id (unit : RT) rts lts i lt') (plist_insert_id (unit : RT) rts r i r')) (λ ly, existT (unit : RT) (UninitLtype (UntypedSynType ly), PlaceIn ())),
        ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
        (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1)).
  Proof.
    iIntros (Hfield Hlook) "Hb".
    edestruct (field_index_of_to_index_of _ _ _ Hfield) as (j & Hindex).
    iPoseProof (big_sepL_insert_acc with "Hb") as "((%ly & %Hly & %Hst & Hl) & Hclose)".
    { eapply pad_struct_lookup_field_Some_2'; done. }
    specialize (hpzipl_lookup_inv _ _ _ _ _ _ _ Hlook) as Hlook'.
    simpl. iSplitR. { eapply lookup_lnth in Hlook'. done. }
    iExists ly. iSplitR; first done.
    rewrite /GetMemberLoc /offset_of Hindex. simpl. iFrame.
    iSplit.
    - iIntros (rt' lt' r') "He %Hst'".
      set (ra := existT (P := λ rt, (ltype rt * place_rfn rt)%type) rt' (lt', r')).
      iSpecialize ("Hclose" $! ra with "[He]").
      { iExists ly. iSplitR; first done. iSplitR; done. }
      erewrite pad_struct_insert_field; [ | done | done | ].
      2: { eapply lookup_lt_Some. done. }
      rewrite insert_hpzipl. done.
    - iIntros (lt' r') "He %Hst'".
      set (ra := existT (P := λ rt, (ltype rt * place_rfn rt)%type) _ (lt', r')).
      iSpecialize ("Hclose" $! ra with "[He]").
      { iExists ly. iSplitR; first done. iSplitR; done. }
      erewrite pad_struct_insert_field; [ | done | done | ].
      2: { eapply lookup_lt_Some. done. }
      rewrite insert_hpzipl.
      enough (hpzipl rts (hlist_insert_id (unit : RT) rts lts i lt') (plist_insert_id (unit : RT) rts r i r') =
        (hpzipl (<[i:=lnth (unit : RT) rts i]> rts) (hlist_insert rts lts i (lnth (unit : RT) rts i) lt') (plist_insert rts r i (lnth (unit : RT) rts i) r'))) as -> by done.
      unfold hlist_insert_id, plist_insert_id.
      generalize (list_insert_lnth rts (unit : RT) i).
      intros <-. done.
  Qed.

  (** Focus the initialized fields of a struct, disregarding the padding fields *)
  Lemma struct_ltype_focus_components π {rts : list RT} (lts : hlist ltype rts) (rs : plist place_rfnRT rts) sls sl k l :
    length rts = length (sls_fields sls) →
    struct_layout_spec_has_layout sls sl →
    ([∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts lts rs) struct_make_uninit_ltype,
       ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗
         ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
         (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1) -∗
    (* we get access to the named fields *)
    ([∗ list] i↦p ∈ hpzipl rts lts rs, let 'existT rt (lt, r) := p in ∃ (name : var_name) (st : syn_type), ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ l atst{sls}ₗ name ◁ₗ[ π, k] r @ lt) ∗
    (* we can update the named fields: *)
    (∀ (rts' : list RT) (lts' : hlist ltype rts') rs',
      (* syn types need to be the same *)
      ⌜length rts = length rts'⌝ -∗
      (⌜Forall2 (λ p p2, let 'existT rt (lt, _) := p in let 'existT rt' (lt', _) := p2 in ltype_st lt = ltype_st lt') (hpzipl rts lts rs) (hpzipl rts' lts' rs')⌝)  -∗
      (* ownership *)
      ([∗ list] i↦p ∈ hpzipl rts' lts' rs', let 'existT rt (lt, r) := p in ∃ (name : var_name) (st : syn_type), ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ l atst{sls}ₗ name ◁ₗ[ π, k] r @ lt) -∗
      (* we get back the full struct ownership *)
      ([∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' rs') struct_make_uninit_ltype,
       ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗
         ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
         (l +ₗ offset_of_idx (sl_members sl) i) ◁ₗ[ π, k] (projT2 ty).2 @ (projT2 ty).1)).
  Proof.
    iIntros (Hlen Halg) "Hl".
    iPoseProof (pad_struct_focus_no_uninit with "Hl") as "(Hl & Hl_cl)".
    { rewrite length_hpzipl. rewrite named_fields_field_names_length (struct_layout_spec_has_layout_fields_length sls); done. }
    { specialize (sl_nodup sl). rewrite bool_decide_spec. done. }
    (* remember the layouts *)
    iAssert ([∗ list] i↦x ∈ hpzipl rts lts rs, ∃ (ly : layout) (n : string), ⌜named_fields (sl_members sl) !! i = Some (n, ly)⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 x).1) ly⌝)%I with "[Hl]" as "%Hly_agree".
    { iApply (big_sepL_impl with "Hl").
      iModIntro. iIntros (j [rt [lt r]] Hlook).
      iIntros "(%j' & %ly & %n & %Hmem & %Hnamed & %ly' & %Hmem' & %Hst & Hl)".
      rewrite Hmem in Hmem'. simpl in *. injection Hmem' as <-.
      specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
      eapply Forall2_lookup_r in Halg2; last done.
      destruct Halg2 as ([n' st'] & Hfields & Hst' & <-).
      rewrite Hnamed. iExists _, _. done. }

    iSplitL "Hl".
    { iApply (big_sepL_impl with "Hl").
      iModIntro. iIntros (j [rt [lt r]] Hlook).
      iIntros "(%j' & %ly & %n & %Hmem & %Hnamed & %ly' & %Hmem' & %Hst & Hl)".
      rewrite Hmem in Hmem'. simpl in *. injection Hmem' as <-.
      specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
      eapply Forall2_lookup_r in Halg2; last done.
      destruct Halg2 as ([n' st'] & Hfields & Hst' & <-).
      iExists _, _. rewrite /GetMemberLocSt.
      rewrite /use_struct_layout_alg'.
      iR. rewrite Halg. simpl.
      rewrite /offset_of.
      erewrite sl_index_of_lookup_2; last done.
      done. }
   iIntros (rts' lts' rs') "%Hlen_eq %Hst Hb".
   iApply "Hl_cl". { rewrite !length_hpzipl//. }

   iApply (big_sepL_impl with "Hb").
   iModIntro. iIntros (ka [rt [lt r]] Hlook) "(%n & %st & %Hst' & Hl)".
   simpl.
   specialize (struct_layout_spec_has_layout_lookup sls sl n _ _ Halg Hst') as Hidx.
   specialize (struct_layout_spec_has_layout_alt_2 _ _ Halg) as Halg2.
   eapply Forall2_lookup_l in Halg2 as ([n' ly'] & Hlook' & Hly); last done.
   simpl in Hly. destruct Hly as (Hly & ->).
   specialize (named_fields_lookup_1 _ _ _ _ Hlook') as (ka' & Hlook'').

   eapply Forall2_lookup_r in Hst; last done.
   destruct Hst as ([rt' [lt' r']] & Hlook2 & Hst).
   rewrite -Hst.
   eapply Hly_agree in Hlook2 as (ly2 & n2 & Hlook2 & Hst2).
   simpl in *. rewrite Hlook' in Hlook2. injection Hlook2 as [= <- <-].
   iExists ka',  ly', n. iR. iR.
   iExists _. rewrite Hlook''. iR. iR.
   rewrite /GetMemberLocSt /use_struct_layout_alg' Halg /=.
   rewrite /offset_of. erewrite sl_index_of_lookup_2; done.
  Qed.
End lemmas.

Section accessors.
  Context `{!typeGS Σ}.

  Local Lemma lift_eq {rts rts'} (lts : hlist ltype rts) (lts' : hlist ltype rts') :
    Forall2 (λ lt lt' : sigT ltype, projT1 lt = projT1 lt')
      (hzipl rts lts) (hzipl rts' lts') →
    rts = rts'.
  Proof.
    induction rts as [ | rt rts IH] in rts', lts, lts' |-*; destruct rts' as [ | rt' rts']; inv_hlist lts; inv_hlist lts'; simpl.
    - done.
    - intros ?? ?%Forall2_nil_inv_l; done.
    - intros ?? ?%Forall2_nil_inv_r; done.
    - intros ???? [Heq1 Heq2%IH]%Forall2_cons_inv.
      simpl in Heq1. rewrite -Heq1 -Heq2//.
  Qed.


  (** Note: regrettably, this does not allow us to just preserve one component trivially.
    This is due to the way how mutable references of products are setup.
    Effectively, this means that our place access lemmas for products will have some sideconditions on when borrows beneath other components will end.
    TODO is there are smarter setup for this? (e.g. by tracking this as a sidecondition in ltypes so that it does not need to reproved over and over again?)
  *)
  Import EqNotations.
  Lemma struct_ltype_place_cond b {rts rts'} (lts : hlist ltype rts) (lts' : hlist ltype rts') sls :
    ([∗ list] lt; lt' ∈ hzipl rts lts; hzipl rts' lts',
      typed_place_cond b (projT2 lt) (projT2 lt')) -∗
    typed_place_cond b (StructLtype lts sls) (StructLtype lts' sls).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Hrel".
      iPoseProof (big_sepL2_Forall2 with "Hrel") as "%Heq".
      iPureIntro. f_equiv.
      by eapply lift_eq.
    - iIntros "Hrel".
      iPoseProof (big_sepL2_impl _ (λ _ lt1 lt2, ⌜projT1 lt1 = projT1 lt2⌝)%I with "Hrel []") as "#Hx".
      { iModIntro. iIntros (?????). iIntros "(%Heq & Ha)". done. }
      iPoseProof (big_sepL2_Forall2 with "Hx") as "%Heq". iClear "Hx".
      apply lift_eq in Heq. subst rts'.
      iExists eq_refl.
      setoid_rewrite <-bi.sep_exist_r.
      rewrite big_sepL2_sep_sepL_r. iDestruct "Hrel" as "(#Heq & #Hub)".
      iSplitL.
      + cbn. simp_ltypes. iIntros (k r). iApply struct_ltype_eq. iIntros (k').
        rewrite hzipl2_fmap big_sepL_fmap.
        rewrite (big_sepL2_hzipl_hzipl_sepL_hzipl2 _ _ _
          (λ _ a b, ∃ Heq, ∀ k r, ltype_eq k r r (ltype_core $ projT2 a) (ltype_core $ rew <-[ltype] Heq in projT2 b))%I
          (λ _ ltp, ∀ k r, ltype_eq k r r (ltype_core (projT2 ltp).1) (ltype_core (projT2 ltp).2))%I 0).
        { iApply big_sepL_mono; last done. iIntros (? [? [??]] ?). eauto. }
        intros _ x a b. iSplit.
        * iIntros "(%Heq & Heq)". rewrite (UIP_refl _ _ Heq). done.
        * iIntros "Heq". iExists eq_refl. done.
      + iApply struct_ltype_imp_unblockable. done.
  Qed.

  Lemma struct_ltype_acc_owned {rts} F π (lts : hlist ltype rts) (r : plist place_rfnRT rts) l sls wl :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] #r @ StructLtype lts sls -∗
    ∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length sls.(sls_fields) = length rts⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗ |={F}=>
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) ∗
      logical_step F
      (∀ rts' (lts' : hlist ltype rts') (r' : plist place_rfnRT rts'),
        (* the number of fields should remain equal *)
        ⌜length rts' = length rts⌝ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) ={F}=∗
        l ◁ₗ[π, Owned wl] #r' @ StructLtype lts' sls).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hb" as "(%sl & %Halg & %Hlen & %Hly & #Hlb & Hcred & %r' & -> & Hb)".
    iExists sl. iFrame "#%".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_maybe with "Hat"). iIntros "Hcred' !>".
    iIntros (rts' lts' r) "%Hlen_eq Hb".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iExists sl. rewrite Hlen_eq. by iFrame "%#∗".
  Qed.

  Definition sigT_ltype_core : (sigT (λ rt, ltype rt * place_rfn rt)%type) → (sigT (λ rt, ltype rt * place_rfn rt)%type) := λ '(existT _ (lt, r)), existT _ (ltype_core lt, r).
  Local Lemma pad_struct_pull_core {rts} (lts : hlist ltype rts) (rs : plist place_rfnRT rts) fields (Φ : nat → (sigT (λ rt, ltype rt * place_rfn rt)%type) → iProp Σ) :
    ([∗ list] i↦ty ∈ pad_struct fields (hpzipl rts (@ltype_core Σ typeGS0 +<$> lts) rs) struct_make_uninit_ltype, Φ i ty)%I ⊣⊢
    ([∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts rs) struct_make_uninit_ltype, Φ i (sigT_ltype_core ty))%I.
  Proof.
    rewrite hpzipl_hmap.
    rewrite (pad_struct_ext _ _ _ (λ ly, sigT_ltype_core (struct_make_uninit_ltype ly))); first last.
    { intros ly. simpl. rewrite ltype_core_uninit. reflexivity. }
    rewrite (pad_struct_fmap _ _ _ sigT_ltype_core) big_sepL_fmap.
    done.
  Qed.
  Lemma ltype_core_sigT_ltype_core_idemp ty :
    ltype_core ((projT2 $ sigT_ltype_core ty).1) = (projT2 $ sigT_ltype_core ty).1.
  Proof.
    destruct ty as [? []]; simpl. rewrite ltype_core_idemp //.
  Qed.
  Lemma ltype_st_sigT_ltype_core ty :
    ltype_st ((projT2 $ sigT_ltype_core ty).1) = ltype_st (projT2 ty).1.
  Proof.
    destruct ty as [? []]; simpl. rewrite ltype_core_syn_type_eq //.
  Qed.

  Local Lemma typed_place_cond_uniq_core_eq_struct {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) κs :
    ([∗ list] ty1; ty2 ∈ hzipl rts lts1; hzipl rts lts2,
      typed_place_cond (UpdUniq κs) (projT2 ty1) (projT2 ty2)) -∗
    ([∗ list] ty ∈ hzipl2 rts lts1 lts2,
      ∀ b' r, ltype_eq b' r r (ltype_core (projT2 ty).1) (ltype_core (projT2 ty).2)).
  Proof.
    iIntros "Hcond".
    iPoseProof (big_sepL2_to_zip with "Hcond") as "Hcond".
    rewrite zip_hzipl_hzipl2 big_sepL_fmap.
    iApply (big_sepL_impl with "Hcond"). iModIntro. iIntros (? [rt [lt1 lt2]] Hlook).
    iApply typed_place_cond_uniq_core_eq.
  Qed.
  Local Lemma typed_place_cond_uniq_unblockable_struct {rts} (lts1 : hlist ltype rts) (lts2 : hlist ltype rts) κs :
    ([∗ list] ty1; ty2 ∈ hzipl rts lts1; hzipl rts lts2,
      typed_place_cond (UpdUniq κs) (projT2 ty1) (projT2 ty2)) -∗
    ([∗ list] ty ∈ hzipl2 rts lts1 lts2,
      imp_unblockable κs (projT2 ty).2).
  Proof.
    iIntros "Hcond".
    iPoseProof (big_sepL2_to_zip with "Hcond") as "Hcond".
    rewrite zip_hzipl_hzipl2 big_sepL_fmap.
    iApply (big_sepL_impl with "Hcond").
    iModIntro. iIntros (? [rt [lt1 lt2]] Hlook).
    iApply typed_place_cond_uniq_unblockable.
  Qed.

  Local Lemma struct_acc_uniq_elems_core π l {rts} (lts lts' : hlist ltype rts) (rs : plist place_rfnRT rts) fields :
    length (field_names fields) = length rts →
    ([∗ list] ty ∈ hzipl2 rts lts lts',
      ∀ b' r, ltype_eq b' r r (ltype_core (projT2 ty).1) (ltype_core (projT2 ty).2)) -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts rs) struct_make_uninit_ltype,
      ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ ltype_core (projT2 ty).1)) -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts' rs) struct_make_uninit_ltype,
        ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ ltype_core (projT2 ty).1)).
  Proof.
    iIntros (Ha) "#Hcond >Hb". iApply big_sepL_fupd.
    iApply big_sepL2_elim_l.
    iPoseProof (big_sepL_extend_r with "Hb") as "Hb"; first last.
    { iApply (big_sepL2_impl with "Hb").
      iModIntro. iIntros (? [? []] [? []] Hlook1 Hlook2).
      simpl. iIntros "(%ly & ? & ? & Hl)".
      apply pad_struct_lookup_Some in Hlook1 as (n & ly1 & Hlook & Hlook1); first last.
      { rewrite length_hpzipl Ha. lia. }
      destruct Hlook1 as [(? & Hlook1) | (-> & Hlook1)].
      - apply (hpzipl_lookup_inv_hzipl_pzipl _ _ rs) in Hlook1 as (Hlook1 & Hlook1').
        destruct n; last done.
        eapply pad_struct_lookup_Some_Some in Hlook2; cycle -2.
        { rewrite length_hpzipl Ha. lia. }
        { done. }
        apply (hpzipl_lookup_inv_hzipl_pzipl _ _ rs) in Hlook2 as (Hlook2 & Hlook2').
        rewrite Hlook1' in Hlook2'. injection Hlook2' => Heq1 ?. subst.
        apply existT_inj in Heq1 as ->.
        iPoseProof (big_sepL_lookup with "Hcond")as "Heq".
        { apply hzipl_hzipl2_lookup; done. }
        (*iPoseProof (typed_place_cond_incl _ (Uniq κ γ) with "Hincl_k Hcond'") as "Hcond''".*)
        iDestruct ("Heq" $! (Owned _) _) as "((%Hst1 & #Heq1 & _) & (_ & #Heq2 & _))".
        (*setoid_rewrite ltype_own_core_equiv. *)
        iPoseProof ("Heq1" with "Hl") as "Hb".
        simpl in Hst1. rewrite !ltype_core_syn_type_eq in Hst1.
        iMod "Hb". iModIntro. rewrite Hst1. cbn. eauto with iFrame.
      - injection Hlook1 => Hlook1_1 Hlook1_2 ?. subst.
        apply existT_inj in Hlook1_2. apply existT_inj in Hlook1_1. subst.
        eapply pad_struct_lookup_Some_None in Hlook2; cycle 1.
        { rewrite length_hpzipl Ha. lia. }
        { done. }
        injection Hlook2 => Hlook2_1 Hlook2_2 ?. subst.
        apply existT_inj in Hlook2_1. apply existT_inj in Hlook2_2. subst.
        eauto with iFrame.
    }
    rewrite !pad_struct_length //.
  Qed.

  (* transition the struct to the core *)
  Local Lemma struct_acc_uniq_elems_unblock π l {rts} (lts lts' : hlist ltype rts) (rs : plist place_rfnRT rts) fields κs :
    length (field_names fields) = length rts →
    ([∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts lts',
      typed_place_cond (UpdUniq κs) (projT2 ty1) (projT2 ty2)) -∗
    lft_dead_list κs -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts' rs) struct_make_uninit_ltype,
      ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ (projT2 ty).1)) -∗
    ((|={lftE}=> [∗ list] i↦ty ∈ pad_struct fields (hpzipl rts lts rs) struct_make_uninit_ltype,
        ∃ ly : layout, ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ (l +ₗ offset_of_idx fields i) ◁ₗ[ π, Owned false] (projT2 ty).2 @ ltype_core (projT2 ty).1)).
  Proof.
    iIntros (Ha) "#Hcond #Hdead >Hb". iApply big_sepL_fupd.
    iApply big_sepL2_elim_l.
    iPoseProof (big_sepL_extend_r with "Hb") as "Hb"; first last.
    { iApply (big_sepL2_impl with "Hb").
      iModIntro. iIntros (? [? []] [? []] Hlook1 Hlook2).
      simpl. iIntros "(%ly & ? & ? & Hl)".
      apply pad_struct_lookup_Some in Hlook1 as (n & ly1 & Hlook & Hlook1); first last.
      { rewrite length_hpzipl Ha. lia. }
      destruct Hlook1 as [(? & Hlook1) | (-> & Hlook1)].
      - apply (hpzipl_lookup_inv_hzipl_pzipl _ _ rs) in Hlook1 as (Hlook1 & Hlook1').
        destruct n; last done.
        eapply pad_struct_lookup_Some_Some in Hlook2; cycle -2.
        { rewrite length_hpzipl Ha. lia. }
        { done. }
        apply (hpzipl_lookup_inv_hzipl_pzipl _ _ rs) in Hlook2 as (Hlook2 & Hlook2').
        rewrite Hlook1' in Hlook2'. injection Hlook2' => Heq1 ?. subst.
        apply existT_inj in Heq1 as ->.
        iPoseProof (typed_place_cond_uniq_core_eq_struct _ _ κs with "Hcond") as "Heq".
        iPoseProof (typed_place_cond_uniq_unblockable_struct _ _ κs with "Hcond") as "Hub".

        iPoseProof (big_sepL_lookup with "Heq") as "Heq1".
        { apply hzipl_hzipl2_lookup; done. }
        iPoseProof (big_sepL_lookup with "Hub") as "Hub1".
        { apply hzipl_hzipl2_lookup; done. }
        cbn.
        iMod (imp_unblockable_use with "Hub1 Hdead Hl") as "Hl"; first done.
        iDestruct ("Heq1" $! (Owned _) _) as "((%Hst1 & #Heq1' & _) & (_ & #Heq2 & _))".
        iMod ("Heq2" with "Hl") as "Hl".
        rewrite !ltype_core_syn_type_eq in Hst1.
        rewrite -Hst1.
        eauto with iFrame.
      - injection Hlook1 => Hlook1_1 Hlook1_2 ?. subst.
        apply existT_inj in Hlook1_2. apply existT_inj in Hlook1_1. subst.
        eapply pad_struct_lookup_Some_None in Hlook2; cycle 1.
        { rewrite length_hpzipl Ha. lia. }
        { done. }
        injection Hlook2 => Hlook2_1 Hlook2_2 ?. subst.
        apply existT_inj in Hlook2_1. apply existT_inj in Hlook2_2. subst.
        setoid_rewrite ltype_core_uninit. eauto with iFrame.
    }
    rewrite !pad_struct_length //.
  Qed.

  Lemma struct_ltype_acc_uniq {rts} F π (lts : hlist ltype rts) (r : plist place_rfnRT rts) l sls κ γ q R :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #r @ StructLtype lts sls -∗
    ∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length sls.(sls_fields) = length rts⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗ |={F}=>
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
        (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) ∗
      logical_step F
      (((* weak access *)
        ∀ bmin (lts' : hlist ltype rts) (r' : plist place_rfnRT rts),
        bmin ⪯ₚ UpdUniq [κ] -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) -∗
        ([∗ list] ty1; ty2 ∈ hzipl rts lts; hzipl rts lts',
          typed_place_cond (bmin) (projT2 ty1) (projT2 ty2)) ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #r' @ StructLtype lts' sls ∗
        R ∗
        typed_place_cond bmin (StructLtype lts sls) (StructLtype lts' sls)) ∧
      ((* strong access, go to OpenedLtype *)
        ∀ rts' (lts' : hlist ltype rts') (r' : plist place_rfnRT rts'),
        (* same number of fields *)
        ⌜length rts' = length rts⌝ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Owned false] (projT2 ty).2 @ (projT2 ty).1) -∗
        l ◁ₗ[π, Uniq κ γ] PlaceIn r' @ OpenedLtype (StructLtype lts' sls) (StructLtype lts sls) (StructLtype lts sls)
            (λ ri ri', ⌜ri = ri'⌝) (λ _ _, R))).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Hκ HR Hb". rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hb" as "(%sl & %Halg & %Hlen & %Hly & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    iExists sl. iFrame "#%".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    (* NOTE: we are currently throwing away the existing "coring"-viewshift that we get *)
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Hκ") as "(%κ'' & #Hincl & Hb & _ & Hb_cl)"; first done.
    iMod "Hcl_F" as "_".
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' &  Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat".
    iModIntro.
    iSplit.
    - (* close *)
      iIntros (bmin lts' rs') "#Hincl_k Hl #Hcond".
      iMod (gvar_update rs' with "Hauth Hrfn") as "(Hauth & Hrfn)".
      set (V := (∃ r', gvar_auth γ r' ∗
        (|={lftE}=> [∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗ ltype_own (projT2 ty).1 (Owned false) π (projT2 ty).2 (l +ₗ offset_of_idx (sl_members sl) i)))%I).
      iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      opose proof* struct_layout_spec_has_layout_fields_length as Ha; first done.
      iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hl]") as "(Hb & Htok)".
      { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
        iModIntro. iNext. iExists r'. iFrame "Hauth".
        rewrite Hlen in Ha. clear -Ha.
        iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
        setoid_rewrite ltype_own_core_equiv.
        iApply (struct_acc_uniq_elems_unblock with "[Hcond] [Hdead] Hb").
        { done. }
        { iApply (big_sepL2_impl with "Hcond").
          iModIntro. iIntros (? [] [] ? ?).
          iApply typed_place_cond_incl; done. }
        by iApply lft_dead_list_singleton.
      }
      { iModIntro. rewrite /V. iExists rs'. iFrame. eauto 8 with iFrame. }
      iMod ("HR" with "Htok") as "$".
      iMod "Hcl_F" as "_".
      iModIntro.
      (* TODO maybe donate the leftover credits *)
      iSplitL.
      { rewrite ltype_own_struct_unfold /struct_ltype_own.
        iExists sl. iFrame. do 4 iR.
        iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
        iModIntro. subst V.
        (* need to adapt the pinned part, too *)
        iApply (pinned_bor_iff with "[] [] Hb").
        { iNext. iModIntro. eauto. }
        iNext. iModIntro.
        setoid_rewrite ltype_own_core_equiv.
        iAssert ([∗ list] ty1;ty2 ∈ hzipl rts lts;hzipl rts lts', typed_place_cond (UpdUniq [κ]) (projT2 ty1) (projT2 ty2))%I with "[Hcond]" as "Ha".
        { iApply (big_sepL2_impl with "Hcond"). iModIntro. iIntros (k [] [] ? ?). by iApply typed_place_cond_incl. }
        iSplit.
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb".
          iApply (struct_acc_uniq_elems_core with "[] Hb"); [ lia | ].
          iApply typed_place_cond_uniq_core_eq_struct.
          iApply (big_sepL2_impl with "Hcond").
          iModIntro. iIntros (? [] [] ? ?). iApply (typed_place_cond_incl with "Hincl_k").
        - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb".
          iApply (struct_acc_uniq_elems_core with "[] Hb"); [ lia | ].
          rewrite hzipl2_swap big_sepL_fmap.
          iPoseProof (typed_place_cond_uniq_core_eq_struct with "Ha") as "Hb".
          iApply (big_sepL_impl with "Hb").
          iModIntro. iIntros (? [? []] ?) "Heq" => /=.
          iIntros (??). iApply ltype_eq_sym. iApply "Heq".
      }
      iApply (struct_ltype_place_cond _ _ lts' sls with "Hcond").
    - (* shift to OpenedLtype *)
      iIntros (rts' lts' rs') "%Hlen' Hl".
      iDestruct "Hcred" as "(Hcred1 & Hcred)".
      iApply (opened_ltype_create_uniq_simple with "Hrfn Hauth Hcred1 Hat Hincl HR Hb_cl [] [Hcred']"); first done.
      { iModIntro. iIntros (?) "Hauth Hc". simp_ltypes.
        rewrite ltype_own_struct_unfold /struct_ltype_own.
        iExists _. iFrame. iDestruct "Hc" as ">(%sl' & %Hsl' & _ & _ & _ & _ & %r' & -> & >Hb)".
        assert (sl' = sl) as ->. { rewrite Halg in Hsl'. injection Hsl' as ->. done. }
        iModIntro. setoid_rewrite ltype_own_core_equiv.

        rewrite pad_struct_pull_core. iApply (big_sepL_impl with "Hb").
        iModIntro. iIntros (? [? []] ?). simpl. rewrite ltype_core_syn_type_eq. eauto. }
      { iIntros (?) "Hobs Hat Hcred Hp". simp_ltypes.
        rewrite ltype_own_struct_unfold /struct_ltype_own.
        setoid_rewrite ltype_own_core_equiv.
        iModIntro. iExists sl. iFrame "% ∗". iR.
        iModIntro.
        setoid_rewrite pad_struct_pull_core.
        setoid_rewrite ltype_core_sigT_ltype_core_idemp.
        setoid_rewrite ltype_st_sigT_ltype_core.
        iApply (pinned_bor_iff with "[] [] Hp").
        - iNext. iModIntro. iSplit.
          all: iIntros "(%r'' & ? & Hb)"; iExists r''; iFrame;
            iMod "Hb"; iModIntro; iApply (big_sepL_impl with "Hb");
            iIntros "!>" (? [? []] ?); eauto.
        - iNext. iModIntro. iSplit.
          all: iIntros "(%r'' & ? & Hb)"; iExists r''; iFrame;
            iMod "Hb"; iModIntro; iApply (big_sepL_impl with "Hb");
            iIntros "!>" (? [? []] ?); eauto. }
      { rewrite ltype_own_struct_unfold /struct_ltype_own.
        iExists sl. iFrame "% ∗". rewrite Hlen'. by do 3 iR. }
  Qed.

  Lemma struct_ltype_acc_shared {rts} F π (lts : hlist ltype rts) (r : plist place_rfnRT rts) l sls κ :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] #r @ StructLtype lts sls -∗
    ∃ sl, ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length sls.(sls_fields) = length rts⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗ |={F}=>
      ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts lts r) struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Shared κ] (projT2 ty).2 @ (projT2 ty).1) ∗
      (∀ rts' (lts' : hlist ltype rts') (r' : plist place_rfnRT rts'),
        (* the number of fields should remain equal *)
        ⌜length rts' = length rts⌝ -∗
        (* new ownership *)
        ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (hpzipl rts' lts' r') struct_make_uninit_ltype,
          ∃ ly : layout, ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            (l +ₗ offset_of_idx sl.(sl_members) i) ◁ₗ[π, Shared κ] (projT2 ty).2 @ (projT2 ty).1) ={F}=∗
        l ◁ₗ[π, Shared κ] #r' @ StructLtype lts' sls).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_struct_unfold /struct_ltype_own.
    iDestruct "Hb" as "(%sl & %Halg & %Hlen & %Hly & #Hlb & %r' & -> & #Hb)".
    iExists sl. iFrame "#%". iMod (fupd_mask_mono with "Hb") as "Hb'"; first done.
    iModIntro. iFrame.
    iIntros (rts' lts' r) "%Hlen_eq #Hb'".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    iExists sl. rewrite Hlen_eq. by iFrame "%#∗".
  Qed.
End accessors.
