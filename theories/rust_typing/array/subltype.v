From refinedrust Require Export type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** ** Properties of the [ArrayLtype] *)

Section subltype.
  Context `{!typeGS Σ}.

  Local Lemma array_ltype_incl_big_wand_in {rt1 rt2} k π F (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) rs1 rs2 l b ly :
    lftE ⊆ F →
    length rs1 = len → length rs2 = len →
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1;lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2, ltype_incl b lt1.2 lt2.2 lt1.1 lt2.1) -∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def1) len lts1;rs1, ⌜ltype_st lt = ty_syn_type def1⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt) ={F}=∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def2) len lts2;rs2, ⌜ltype_st lt = ty_syn_type def2⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt).
  Proof.
    iIntros (? Hlen1 Hlen2 Hstdef) "#Hincl Ha".
    iInduction len as [ | len] "IH" forall (k rs1 rs2 lts1 lts2 Hlen1 Hlen2); simpl.
    { destruct rs2; last done. rewrite !interpret_iml_0 //. }
    destruct rs2 as [ | r2 rs2]; first done.
    destruct rs1 as [ | r1 rs1]; first done.
    simpl.
    rewrite !interpret_iml_succ. simpl.
    iDestruct "Ha" as "((%Hsteq & Ha) & Hb)".
    iDestruct "Hincl" as "(Hincl1 & Hincl)".
    simpl in *.
    iSpecialize ("IH" $! (S k) with "[] [] Hincl [Hb]").
    { iPureIntro. lia. }
    { iPureIntro. lia. }
    { setoid_rewrite Nat.add_succ_r. done. }
    iMod "IH" as "IH".
    iPoseProof "Hincl1" as "(%Hst & _)".
    iMod (ltype_incl_use with "Hincl1 Ha") as "$"; first done.
    iSplitR. { rewrite -Hst -Hstdef. done. }
    setoid_rewrite Nat.add_succ_r. done.
  Qed.

  Local Lemma array_ltype_incl_big_wand {rt} k π F (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) rs l b ly :
    lftE ⊆ F →
    length rs = len →
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1;lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2, ∀ r, ltype_incl b r r lt1 lt2) -∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def1) len lts1;rs, ⌜ltype_st lt = ty_syn_type def1⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt) ={F}=∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def2) len lts2;rs, ⌜ltype_st lt = ty_syn_type def2⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ lt).
  Proof.
    iIntros (? Hlen Hstdef) "#Hincl Ha".
    iInduction len as [ | len] "IH" forall (k rs lts1 lts2 Hlen); simpl.
    { destruct rs; last done. rewrite !interpret_iml_0 //. }
    destruct rs as [ | r rs]; first done.
    simpl.
    rewrite !interpret_iml_succ. simpl.
    iDestruct "Ha" as "((%Hsteq & Ha) & Hb)".
    iDestruct "Hincl" as "(Hincl1 & Hincl)".
    simpl in *.
    setoid_rewrite Nat.add_succ_r.
    iSpecialize ("IH" $! (S k) rs with "[] Hincl Hb").
    { iPureIntro. lia. }
    iMod "IH" as "IH".
    iPoseProof ("Hincl1" $! r) as "(%Hst & _)".
    iMod (ltype_incl_use with "Hincl1 Ha") as "$"; first done.
    iSplitR. { rewrite -Hst -Hstdef. done. }
    done.
  Qed.
  Local Lemma array_ltype_incl_big_wand_core {rt} k π F (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) rs l b ly :
    lftE ⊆ F →
    length rs = len →
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1;lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2, ∀ r, ltype_incl b r r lt1 lt2) -∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def1) len lts1;rs, ⌜ltype_st lt = ty_syn_type def1⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ ltype_core lt) ={F}=∗
    ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def2) len lts2;rs, ⌜ltype_st lt = ty_syn_type def2⌝ ∗ (l offset{ly}ₗ (k + i)%nat) ◁ₗ[ π, b] r0 @ ltype_core lt).
  Proof.
    iIntros (? Hlen Hstdef) "#Hincl Ha".
    iMod (array_ltype_incl_big_wand _ _ _ _ _ _ ((λ '(a, b), (a, ltype_core b)) <$> lts1) ((λ '(a, b), (a, ltype_core b)) <$> lts2)  with "[] [Ha]") as "Ha".
    - done.
    - apply Hlen.
    - apply Hstdef.
    - iEval (rewrite -(ltype_core_ofty def1)). iEval (rewrite -(ltype_core_ofty def2)).
      rewrite !interpret_iml_fmap big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_impl with "Hincl").
      iModIntro. iIntros (??? Hlook1 Hlook2) "Ha".
      iIntros (?). by iApply ltype_incl_core.
    - iEval (rewrite -(ltype_core_ofty def1)).
      rewrite !interpret_iml_fmap big_sepL2_fmap_l. setoid_rewrite ltype_core_syn_type_eq. done.
    - iEval (rewrite -(ltype_core_ofty def2)) in "Ha".
      rewrite !interpret_iml_fmap big_sepL2_fmap_l. setoid_rewrite ltype_core_syn_type_eq. done.
  Qed.

  Local Lemma array_ltype_incl'_shared_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) κ' rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ ([∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Shared κ') (lt1).2 (lt2).2 (lt1).1 (lt2).1)) -∗
    ltype_incl' (Shared κ') #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & <- & #Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame. iExists rs2. iR.
    iModIntro. iMod "Ha" as "(%Hlen & Ha)".
    iPoseProof ("Hel" with "[//]") as "Hc".
    iDestruct "Hc" as "(%Hb & Hc)". iR.
    iMod (array_ltype_incl_big_wand_in 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_shared_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) κ' rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ [∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Shared κ') (lt1).2 (lt2).2 (lt1).1 (lt2).1) -∗
    ltype_incl (Shared κ') #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_shared_in; first done).
    - done.
    - iIntros (Hlen'). iSpecialize ("Heq" with "[//]"). iDestruct "Heq" as "($ & Heq)".
      rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite !zip_fmap_l.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k [lt1 r1] [lt2 r2] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_shared {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Shared κ') r r lt1 lt2) -∗
    ltype_incl' (Shared κ') rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & Hrfn & #Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame "Hlb". iExists r'. iFrame.
    iModIntro. iMod "Ha" as "(%Hlen & Ha)". iR.
    iMod (array_ltype_incl_big_wand 0 with "Hel Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_shared {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Shared κ') r r lt1 lt2) -∗
    ltype_incl (Shared κ') rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_shared; first done).
    - done.
    - rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k lt1 lt2 ??). simpl. iIntros "Ha" (?). iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_owned_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) wl rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ [∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Owned false) (lt1).2 (lt2).2 (lt1).1 (lt2).1) -∗
    ltype_incl' (Owned wl) #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & Hcred & %r' & <- & Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame. iExists rs2. iR.
    iModIntro. iNext. iMod "Ha" as "(%Hlen & Ha)".
    iPoseProof ("Hel" with "[//]") as "Hc".
    iDestruct "Hc" as "(%Hb & Hc)". iR.
    iMod (array_ltype_incl_big_wand_in 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_owned_in {rt1 rt2} (def1 : type rt1) (def2 : type rt2) len (lts1 : list (nat * ltype rt1)) (lts2 : list (nat * ltype rt2)) wl rs1 rs2 :
    ty_syn_type def1 = ty_syn_type def2 →
    (⌜length rs1 = len⌝ -∗ ⌜length rs2 = len⌝ ∗ [∗ list] lt1; lt2 ∈ zip (interpret_iml (◁ def1) len lts1) rs1; zip (interpret_iml (◁ def2) len lts2) rs2,
      ltype_incl (Owned false) (lt1).2 (lt2).2 (lt1).1 (lt2).1) -∗
    ltype_incl (Owned wl) #rs1 #rs2 (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_owned_in; first done).
    - done.
    - iIntros (Hlen'). iSpecialize ("Heq" with "[//]"). iDestruct "Heq" as "(% & Heq)". iR.
      rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite !zip_fmap_l.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k [lt1 r1] [lt2 r2] ??). simpl. iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_owned {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) wl rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Owned false) r r lt1 lt2) -∗
    ltype_incl' (Owned wl) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & Hcred & %r' & Hrfn & Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame "Hlb Hcred". iExists r'. iFrame.
    iModIntro. iNext. iMod "Ha" as "(%Hlen & Ha)". iR.
    iPoseProof ("Hel" with "") as "Hc".
    iMod (array_ltype_incl_big_wand 0 with "Hc Ha") as "Ha"; [done.. | ].
    done.
  Qed.
  Lemma array_ltype_incl_owned {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) wl rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_incl (Owned false) r r lt1 lt2) -∗
    ltype_incl (Owned wl) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_owned; first done).
    - done.
    - rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k lt1 lt2 ??). simpl. iIntros "Ha" (?). iApply ltype_incl_core; done.
  Qed.

  Local Lemma array_ltype_incl'_uniq {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' γ rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_eq (Owned false) r r lt1 lt2) -∗
    ltype_incl' (Uniq κ' γ) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Hel".
    iModIntro. iIntros (π l) "Ha".
    rewrite !ltype_own_array_unfold /array_ltype_own.
    iDestruct "Ha" as "(%ly & %Halg & %Hsz & %Hly & Hlb & ? & Hrfn & Ha)".
    iExists ly. iSplitR. { rewrite -Hst. done. }
    iR. iR. iFrame.
    iMod "Ha". iModIntro.
    iApply (pinned_bor_iff with "[] [] Ha"); iNext; iModIntro.
    - iSplit; iIntros "(%r' & ? & Ha)"; iExists _; iFrame "∗%"; iMod "Ha" as "(% & Ha)";
        (iMod (array_ltype_incl_big_wand 0 with "[Hel] Ha") as "Hx"; [done.. |  | iR; done]).
      + iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "($ & _)".
      + rewrite big_sepL2_flip.
        iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "(_ & $)".
    - iSplit; iIntros "(%r' & ? & Ha)"; iExists _; iFrame "∗%"; iMod "Ha" as "(% & Ha)".
      all: setoid_rewrite ltype_own_core_equiv.
      all: iMod (array_ltype_incl_big_wand_core 0 with "[Hel] Ha") as "Hx"; [done.. |  | iR; done ].
      + iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "($ & _)".
      + rewrite big_sepL2_flip.
        iApply (big_sepL2_mono with "Hel"). iIntros (?????) "Ha". iIntros (?). iDestruct ("Ha" $! _) as "(_ & $)".
  Qed.
  Lemma array_ltype_incl_uniq {rt} (def1 : type rt) (def2 : type rt) len (lts1 : list (nat * ltype rt)) (lts2 : list (nat * ltype rt)) κ' γ rs :
    ty_syn_type def1 = ty_syn_type def2 →
    ([∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_eq (Owned false) r r lt1 lt2) -∗
    ltype_incl (Uniq κ' γ) rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (Hst) "#Heq".
    iSplitR. { iPureIntro. simp_ltypes. rewrite Hst//. }
    iModIntro. simp_ltypes.
    iSplit; (iApply array_ltype_incl'_uniq; first done).
    - done.
    - rewrite -{2}(ltype_core_ofty def1) -{2}(ltype_core_ofty def2).
      rewrite !interpret_iml_fmap.
      rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "Heq").
      iIntros (k lt1 lt2 ??). simpl. iIntros "Ha" (?). iApply ltype_eq_core; done.
  Qed.

  Lemma array_ltype_incl {rt} (def1 def2 : type rt) len (lts1 lts2 : list (nat * ltype rt)) k rs :
    ty_syn_type def1 = ty_syn_type def2 →
    (∀ k, [∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2) len lts2,
      ∀ r, ltype_eq k r r lt1 lt2) -∗
    ltype_incl k rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (?) "#Heq".
    destruct k.
    - iApply array_ltype_incl_owned; first done.
      iApply (big_sepL2_wand with "Heq"). iApply big_sepL2_intro.
      { rewrite !length_interpret_iml//. }
      iIntros "!>" (? lt1 lt2 ? ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply array_ltype_incl_shared; first done.
      iApply (big_sepL2_wand with "Heq"). iApply big_sepL2_intro.
      { rewrite !length_interpret_iml//. }
      iIntros "!>" (? lt1 lt2 ? ?) "Ha". iIntros (r).
      iDestruct ("Ha" $! r) as "[$ _]".
    - iApply array_ltype_incl_uniq; done.
  Qed.

  Lemma array_ltype_eq {rt} (def1 def2 : type rt) (lts1 lts2 : list (nat * ltype rt)) len rs k :
    ty_syn_type def1 = ty_syn_type def2 →
    (∀ k, [∗ list] lt1; lt2 ∈ (interpret_iml (◁ def1) len lts1); (interpret_iml (◁ def2) len lts2),
      ∀ r, ltype_eq k r r lt1 lt2) -∗
    ltype_eq k rs rs (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    iIntros (?) "#Heq".
    iSplit.
    - iApply array_ltype_incl; done.
    - iApply array_ltype_incl; first done. iIntros (k').
      iSpecialize ("Heq" $! k').
      iApply big_sepL2_flip.
      iApply (big_sepL2_wand with "Heq").
      iApply big_sepL2_intro. { rewrite !length_interpret_iml//. }
      iIntros "!>" (? ?? ??) "Heq'".
      iIntros (?). iApply ltype_eq_sym. done.
  Qed.

  Lemma array_full_subltype E L {rt} (def1 def2 : type rt) (lts1 lts2 : list (nat * ltype rt)) len :
    ty_syn_type def1 = ty_syn_type def2 →
    Forall2 (λ lt1 lt2, full_eqltype E L lt1 lt2) (interpret_iml (◁ def1) len lts1)%I (interpret_iml (◁ def2)%I len lts2) →
    full_subltype E L (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    intros ? Hsub.
    iIntros (qL) "HL #CTX #HE".
    iAssert (∀ k, [∗ list] lt1; lt2 ∈ interpret_iml (◁ def1) len lts1; interpret_iml (◁ def2)%I len lts2,
      ∀ r, ltype_eq k r r lt1 lt2)%I with "[HL]" as "#Heq".
    { iIntros (k).
      iPoseProof (Forall2_big_sepL2 with "HL []") as "(Ha & HL)"; first apply Hsub.
      { rewrite !length_interpret_iml. done. }
      { iModIntro. iIntros (lt1 lt2) "HL %Heqt".
        iPoseProof (Heqt with "HL CTX HE") as "#Ha". iFrame "HL". iApply "Ha". }
      iApply (big_sepL2_mono with "Ha").
      iIntros (??? ??) "#Heq". iIntros (r). iApply "Heq". }
    iIntros (k r). iApply array_ltype_incl; done.
  Qed.
  Lemma array_full_eqltype E L {rt} (def1 def2 : type rt) len (lts1 lts2 : list (nat * ltype rt)) :
    ty_syn_type def1 = ty_syn_type def2 →
    Forall2 (λ lt1 lt2, full_eqltype E L lt1 lt2) (interpret_iml (◁ def1) len lts1)%I (interpret_iml (◁ def2)%I len lts2) →
    full_eqltype E L (ArrayLtype def1 len lts1) (ArrayLtype def2 len lts2).
  Proof.
    intros ? Hsub.
    apply full_subltype_eqltype; (eapply array_full_subltype; first done).
    - done.
    - rewrite Forall2_flip. eapply Forall2_impl; first done.
      intros ??; naive_solver.
  Qed.
End subltype.

Section to_default.
  Context `{!typeGS Σ}.

  Fixpoint delete_iml {X} i (iml : list (nat * X)) : list (nat * X) :=
    match iml with
    | [] => []
    | (j, x) :: iml => if decide (i = j) then delete_iml i iml else (j, x) :: delete_iml i iml
    end.

  Lemma array_ltype_make_default {rt} (def : type rt) len lts i lt1 b r1 r2 :
    (∀ b r, ltype_eq b r r lt1 (◁ def)) -∗
    ltype_incl b r1 r2 (ArrayLtype def len ((i, lt1) :: lts)) (ArrayLtype def len (delete_iml i lts)).
  Proof.

  Abort.

  (* can I get this just with ltype_incl?
      If the core of arrays was just ofty def, I could get it with some reasoning.
      Because I would just show that it collapses to the core.

    Now, I can't, because we need the core of all of these things.
      Should I change the definition?
    I guess then, when I write, I need to show that the core of the new thing is ◁ def.
     *)
  (*
  Lemma array_ltype_transform_iml {rt} (def : type rt) b r len lts :
    (∀ i,
      interpret_iml (◁ def)%I len lts1 !! i = Some lt1 →
      interpret_iml (◁ def)%I len lts2 !! i = Some lt2 →
      lt1 = lt2
    ([∗ list] lt ∈ interpret_iml (◁ def)%I len lts, ∀ b r, ltype_eq b r r lt (◁ def)) -∗
    ltype_incl b r r (ArrayLtype def len lts) (ArrayLtype def len []).
   *)

  Definition full_iml {A} (def : A) start len := (λ i, (i, def)%I) <$> seq start len.
  Lemma interpret_inserts_full_iml {A} iml' i def len (l : list A) :
    interpret_inserts (full_iml def i len ++ iml') l =
    take i (interpret_inserts iml' l) ++ replicate (min len (length l - i)) def ++ drop (i + len) (interpret_inserts iml' l).
  Proof.
    induction len as [ | len IH] in i, l |-*; simpl.
    { rewrite Nat.add_0_r. rewrite take_drop. done. }
    rewrite IH. simpl.
    destruct (decide (i < length l)) as [Hlt | Hnlt].
    - rewrite insert_app_l. 2: { rewrite length_take length_interpret_inserts. lia. }
      rewrite insert_take_drop. 2: { rewrite length_take length_interpret_inserts.  lia. }
      rewrite take_take. rewrite Nat.min_l; last lia.
      rewrite drop_ge; first last. { rewrite length_take. lia. }
      rewrite Nat.add_succ_r.
      rewrite -app_assoc.
      assert (length l - i = S (length l - S i)) as -> by lia.
      rewrite -Nat.succ_min_distr. done.
    - rewrite !Nat.min_r; [ | lia..].
      assert (length l - i = 0) as -> by lia.
      assert (length l - S i = 0) as -> by lia.
      simpl.
      rewrite drop_ge; first last. { rewrite length_interpret_inserts. lia. }
      rewrite drop_ge; first last. { rewrite length_interpret_inserts. lia. }
      rewrite !app_nil_r.
      rewrite !take_ge; [ | rewrite length_interpret_inserts; lia.. ].
      rewrite list_insert_id'; first done.
      rewrite length_interpret_inserts. lia.
  Qed.
  Lemma interpret_full_iml {A} (def : A) len iml' :
    interpret_iml def len (full_iml def 0 len ++ iml') = interpret_iml def len [].
  Proof.
    rewrite /interpret_iml. simpl.
    rewrite interpret_inserts_full_iml.
    rewrite take_0 length_replicate Nat.min_l; last lia.
    rewrite drop_ge; first by rewrite app_nil_r.
    rewrite length_interpret_inserts length_replicate. lia.
  Qed.

  Lemma array_ltype_make_defaults {rt} (def : type rt) b r len lts :
    ([∗ list] lt ∈ interpret_iml (◁ def)%I len lts, ∀ b r, ltype_eq b r r lt (◁ def)) -∗
    ltype_eq b r r (ArrayLtype def len lts) (ArrayLtype def len []).
  Proof.
    iIntros "#Hincl".
    iApply (array_ltype_eq with "[]"); first done.
    rewrite -(interpret_full_iml _ _ lts).
    iIntros (k). rewrite interpret_full_iml/=.
    rewrite big_sepL2_replicate_r; first last.
    { rewrite length_interpret_iml//. }
    iApply (big_sepL_impl with "Hincl").
    iModIntro. iIntros (?? Hlook) "Ha". iIntros (?). iApply "Ha".
  Qed.

  Lemma array_ltype_make_defaults_full_eqltype E L {rt} (def : type rt) len lts :
    Forall (λ lt, full_eqltype E L lt (◁ def)%I) (interpret_iml (◁ def)%I len lts) →
    full_eqltype E L (ArrayLtype def len lts) (ArrayLtype def len []).
  Proof.
    intros Ha. iIntros (?) "HL #CTX #HE". iIntros (??).
    iPoseProof (Forall_big_sepL with "HL []") as "(Ha & HL)"; first apply Ha.
    { iModIntro. iIntros (lt) "HL %Heqt". iPoseProof (Heqt with "HL CTX HE") as "#Heq".
      iFrame "HL". iApply "Heq". }
    iApply array_ltype_make_defaults.
    done.
  Qed.

  Lemma array_ltype_place_cond b {rt rt'} (def : type rt) (def' : type rt') (len : nat) (lts : list (nat * ltype rt)) (lts' : list (nat * ltype rt')) :
    place_access_rt_rel b rt rt' →
    ty_syn_type def = ty_syn_type def' →
    ([∗ list] lt; lt' ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def') len lts', typed_place_cond b lt lt') -∗
    typed_place_cond b (ArrayLtype def len lts) (ArrayLtype def' len lts').
  Proof.
    iIntros (Hrel Hst). destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Hrel".
      unfold typed_place_cond; simpl.
      unfold place_access_rt_rel in Hrel.
      iPureIntro. subst rt'. done.
    - iIntros "Hrel".
      simpl in Hrel. subst rt'.
      iExists eq_refl.
      setoid_rewrite <-bi.sep_exist_r.
      rewrite big_sepL2_sep_sepL_r. iDestruct "Hrel" as "(#Heq & #Hub)".
      iSplitL.
      + cbn. simp_ltypes. iIntros (k r). iApply array_ltype_eq; first done. iIntros (k').
        rewrite -{-1}(ltype_core_ofty def) -{-1}(ltype_core_ofty def').
        rewrite !interpret_iml_fmap. rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
        iApply (big_sepL2_mono with "Heq").
        iIntros (? lt1 lt2 Hlook1 Hlook2). iIntros "(%Heq & Ha)".
        rewrite (UIP_refl _ _ Heq). iIntros (?). iApply "Ha".
      + iApply array_ltype_imp_unblockable. done.
  Qed.
End to_default.

Section accessors.
  Context `{!typeGS Σ}.

  Lemma array_ltype_acc_owned_cred {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l wl :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs, ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt) ∗
      (∀ (rt' : RT) (def' : type rt') (lts' : list (nat * ltype rt')) (rs' : list (place_rfn rt')),
        (if wl then £1 else True) -∗
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs', ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Owned wl] #rs' @ ArrayLtype def' len lts').
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & Hcred & %r' & <- & Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & (<- & Hb))"; first done.
    iModIntro. iFrame.
    iIntros (rt' def' lts' rs') "Hcred' %Hst' Hb".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iModIntro.
    iExists ly. rewrite -Hst'. iR. iR. iR. iR.
    iSplitL "Hat Hcred Hcred'".
    { destruct wl; last done. iFrame. rewrite /num_cred. iApply lc_succ. iFrame. }
    iExists rs'. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hleneq".
    rewrite length_interpret_iml in Hleneq. iR.
    iNext. done.
  Qed.

  Lemma array_ltype_acc_owned {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l wl :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs, ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt) ∗
      logical_step F
      (∀ (rt' : RT) (def' : type rt') (lts' : list (nat * ltype rt')) (rs' : list (place_rfn rt')),
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs', ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Owned wl] #rs' @ ArrayLtype def' len lts').
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & Hcred & %r' & <- & Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & (<- & Hb))"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_maybe with "Hat"). iIntros "Hcred' !>".
    iIntros (rt' def' lts' rs') "%Hst' Hb".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iModIntro.
    iExists ly. rewrite -Hst'. iR. iR. iR. iR. iFrame "Hcred'".
    iExists rs'. iR.
    iPoseProof (big_sepL2_length with "Hb") as "%Hleneq".
    rewrite length_interpret_iml in Hleneq. iR.
    iNext. done.
  Qed.

  Local Lemma typed_place_cond_uniq_core_eq_array {rt} (def : type rt) (def' : type rt) lts lts' len κs :
    ([∗ list] ty1; ty2 ∈ interpret_iml (◁ def)%I len lts; interpret_iml (◁ def')%I len lts',
      typed_place_cond (UpdUniq κs) ty1 ty2) -∗
    ([∗ list] ty1; ty2 ∈ interpret_iml (◁ def)%I len lts; interpret_iml (◁ def')%I len lts',
      ∀ b' r, ltype_eq b' r r (ltype_core ty1) (ltype_core ty2)).
  Proof.
    iIntros "Hcond". iApply (big_sepL2_impl with "Hcond").
    iModIntro. iIntros (? lt1 lt2 Hlook1 Hlook2).
    iApply typed_place_cond_uniq_core_eq.
  Qed.
  Local Lemma typed_place_cond_uniq_unblockable_array {rt} (def : type rt) (def' : type rt) lts lts' len κs :
    ([∗ list] ty1; ty2 ∈ interpret_iml (◁ def)%I len lts; interpret_iml (◁ def')%I len lts',
      typed_place_cond (UpdUniq κs) ty1 ty2) -∗
    ([∗ list] ty1; ty2 ∈ interpret_iml (◁ def)%I len lts; interpret_iml (◁ def')%I len lts',
      imp_unblockable κs ty2).
  Proof.
    iIntros "Hcond". iApply (big_sepL2_impl with "Hcond").
    iModIntro. iIntros (? lt1 lt2 Hlook1 Hlook2).
    iApply typed_place_cond_uniq_unblockable.
  Qed.

  Local Lemma array_acc_uniq_elems_unblock π l {rt} len (def def' : type rt) ly lts lts' (rs : list (place_rfn rt)) κs :
    syn_type_has_layout (ty_syn_type def) ly →
    ty_syn_type def = ty_syn_type def' →
    ([∗ list] ty1;ty2 ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def')%I len lts', typed_place_cond (UpdUniq κs) ty1 ty2) -∗
    lft_dead_list κs -∗
    (|={lftE}=> [∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs, ⌜ ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[ π, Owned false] r0 @  lt) -∗
    |={lftE}=> [∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs, ⌜ ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[ π, Owned false] r0 @ ltype_core lt.
  Proof.
    iIntros (Hst Hst_eq) "#Hcond #Hdead >Hb". iApply big_sepL2_fupd.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen2". rewrite length_interpret_iml in Hlen2.
    iPoseProof (big_sepL2_to_zip with "Hb") as "Hb".
    iApply big_sepL2_from_zip. { rewrite length_interpret_iml. done. }
    iPoseProof (big_sepL_extend_r with "Hb") as "Hb"; first last.
    { iApply big_sepL2_elim_l. iApply (big_sepL2_impl with "Hb").
      iModIntro. iIntros (? [lt1 r1] [lt2 r2] Hlook1 Hlook2).
      simpl. iIntros "(%Hst1 & Hl)".
      apply lookup_zip in Hlook1 as (Hlook1 & Hlook1').
      apply lookup_zip in Hlook2 as (Hlook2 & Hlook2'). simpl in *.
      assert (r1 = r2) as -> by naive_solver.
      iPoseProof (typed_place_cond_uniq_core_eq_array _ _ _ _ _ κs with "Hcond") as "Heq".
      iPoseProof (typed_place_cond_uniq_unblockable_array _ _ _ _ _ κs with "Hcond") as "Hub".
      iPoseProof (big_sepL2_lookup with "Heq") as "Heq1"; [ done.. | ].
      iPoseProof (big_sepL2_lookup with "Hub") as "Hub1"; [ done.. | ].
      iMod (imp_unblockable_use with "Hub1 Hdead Hl") as "Hl"; first done.
      iDestruct ("Heq1" $! (Owned _) _) as "((%Hst1' & #Heq1' & _) & (_ & #Heq2 & _))".
      iMod ("Heq2" with "Hl") as "Hl".
      rewrite !ltype_core_syn_type_eq in Hst1'.
      rewrite -Hst1. eauto with iFrame.
    }
    rewrite !length_zip !length_interpret_iml//.
  Qed.
  Local Lemma array_acc_uniq_elems_core_eq π l {rt} len (def def' : type rt) ly lts lts' (rs : list (place_rfn rt)) :
    syn_type_has_layout (ty_syn_type def) ly →
    ty_syn_type def = ty_syn_type def' →
    ([∗ list] ty1;ty2 ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def')%I len lts',
      ∀ b' r, ltype_eq b' r r (ltype_core ty1) (ltype_core ty2)) -∗
    (|={lftE}=> [∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs,
      ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[ π, Owned false] r0 @ ltype_core lt) -∗
    |={lftE}=> [∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs,
      ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[ π, Owned false] r0 @ ltype_core lt.
  Proof.
    iIntros (Hst Hst_eq) "#Heq >Hb". iApply big_sepL2_fupd.
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen2". rewrite length_interpret_iml in Hlen2.
    iPoseProof (big_sepL2_to_zip with "Hb") as "Hb".
    iApply big_sepL2_from_zip. { rewrite length_interpret_iml. done. }
    iPoseProof (big_sepL_extend_r with "Hb") as "Hb"; first last.
    { iApply big_sepL2_elim_l. iApply (big_sepL2_impl with "Hb").
      iModIntro. iIntros (? [lt1 r1] [lt2 r2] Hlook1 Hlook2).
      simpl. iIntros "(%Hst1 & Hl)".
      apply lookup_zip in Hlook1 as (Hlook1 & Hlook1').
      apply lookup_zip in Hlook2 as (Hlook2 & Hlook2'). simpl in *.
      assert (r1 = r2) as -> by naive_solver.
      iPoseProof (big_sepL2_lookup with "Heq") as "Heq1"; [ done.. | ].
      iDestruct ("Heq1" $! (Owned _) _) as "((%Hst1' & #Heq1' & _) & (_ & #Heq2 & _))".
      iMod ("Heq1'" with "Hl") as "Hl".
      rewrite !ltype_core_syn_type_eq in Hst1'.
      rewrite -Hst1. eauto with iFrame.
    }
    rewrite !length_zip !length_interpret_iml//.
  Qed.

  Lemma array_ltype_acc_uniq {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l R q κ γ :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ R) -∗
    l ◁ₗ[π, Uniq κ γ] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs,
        ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt) ∗
      logical_step F
      (∀ (def' : type rt) (lts' : list (nat * ltype rt)) (rs' : list (place_rfn rt)) bmin,
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        ⌜len = length rs'⌝ -∗
        bmin ⪯ₚ UpdUniq [κ] -∗
        ([∗ list] ty1; ty2 ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def') len lts',
          typed_place_cond bmin ty1 ty2) -∗
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs',
          ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Owned false] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Uniq κ γ] #rs' @ ArrayLtype def' len lts' ∗
        R ∗
        typed_place_cond bmin (ArrayLtype def len lts) (ArrayLtype def' len lts')
        ).
  Proof.
    iIntros (?) "#(LFT & TIME & LLCTX) Htok Htokcl Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & Hcred & Hrfn & Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ'' & #Hincl & Hb & _ & Hb_cl)"; first done.
    iMod "Hcl_F" as "_".
    iDestruct "Hcred" as "((Hcred1 & Hcred) & Hat)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iMod (fupd_mask_mono with "Hb") as "(%Hlen & Hb)"; first done.
    iModIntro. iFrame.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat".
    iModIntro.
    (* close with updated type *)
    iIntros (def' lts' rs' bmin Hst_eq Hlen_eq) "#Hincl' #Hcond_ty Hb".
    iMod (gvar_update rs' with "Hauth Hrfn") as "(Hauth & Hrfn)".
    set (V := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗ [∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';r', ⌜ltype_st lt = ty_syn_type def⌝ ∗ ltype_own lt (Owned false) π r0 (l offset{ly}ₗ i)))%I).
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod ("Hb_cl" $! V with "[] Hcred1 [Hauth Hb]") as "(Hb & Htok)".
    { iNext. iIntros "(%r' & Hauth & Hb) Hdead".
      iModIntro. iNext. iExists r'. iFrame "Hauth". iMod "Hb" as "($ & Hb)".
      iMod (lft_incl_dead with "Hincl Hdead") as "Hdead"; first done.
      setoid_rewrite ltype_own_core_equiv.
      iApply (array_acc_uniq_elems_unblock _ _ _ _ _ _ _ _ _ [κ] with "[Hcond_ty] [Hdead] Hb").
      - done.
      - done.
      - iApply (big_sepL2_impl with "Hcond_ty").
        iModIntro. iIntros (? [] [] ? ?).
        iApply typed_place_cond_incl. done.
      - by iApply lft_dead_list_singleton.
    }
    { iModIntro. rewrite /V. iExists rs'. iFrame. rewrite Hst_eq. eauto 8 with iFrame. }
    iMod ("Htokcl" with "Htok") as "$".
    iMod "Hcl_F" as "_".
    iModIntro.
    (* TODO maybe donate the leftover credits *)
    iSplitL.
    { rewrite ltype_own_array_unfold /array_ltype_own.
      iExists ly. iFrame. rewrite -Hst_eq. do 4 iR.
      iPoseProof (pinned_bor_shorten with "Hincl Hb") as "Hb".
      iModIntro. subst V.
      (* need to adapt the pinned part, too *)
      iApply (pinned_bor_iff with "[] [] Hb").
      { iNext. iModIntro. eauto. }
      iNext. iModIntro.
      setoid_rewrite ltype_own_core_equiv.

      iAssert ([∗ list] ty1;ty2 ∈ interpret_iml (◁ def) len lts; interpret_iml (◁ def') len lts', typed_place_cond (UpdUniq [κ]) ty1 ty2)%I with "[Hcond_ty]" as "Ha".
      { iApply (big_sepL2_impl with "Hcond_ty"). iModIntro. iIntros (k ? ? ? ?). by iApply typed_place_cond_incl. }
      iSplit.
      - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "($ & Hb)".
        iApply (array_acc_uniq_elems_core_eq with "[] Hb"). { done. } { done. }
        iApply typed_place_cond_uniq_core_eq_array. done.
      - iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame. iMod "Hb" as "($ & Hb)".
        rewrite Hst_eq. iApply (array_acc_uniq_elems_core_eq with "[] Hb").
        { rewrite -Hst_eq. done. } { done. }
        iPoseProof (typed_place_cond_uniq_core_eq_array with "Ha") as "Hb".
        iApply big_sepL2_flip. iApply (big_sepL2_impl with "Hb").
        iModIntro. iIntros (? ? ? ? ?) "Heq" => /=.
        iIntros (??). iApply ltype_eq_sym. iApply "Heq".
    }
    iApply (array_ltype_place_cond _ _  with "Hcond_ty"); last done.
    apply place_access_rt_rel_refl.
  Qed.

  Lemma array_ltype_acc_shared {rt} F π (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (rs : list (place_rfn rt)) l κ :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] #rs @ ArrayLtype def len lts -∗
    ∃ ly, ⌜syn_type_has_layout def.(ty_syn_type) ly⌝ ∗
      ⌜l `has_layout_loc` (mk_array_layout ly len)⌝ ∗
      ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗ |={F}=>
      ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def) len lts;rs,
        ⌜ltype_st lt = ty_syn_type def⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Shared κ] r0 @ lt) ∗
      (∀ (def' : type rt) (lts' : list (nat * ltype rt)) rs',
        ⌜ty_syn_type def = ty_syn_type def'⌝ -∗
        ⌜length rs = length rs'⌝ -∗
        (* new ownership *)
        ([∗ list] i↦lt;r0 ∈ interpret_iml (◁ def') len lts';rs',
          ⌜ltype_st lt = ty_syn_type def'⌝ ∗ (l offset{ly}ₗ i) ◁ₗ[π, Shared κ] r0 @ lt)
         ={F}=∗
        l ◁ₗ[π, Shared κ] #rs' @ ArrayLtype def' len lts'
      ).
  Proof.
    iIntros (?) "Hb". rewrite ltype_own_array_unfold /array_ltype_own.
    iDestruct "Hb" as "(%ly & %Hst & % & %Hly & #Hlb & %r' & <- & #Hb)".
    iExists ly. iR. iR. iR. iR.
    iMod (fupd_mask_mono with "Hb") as "(<- & #Hb')"; first done.
    iModIntro. iFrame "Hb'".
    iIntros (def' lts' rs') "%Hst' %Hlen #Hb''".
    rewrite ltype_own_array_unfold /array_ltype_own.
    iModIntro.
    iExists ly. rewrite -Hst'. iR. iR. iR. iR.
    iExists _. iR. iR. iModIntro. by iFrame "Hb''".
  Qed.

End accessors.

