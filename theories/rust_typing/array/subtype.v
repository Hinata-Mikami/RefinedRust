From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.array Require Import def.
From refinedrust Require Import options.

(* Note: We don't support things like [u16; 2] <: [u8; 4]. *)
Section subtype.
  Context `{!typeGS Σ}.

  Implicit Types (rt : RT).

  Import EqNotations.
  Local Definition array_t_incl_precond_elem {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 :=
    (match r1, r2 with
      | #r1, #r2 => type_incl r1 r2 ty1 ty2
      | _, _ => ∃ (Heq : rt1 = rt2), ⌜r1 = rew <- [place_rfnRT] Heq in r2⌝ ∗ ∀ (r : rt1), type_incl r (rew Heq in r) ty1 ty2
      end)%I.
  Local Definition array_t_incl_precond {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 :=
    ([∗ list] r1; r2 ∈ rs1; rs2, array_t_incl_precond_elem ty1 ty2 r1 r2)%I.

  Local Instance array_t_incl_precond_elem_pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    Persistent (array_t_incl_precond_elem ty1 ty2 r1 r2).
  Proof. destruct r1, r2; simpl; apply _. Qed.
  Local Instance array_t_incl_precond_pers {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 :
    Persistent (array_t_incl_precond ty1 ty2 rs1 rs2).
  Proof. apply big_sepL2_persistent. intros ? [] []; simpl; apply _. Qed.

  (* TODO move *)
  Lemma type_incl_use_val π {rt1 rt2} (r1 : rt1) (r2 : rt2) ty1 ty2 v :
    type_incl r1 r2 ty1 ty2 -∗ v ◁ᵥ{π} r1 @ ty1 -∗ v ◁ᵥ{π} r2 @ ty2.
  Proof. iIntros "#(_ & _ & Hval & _) Hv". by iApply "Hval". Qed.
  Lemma type_incl_use_shr π κ {rt1 rt2} (r1 : rt1) (r2 : rt2) ty1 ty2 l :
    type_incl r1 r2 ty1 ty2 -∗ l ◁ₗ{π, κ} r1 @ ty1 -∗ l ◁ₗ{π, κ} r2 @ ty2.
  Proof. iIntros "#(_ & _ & _ & Hshr) Hl". by iApply "Hshr". Qed.

  (* TODO: in practice, we probably just want equality for the refinements? think about the symbolic case.. *)
  Lemma array_t_own_val_mono' {rt1 rt2} π (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 len v :
    ty1.(ty_syn_type) = ty2.(ty_syn_type) →
    array_t_incl_precond ty1 ty2 rs1 rs2 -∗
    v ◁ᵥ{π} rs1 @ array_t len ty1 -∗
    v ◁ᵥ{π} rs2 @ array_t len ty2.
  Proof.
    iIntros (Heqst) "Hincl Ha".
    rewrite /ty_own_val/=.
    iDestruct "Ha" as "(%ly & %Hst & % & % & %Hly & Ha)".
    iExists ly. rewrite -Heqst. iR. iR.
    iPoseProof (big_sepL2_length with "Hincl") as "%Hleneq".
    rewrite -Hleneq. iR. iR.
    iPoseProof (big_sepL2_length with "Ha") as "%Hleneq'".
    iApply big_sepL2_from_zip. { rewrite -Hleneq//. }
    iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
    iPoseProof (big_sepL_extend_l rs2 with "Ha") as "Ha".
    { rewrite -Hleneq length_zip. lia. }
    iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
    iApply (big_sepL2_elim_l rs1).
    iApply big_sepL2_from_zip. { rewrite length_zip -Hleneq -Hleneq'. lia. }
    rewrite !zip_assoc_r [zip rs2 rs1]zip_flip zip_fmap_l !big_sepL_fmap.
    iPoseProof (big_sepL2_from_zip' with "Ha") as "Ha".
    { rewrite length_zip. lia. }
    iApply big_sepL2_to_zip'.
    iPoseProof (big_sepL2_to_zip with "Hincl") as "Hincl".
    iPoseProof (big_sepL_extend_r with "Hincl") as "Hincl"; first last.
    { iPoseProof (big_sepL2_sep_1 with "Ha Hincl") as "Ha".
      iApply (big_sepL2_impl with "Ha"). iModIntro.
      iIntros (k [r1 r2] v' Hlook1 Hlook2) "((%r'' & Hrfn & Hown) & Hincl)"=>/=.
      rewrite /array_own_el_val. destruct r1, r2; simpl.
      - iDestruct "Hrfn" as "->". iPoseProof (type_incl_use_val with "Hincl Hown") as "?". eauto with iFrame.
      - iDestruct "Hrfn" as "->". iDestruct "Hincl" as "(%Heq & %Heq' & Hincl)". subst. done.
      - iDestruct "Hincl" as "(%Heq & %Heq' & Hincl)". subst. done.
      - iDestruct "Hincl" as "(%Heq & %Heq' & Hincl)". subst. injection Heq' as <-.
        iPoseProof (type_incl_use_val with "Hincl Hown") as "?". eauto with iFrame.
    }
    rewrite length_zip. lia.
  Qed.
  (* the "trivial" (Rust) subtyping that we need for, e.g., lifetimes *)
  Lemma array_t_own_val_mono {rt} π (ty1 ty2 : type rt) len v rs :
    ty_syn_type ty1 = ty_syn_type ty2 →
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ᵥ{π} rs @ array_t len ty1 -∗
    v ◁ᵥ{π} rs @ array_t len ty2.
  Proof.
    iIntros (?) "#Hincl". iApply array_t_own_val_mono'; first done.
    iApply big_sepL2_intro; first done.
    iModIntro. iIntros (k x1 x2 Hlook1 Hlook2).
    assert (x1 = x2) as -> by naive_solver.
    destruct x2; simpl; first done.
    iExists eq_refl. iR. done.
  Qed.

  Lemma array_t_shr_mono' {rt1 rt2} π (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 len v κ :
    ty_syn_type ty1 = ty_syn_type ty2 →
    array_t_incl_precond ty1 ty2 rs1 rs2 -∗
    v ◁ₗ{π, κ} rs1 @ array_t len ty1 -∗
    v ◁ₗ{π, κ} rs2 @ array_t len ty2.
  Proof.
    iIntros (Heqst) "Hincl Ha".
    rewrite /ty_shr/=.
    iDestruct "Ha" as "(%ly & %Hst & % & % & %Hly & Ha)".
    iExists ly. rewrite -Heqst. iR. iR.
    iPoseProof (big_sepL2_length with "Hincl") as "%Hleneq".
    rewrite -Hleneq. iR. iR.
    iPoseProof (big_sepL_extend_r rs2 with "Ha") as "Ha"; first done.
    iApply big_sepL2_elim_l.
    iPoseProof (big_sepL2_sep_1 with "Ha Hincl") as "Ha".
    iApply (big_sepL2_impl with "Ha"). iModIntro.
    iIntros (k r1 r2 Hlook1 Hlook2) "((%r'' & Hrfn & Hown) & Hincl)"=>/=.
    rewrite /array_own_el_shr. destruct r1, r2; simpl.
    - iDestruct "Hrfn" as "->". iPoseProof (type_incl_use_shr with "Hincl Hown") as "?". eauto with iFrame.
    - iDestruct "Hrfn" as "->". iDestruct "Hincl" as "(%Heq & %Heq' & Hincl)". subst. done.
    - iDestruct "Hincl" as "(%Heq & %Heq' & Hincl)". subst. done.
    - iDestruct "Hincl" as "(%Heq & %Heq' & Hincl)". subst. injection Heq' as <-.
      iPoseProof (type_incl_use_shr with "Hincl Hown") as "?". eauto with iFrame.
  Qed.
  Lemma array_t_shr_mono {rt} π (ty1 ty2 : type rt) len v rs κ :
    ty_syn_type ty1 = ty_syn_type ty2 →
    (∀ r, type_incl r r ty1 ty2) -∗
    v ◁ₗ{π, κ} rs @ array_t len ty1 -∗
    v ◁ₗ{π, κ} rs @ array_t len ty2.
  Proof.
    iIntros (?) "#Hincl". iApply array_t_shr_mono'; first done.
    iApply big_sepL2_intro; first done.
    iModIntro. iIntros (k x1 x2 Hlook1 Hlook2).
    assert (x1 = x2) as -> by naive_solver.
    destruct x2; simpl; first done.
    iExists eq_refl. iR. done.
  Qed.

  Lemma array_t_type_incl' {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) rs1 rs2 len :
    ty_syn_type ty1 = ty_syn_type ty2 →
    array_t_incl_precond ty1 ty2 rs1 rs2 -∗
    type_incl rs1 rs2 (array_t len ty1) (array_t len ty2).
  Proof.
    iIntros (Hst) "#Ha".
    iSplit; last iSplit; last iSplit.
    - simpl. rewrite Hst. done.
    - simpl. eauto.
    - iModIntro. iIntros (π v) "Hv".
      iApply array_t_own_val_mono'; done.
    - iModIntro. iIntros (κ π l) "Hl".
      by iApply array_t_shr_mono'.
  Qed.
  Lemma array_t_type_incl {rt} (ty1 ty2 : type rt) rs len :
    ty_syn_type ty1 = ty_syn_type ty2 →
    (∀ r, type_incl r r ty1 ty2) -∗
    type_incl rs rs (array_t len ty1) (array_t len ty2).
  Proof.
    iIntros (Hst) "#Ha".
    iSplit; last iSplit; last iSplit.
    - simpl. rewrite Hst. done.
    - simpl. eauto.
    - iModIntro. iIntros (π v) "Hv".
      iApply array_t_own_val_mono; done.
    - iModIntro. iIntros (κ π l) "Hl".
      by iApply array_t_shr_mono.
  Qed.

  Lemma array_t_full_subtype E L {rt} (ty1 ty2 : type rt) len :
    full_subtype E L ty1 ty2 →
    full_subtype E L (array_t len ty1) (array_t len ty2).
  Proof.
    iIntros (Hsubt rs qL) "HL HE".
    iAssert (∀ r, type_incl r r ty1 ty2)%I with "[HL HE]" as "#Hincl".
    { iIntros (r). iApply (Hsubt with "HL HE"). }
    iDestruct ("Hincl" $! inhabitant) as "(%Hst & _)".
    iApply array_t_type_incl; done.
  Qed.
  Lemma array_t_full_eqtype E L {rt} (ty1 ty2 : type rt) len :
    full_eqtype E L ty1 ty2 →
    full_eqtype E L (array_t len ty1) (array_t len ty2).
  Proof.
    intros Heqt. apply full_subtype_eqtype.
    - apply array_t_full_subtype. by apply full_eqtype_subtype_l.
    - apply array_t_full_subtype. by apply full_eqtype_subtype_r.
  Qed.
End subtype.


