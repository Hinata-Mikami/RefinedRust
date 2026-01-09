(** From the CPP'26 paper "Building Blocks for Step-Indexed Program Logics",
    by Thomas Somers, Jonas Kastberg Hinrichsen, Lennard Gäher, and Robbert Krebbers.

    Upstream: https://gitlab.mpi-sws.org/tlsomers/iris-contrib/-/tree/8a482f0a60295cb016c5a39b2ec5f602b74e3514
*)
From iris.prelude Require Import options.
From iris.proofmode Require Import base proofmode environments classes classes_make
                                   modality_instances ltac_tactics.
From caesium.physical_step Require Import physical_step.

(** ==============================
    Step Updates
    ==============================

    The previous modality |={E}⧗=> is used to define the weakest precondition, but cannot directly be used by users, as it is not nicely composable.
    In this file we define a step update modality |~{E1, E2}~> (Notation from Aneris), which supports most of the rules of `|={E}⧗=>` -- or slightly weaker in the case of conjunction -- which is nicely composable and can be eliminated by taking a physical step (e.g. in WP).

    Such a step modality already exists in Aneris for persistent time receipts ⧖ and in Refined Rust for spatial time receipts ⧗.
    Below our definition of the step modality, we prove that our step modality supports the same rules as both of their modalities, generalized to a
    general `f`.

*)

Section step_update.

  Context `{!lcGS Σ, !trGS Σ, !tr_generation} `{!BiFUpd (iProp Σ), HBUpdFUpd: !BiBUpdFUpd (iProp Σ)}.

  (* Generalization of the Aneris step update modality *)
  Definition step_upd_def E1 E2 P : iProp Σ :=
    ∀ Q, (|={E2}⧗=> Q) -∗ |={E1}⧗=> Q ∗ P.
  Local Definition step_upd_aux : seal ( @step_upd_def). Proof using HBUpdFUpd. by eexists. Qed.
  Definition step_upd := step_upd_aux.(unseal).
  Local Definition step_upd_unseal :
    @step_upd = @step_upd_def := step_upd_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?step_upd_unseal /step_upd_def.


  Notation "|~{ E1 , E2 }~> P" := (step_upd E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
  Notation "|~{ E }~> P" := (step_upd E ∅ P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
  Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

  Lemma physical_step_step_upd E1 E2 P Q :
    (|~{E1, E2}~> P) -∗
    (|={E2}⧗=> P -∗ Q) -∗
    |={E1}⧗=> Q.
  Proof using HBUpdFUpd.
    unseal. iIntros "Hupd Hstep".
    iApply (physical_step_wand with "(Hupd Hstep)").
    iIntros "[HPQ HP]". by iApply "HPQ".
  Qed.

  Local Lemma fupd_mask_subseteq_l E1 E2 Ef1 Ef2 (P : iProp Σ) :
    E2 ⊆ E1 → E1 ## Ef1 → E1 ## Ef2 →
    (|={E2 ∪ Ef1, E2 ∪ Ef2}=> P) ⊢ |={E1 ∪ Ef1, E1 ∪ Ef2}=> P.
  Proof using HBUpdFUpd.
    iIntros (Hle Hf1 Hf2) "Hupd".
    assert (∀ Ef, E1 ## Ef → E1 ∪ Ef = E2 ∪ Ef ∪ E1 ∖ E2) as Hset.
    { intros.
      rewrite (comm_L _ E2) -assoc_L (comm_L _ E2) difference_union_L (comm_L _ _ E2).
      rewrite (subseteq_union_1_L E2); [|done].
      rewrite (comm_L _ E1) //.
    }
    rewrite (Hset Ef1) ?(Hset Ef2); [|set_solver..].
    iApply (fupd_mask_frame_r with "[$]"); set_solver.
  Qed.

  Lemma step_update_frame E1 E2 Ef P :
    E2 ⊆ E1 → E1 ## Ef →
    (|~{E1,E2}~> P) -∗
    (|~{E1 ∪ Ef,E2 ∪ Ef}~> P).
  Proof using HBUpdFUpd.
    unseal. iIntros (Hle Hdiff) "Hupd %Q HQ".
    iApply (physical_step_atomic E1).
    iDestruct (physical_step_atomic_inv_subseteq (E2) with "HQ") as "HQ"; [set_solver|].
    iDestruct (fupd_mask_subseteq_l E1 E2 Ef ∅ with "[HQ]") as ">HQ"; try set_solver;
      rewrite right_id_L; [done|].
    iModIntro. iApply (physical_step_wand with "[-]").
    2: { iIntros "H". iApply fupd_frame_r. iExact "H". }
    iApply "Hupd". iApply (physical_step_wand with "[$]").
    iIntros "HQ".
    iDestruct (fupd_mask_subseteq_l E1 E2 ∅ Ef with "[HQ]") as "HQ"; try set_solver;
      by rewrite right_id_L.
  Qed.

  Lemma step_update_intro E1 E2 P :
    E2 ⊆ E1 → P -∗ |~{E1,E2}~> P.
  Proof using HBUpdFUpd.
    unseal. iIntros (HE) "HP %Q HQ".
    iApply (physical_step_atomic E2).
    iMod (fupd_mask_subseteq) as "Hclose"; [done|].
    iModIntro. iApply (physical_step_wand with "[$]").
    iMod "Hclose". by iIntros "$".
  Qed.

  Lemma step_update_fupd E1 E2 P :
    (|~{E1,E2}~> |={E1}=> P) -∗ |~{E1,E2}~> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "Hstep %R HR".
    iDestruct ("Hstep" with "HR") as "HR".
    iApply physical_step_fupd. iApply (physical_step_wand with "[$]").
    iIntros "[$ >$] //".
  Qed.
  Lemma step_update_fupd_l E1 E2 P :
    (|={E1}=> |~{E1,E2}~> P) -∗ |~{E1,E2}~> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "Hstep %R HR". iMod "Hstep".
    by iApply "Hstep".
  Qed.

  Lemma step_update_sep E1 E2 E3 P Q :
    (|~{E1,E2}~> P) -∗ (|~{E2,E3}~> Q) -∗ |~{E1,E3}~> P ∗ Q.
  Proof using HBUpdFUpd.
    unseal. iIntros "HP HPQ %R HR".
    iDestruct ("HPQ" with "HR") as "HR".
    iDestruct ("HP" with "HR") as "HR".
    iApply (physical_step_wand with "[$]").
    iIntros "[[$ $] $]".
  Qed.

  Lemma step_update_frame_l E1 E2 P Q :
    (|~{E1,E2}~> P) -∗ (|={E1}=> Q) -∗ |~{E1,E2}~> (P ∗ Q).
  Proof using HBUpdFUpd.
    unseal. iIntros "Hstep1 Hstep2 %R HR".
    iApply physical_step_fupd_l. iMod "Hstep2". iModIntro.
    iApply (physical_step_wand (R ∗ P) with "[Hstep1 HR]").
    - by iApply "Hstep1".
    - iIntros "[$ $] //".
  Qed.


  Lemma step_update_comm_strong E1 E2 E3 E4 P Q :
    E1 ## E3 → E2 ## E4 →
    E2 ⊆ E1 → E4 ⊆ E3 → (* I would rather not have these conditions. *)
    (|~{E1, E2}~> P) -∗ (|~{E3, E4}~> Q) -∗ |~{E1 ∪ E3, E2 ∪ E4}~> P ∗ Q.
  Proof using HBUpdFUpd.
    iIntros (Hdisj1 Hdisj2 Hle1 Hle2) "HP HQ".
    iDestruct (step_update_frame _ _ E3 with "HP") as "HP"; [done..|].
    iDestruct (step_update_frame _ _ E2 with "HQ") as "HQ"; [set_solver..|].
    rewrite !(comm_L _ _ E2).
    iApply (step_update_sep with "HP HQ").
  Qed.

  Lemma step_update_comm E1 E2 P Q :
    E1 ## E2 → (|~{E1}~> P) -∗ (|~{E2}~> Q) -∗ |~{E1 ∪ E2}~> P ∗ Q.
  Proof using HBUpdFUpd.
    iIntros (Hdisj) "HP HQ".
    iDestruct (step_update_comm_strong with "HP HQ") as "H"; [set_solver..|].
    rewrite idemp_L //.
  Qed.

  Lemma step_update_atomic E1 E2 E3 P :
    (|={E1,E2}=> |~{E2,E3}~> |={E2,E1}=> P) -∗ |~{E1,E3}~> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "HP %R HR".
    iMod "HP". iApply (physical_step_wand with "(HP HR)").
    iIntros "[$ $]".
  Qed.

  Lemma step_update_wand_later E1 E2 P Q :
    (|~{E1, E2}~> P) -∗ ▷ (P -∗ Q) -∗ |~{E1, E2}~> Q.
  Proof using HBUpdFUpd.
    unseal. iIntros "HP HPQ %R HR".
    iApply (physical_step_wand_later with "(HP HR) [HPQ]").
    iNext. iIntros "[$ HP]". by iApply "HPQ".
  Qed.
  Lemma step_update_wand E1 E2 P Q :
    (|~{E1, E2}~> P) -∗ (P -∗ Q) -∗ |~{E1, E2}~> Q.
  Proof using HBUpdFUpd.
    iIntros "HP HPQ". iApply (step_update_wand_later with "[$] [$]").
  Qed.

  Lemma step_update_mono E1 E2 E3 P Q :
    E2 ⊆ E1 → (|~{E2,E3}~> P) -∗ (P ={E2,E1}=∗ Q) -∗ |~{E1,E3}~> Q.
  Proof using HBUpdFUpd.
    iIntros (Hle) "HP HPQ". iApply (step_update_atomic E1 E2).
    iMod (fupd_mask_subseteq E2) as "Hclose"; [done|]. iModIntro.
    by iApply (step_update_wand with "[$]").
  Qed.

  Lemma step_update_impl E1 E2 E3 P Q :
    (|~{E1,E2}~> P) -∗ (|~{E2,E3}~> P -∗ Q) -∗ |~{E1,E3}~> Q.
  Proof using HBUpdFUpd.
    iIntros "HP HPQ". iDestruct (step_update_sep with "HP HPQ") as "HP".
    iApply (step_update_wand with "[$]").
    iIntros "[HP HPQ]". by iApply "HPQ".
  Qed.

  Lemma step_update_lb_step_very_strong {E1 E3} E2 P Q n :
    ((|={E1, ∅}=> ⧖ n) ∧
      (|={E1, E2}=> |={∅}▷=>^(S $ tr_f n) Q ={E2, E1}=∗ P) ∗ |~{E2, E3}~> Q) -∗
    |~{E1, E3}~> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "H %R HR".
    iApply (physical_step_fupdN_strong E2).
    iSplit; [by iDestruct "H" as "[>$ _]"|].
    iDestruct "H" as "[_ [>H HQ]]".
    iDestruct ("HQ" with "HR") as "HR".
    iModIntro. iFrame "H".
    iApply (physical_step_wand with "[$]").
    iIntros "[$ $] $ //".
  Qed.

  Lemma step_update_lb_step_strong E P n :
    (|={E, ∅}=> ⧖ n) ∧ (|={E, ∅}=> |={∅}▷=>^(S $ tr_f n) |={∅, E}=> P) -∗ |~{E}~> P.
  Proof using HBUpdFUpd.
    iIntros "H".
    iApply (step_update_lb_step_very_strong ∅).
    iSplit; [iDestruct "H" as "[$ _]"|].
    iDestruct "H" as "[_ H]".
    iSplitL; [|by iApply (step_update_intro _ _ True)].
    iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
    iIntros "$ //".
  Qed.

  Lemma step_update_lb_step E P n :
    ⧖ n -∗ (|={E, ∅}=> |={∅}▷=>^(S $ tr_f n) |={∅, E}=> P) -∗ |~{E}~> P.
  Proof using HBUpdFUpd.
    iIntros " H⧖ Hupd". iApply step_update_lb_step_strong.
    iSplit; [|done].
    iApply (fupd_mask_intro); [set_solver|by iIntros].
  Qed.

  Lemma step_update_lb_update n :
    ⧖ n -∗ |~~> (⧖ (tr_f (S n))).
  Proof using HBUpdFUpd.
    unseal. iIntros "H⧖ %R HR".
    iApply (physical_step_incr with "[$]").
    iApply (physical_step_wand with "[$]").
    iIntros "$ $ //".
  Qed.

  Lemma step_update_tr_use n :
    ⧗ n -∗ |~~> ⧗ (tr_f n) ∗ £ (tr_f n).
  Proof using HBUpdFUpd.
    unseal. iIntros "H⧗ %Q HQ".
    iApply (physical_step_tr_use with "[$]").
    iApply (physical_step_wand with "[$]").
    iIntros "$ $ $ //".
  Qed.

  (* Instances *)
  Global Instance elim_modal_upd_step_update p E1 E1' P Q :
    ElimModal True p false (|==> P) P (|~{E1, E1'}~> Q) (|~{E1, E1'}~> Q).
  Proof using HBUpdFUpd.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (_) "[HP HPQ]". iApply step_update_fupd_l.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_modal_fupd_step_update p E1 E1' P Q :
    ElimModal True p false (|={E1}=> P) P (|~{E1, E1'}~> Q) (|~{E1, E1'}~> Q).
  Proof using HBUpdFUpd.
    rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r.
    iIntros (?) "H". by iApply step_update_fupd_l.
  Qed.

  Global Instance elim_modal_fupd_step_update_weak p E1 E1' E2 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|~{E1, E1'}~> Q) (|~{E2, E1'}~>|={E2,E1}=> Q) | 100.
  Proof using HBUpdFUpd.
    rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r.
    iIntros (_) "H". by iApply step_update_atomic.
  Qed.

  Global Instance is_except_zero_step_update E1 E1' P :
    IsExcept0 (|~{E1, E1'}~> P).
  Proof using HBUpdFUpd.
    rewrite /IsExcept0. iIntros "H".
    iApply step_update_fupd_l. by iMod "H".
  Qed.

  Global Instance step_update_contractive E1 E2 :
    Contractive (step_upd E1 E2).
  Proof using HBUpdFUpd.
    intros n P Q HPQ. unseal.
    do 3 f_equiv. f_contractive. by repeat f_equiv.
  Qed.
  Global Instance step_update_proper E1 E2 :
      Proper ((≡) ==> (≡)) (step_upd E1 E2).
  Proof using HBUpdFUpd. apply _. Qed.

  Global Instance from_modal_step_update E P :
    FromModal True modality_id (|~{E, E}~> P) (|~{E, E}~> P) P.
  Proof.
    rewrite /FromModal /=. iIntros (_) "H". by iApply step_update_intro.
  Qed.

  Global Instance from_modal_step_update_wrong_mask E1 E2 P :
    FromModal
      (pm_error "Only non-mask-changing step update modalities can be introduced directly.
Use [iApply step_update_intro] to introduce mask-changing step update modalities")
      modality_id (|~{E1,E2}~> P) (|~{E1,E2}~> P) P | 100.
  Proof. by intros []. Qed.

  Global Instance elim_modal_step_upd_physical_step_1 p E1 E2 P Q :
    ElimModal True p false (|~{E1, E2}~> P) emp (|={E1}⧗=> Q) (|={E2}⧗=> P -∗ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (?) "[HP HPQ]".
    rewrite step_upd_unseal /step_upd_def.
    iApply (physical_step_wand with "(HP (HPQ [//]))").
    iIntros "[HP HPQ]". by iApply "HP".
  Qed.
  Global Instance elim_modal_step_upd_physical_step_2 p E1 E2 P Q :
    ElimModal (E1 ⊆ E2) p false (|~{E1}~> P) emp (|={E2}⧗=> Q) (|={E2∖E1}⧗=> P -∗ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=. iIntros (Hle) "[Hupd HPQ]".
    iDestruct (step_update_frame _ _ (E2 ∖ E1) with "Hupd") as "Hupd"; [set_solver..|].
    rewrite <-union_difference_L, (left_id_L ∅ (∪)); try done.
    iMod "Hupd" as "_". by iApply "HPQ".
  Qed.
  Global Instance elim_modal_step_upd_physical_step_3 p E P Q :
    ElimModal True p false (|~~> P) emp (|={E}⧗=> Q) (|={E}⧗=> P -∗ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=. iIntros (Hle) "[Hupd HPQ]".
    iMod "Hupd" as "_". rewrite difference_empty_L. by iApply "HPQ".
  Qed.

  Global Instance elim_modal_step_upd_step_upd_1 p E1 E2 E3 P Q :
    ElimModal True p false (|~{E1, E2}~> P) emp (|~{E1, E3}~> Q) (|~{E2, E3}~> P -∗ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=. iIntros (?) "[HP HPQ]".
    iApply (step_update_impl with "[$] (HPQ [//])").
  Qed.
  Global Instance elim_modal_step_upd_step_upd_2 p E1 E2 E3 P Q :
    ElimModal (E1 ⊆ E2) p false (|~{E1}~> P) emp (|~{E2, E3}~> Q) (|~{E2∖E1, E3}~> P -∗ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=. iIntros (Hle) "[Hupd HPQ]".
    iDestruct (step_update_frame _ _ (E2 ∖ E1) with "Hupd") as "Hupd"; [set_solver..|].
    rewrite <-union_difference_L, (left_id_L ∅ (∪)); try done.
    iMod "Hupd" as "_". by iApply "HPQ".
  Qed.
  Global Instance elim_modal_step_upd_step_upd_3 p E1 E2 P Q :
    ElimModal True p false (|~~> P) emp (|~{E1, E2}~> Q) (|~{E1, E2}~> P -∗ Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=. iIntros (Hle) "[Hupd HPQ]".
    iMod "Hupd" as "_". rewrite difference_empty_L. by iApply "HPQ".
  Qed.
End step_update.

Notation "|~{ E1 , E2 }~> P" := (step_upd E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
Notation "|~{ E }~> P" := (step_upd E ∅ P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").


(* The logical step modality used in RefinedRust. Note that the lemmas are derived from those above. *)
Module logical_step.
  Section logical_step.

    Context `{!lcGS Σ, !trGS Σ, !tr_generation} `{!BiFUpd (iProp Σ), HBUpdFUpd: !BiBUpdFUpd (iProp Σ)}.

    Definition logical_step E P : iProp Σ := |~{E, E}~> P.

    Lemma logical_step_sep E P1 P2 :
      logical_step E P1 -∗
      logical_step E P2 -∗
      logical_step E (P1 ∗ P2).
    Proof using HBUpdFUpd.
      iApply step_update_sep.
    Qed.

    Lemma fupd_logical_step E P :
      (|={E}=> logical_step E P) -∗
      logical_step E P.
    Proof using HBUpdFUpd. iIntros ">$". Qed.

    Lemma logical_step_fupd E P :
      logical_step E (|={E}=> P) -∗
      logical_step E P.
    Proof using HBUpdFUpd.
      iIntros "Hupd".
      iApply (step_update_atomic _ E).
      by iModIntro.
    Qed.

    Lemma logical_step_intro E P :
      P -∗
      logical_step E P.
    Proof using HBUpdFUpd.
      by iApply (step_update_intro).
    Qed.

    Lemma logical_step_intro_atime F P n :
      ⧗ n -∗
      (⧗ (tr_f n) -∗ £ (tr_f n) ={F}=∗ P) -∗
      logical_step F P.
    Proof using HBUpdFUpd.
      iIntros "H⧗ Hupd".
      iApply step_update_fupd.
      iMod (step_update_tr_use with "H⧗") as "_".
      iIntros "!> [? ?]". iApply ("Hupd" with "[$] [$]").
    Qed.

    Lemma logical_step_frame_r E P Q :
      logical_step E P -∗
      Q -∗
      logical_step E (P ∗ Q).
    Proof using HBUpdFUpd.
      iIntros "HP HQ".
      by iApply (step_update_frame_l with "[$]").
    Qed.

    Lemma logical_step_wand E P Q :
      logical_step E P -∗
      (P -∗ Q) -∗
      logical_step E Q.
    Proof using HBUpdFUpd.
      iApply step_update_wand.
    Qed.

    Lemma logical_step_compose E P Q :
      logical_step E P -∗
      logical_step E (P -∗ Q) -∗
      logical_step E Q.
    Proof using HBUpdFUpd.
      iApply step_update_impl.
    Qed.

    Lemma logical_step_big_sepL {A} E (l : list A) Φ :
      ([∗ list] i ↦ x ∈ l, logical_step E (Φ i x)) -∗
      logical_step E ([∗ list] i ↦ x ∈ l, Φ i x).
    Proof using HBUpdFUpd.
      iInduction l as [ | x l] "IH" forall (Φ); simpl.
      - iApply logical_step_intro.
      - iIntros "[Ha Hb]". iPoseProof ("IH" with "Hb") as "Hb".
        iPoseProof (logical_step_sep with "Ha Hb") as "Ha". done.
    Qed.

    Lemma logical_step_mask_mono E1 E2 P :
      E1 ⊆ E2 →
      logical_step E1 P -∗
      logical_step E2 P.
    Proof using HBUpdFUpd.
      iIntros (Hle).
      apply (union_difference_L) in Hle. rewrite Hle.
      iApply (step_update_frame); set_solver.
    Qed.

    Local Lemma logical_step_big_sepL2' {A B} E (xs : list A) (ys : list B) Φ (k : nat) :
      ([∗ list] i ↦ x; y ∈ xs; ys, logical_step E (Φ (k + i)%nat x y)) -∗
      logical_step E ([∗ list] i ↦ x; y ∈ xs; ys, Φ (k + i)%nat x y).
    Proof using HBUpdFUpd.
      iIntros "Ha".
      iInduction xs as [ | x xs] "IH" forall (ys k); destruct ys as [ | y ys]; simpl; [ | done | done | ].
      { iApply logical_step_intro. done. }
      iDestruct "Ha" as "(Hx & Ha)".
      rewrite /logical_step. setoid_rewrite Nat.add_succ_r.
      iPoseProof ("IH" $! _ (S k) with "Ha") as "Ha".
      iApply (logical_step_compose with "Hx"). iApply (logical_step_compose with "Ha").
      iApply logical_step_intro. iIntros "$ $".
    Qed.
    Lemma logical_step_big_sepL2 {A B} E (xs : list A) (ys : list B) Φ :
      ([∗ list] i ↦ x; y ∈ xs; ys, logical_step E (Φ i x y)) -∗
      logical_step E ([∗ list] i ↦ x; y ∈ xs; ys, Φ i x y).
    Proof using HBUpdFUpd.
      apply (logical_step_big_sepL2' _ _ _ _ 0).
    Qed.

    Lemma logical_step_intro_fupd E P :
      (|={E}=> P) -∗
      logical_step E P.
    Proof using HBUpdFUpd.
      iIntros "HP".
      iApply logical_step_fupd.
      by iApply (step_update_intro).
    Qed.
  End logical_step.
End logical_step.

