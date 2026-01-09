(** From the CPP'26 paper "Building Blocks for Step-Indexed Program Logics",
    by Thomas Somers, Jonas Kastberg Hinrichsen, Lennard Gäher, and Robbert Krebbers.

    Upstream: https://gitlab.mpi-sws.org/tlsomers/iris-contrib/-/tree/8a482f0a60295cb016c5a39b2ec5f602b74e3514
*)
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export iprop own later_credits.
From caesium.physical_step Require Export time_receipts.
From iris.proofmode Require Import base environments classes classes_make
                                   modality_instances ltac_tactics.
From caesium.physical_step Require Export tr_view.
Import uPred.

Section fupd_derived.

  Context {PROP : bi} `{!BiFUpd PROP}.
  Implicit Types P Q R : PROP.

  Lemma step_fupdN_S_fupd_l n E P :
    (|={E}[∅]▷=>^(S n) P) ⊣⊢ (|={E}=> |={E}[∅]▷=>^(S n) P).
  Proof.
    apply (anti_symm (⊢)); rewrite !Nat.iter_succ.
    - apply fupd_intro.
    - by rewrite fupd_trans.
  Qed.

  Lemma step_fupdN_fupd_swap n E P :
    (|={E}[∅]▷=>^n |={E}=> P) ⊣⊢ |={E}=> |={E}[∅]▷=>^n P.
  Proof.
    destruct n as [|n]; [done|].
    rewrite -step_fupdN_S_fupd -step_fupdN_S_fupd_l //.
  Qed.
End fupd_derived.


(* ======== Simple tactic to do decisions with updates. ======== *)

Section fupd_decide.

  Context `{!BiFUpd (iProp Σ), !BiBUpdFUpd (iProp Σ)}.

  Local Lemma update_decide_pure {E} φ (P : iProp Σ) :
    Decision φ →
    (|={E, ∅}=> ⌜φ⌝) ∧ (|={E}=> P) ={E}=∗ ⌜φ⌝ ∗ P.
  Proof.
    iIntros (Hdec).
    destruct Hdec.
    - iIntros "[_ >$] //".
    - iIntros "[>%H' _] //".
  Qed.

  Lemma tac_fupd_decision {E} φ (Δ : envs (iProp Σ)) Q :
    Decision φ →
    envs_entails Δ (|={E, ∅}=> ⌜φ⌝) →
    (φ → envs_entails Δ (|={E}=> Q)) →
    envs_entails Δ (|={E}=> Q).
  Proof.
    rewrite envs_entails_unseal.
    intros Hdecision Hupdφ Hnext.
    iIntros "Henvs".
    iMod (update_decide_pure φ with "[Henvs]") as "[%Hφ Henvs]".
    - iSplit.
      + by iApply Hupdφ.
      + iModIntro. iExact "Henvs".
    - by iApply Hnext.
  Qed.
End fupd_decide.

Tactic Notation "iModDecide" open_constr(φ) "gives" ident(H) :=
  apply (tac_fupd_decision φ _ _); [
    tc_solve |
    | intro H
  ].

Class tr_generation := TrGeneration {
  tr_f : nat → nat;
  tr_f_superadditive x y : tr_f x + tr_f y ≤ tr_f (x + y);
}.

Program Definition tr_generation_nolc : tr_generation := {|
  tr_f x := 0;
|}.
Final Obligation. intros; simpl; lia. Qed.

Section physical_step.

  Context `{!lcGS Σ, !trGS Σ, !tr_generation} `{!BiFUpd (iProp Σ), HBUpdFUpd: !BiBUpdFUpd (iProp Σ)}.

  Lemma tr_f_mono x y :
    x ≤ y → tr_f x ≤ tr_f y.
  Proof.
    intros.
    replace y with (x + (y - x)) by lia.
    etrans; [|apply tr_f_superadditive]; lia.
  Qed.

  Lemma tr_f_zero :
    tr_f 0 = 0.
  Proof.
    destruct (tr_f 0) eqn:Heq; [done|].
    pose proof (tr_f_superadditive 0 0) as Hsub; simpl in *; lia.
  Qed.

  (* Alternative formulation of `f_subadditive` which is nicer to apply. *)
  Local Lemma tr_f_subadditive' x y z :
    x + y ≤ z → tr_f x + tr_f y ≤ tr_f z.
  Proof.
    intros Heq.
    etrans; [apply tr_f_superadditive|].
    apply tr_f_mono; lia.
  Qed.

  (** A modality which represents a single physical step taken. Each physical step
      has additional logical steps which can be used to eliminate more laters
      (specifically (1 + (f (2*nsup))) such steps). The number of additional logical steps is
      determined by time receipts, which are also updated by this modality.
      Note that 2*nsup is the maximum persistent time receipt by converting all additive
      time receipts into persistent ones.

      Remark: The mask changing updates are included specifically for the
      `physical_step_fupdN` rule to support the wp_step_fupdN_strong rule,
      which uses a conjunction at the WP-level rather than the physical step level.
  *)
  Definition physical_step_def E P : iProp Σ :=
    ∀ nsup ntr,
      tr_supply nsup ntr -∗ (* Supply for time receipts *)
      £ (tr_f (1 + 2*nsup - ntr)) -∗ (* Remaining later credits for the step. *)
      |={E, ∅}=> |={∅}▷=>^(S $ tr_f (2*nsup)) |={∅, E}=>
          tr_supply (nsup + tr_f (1 + 2*nsup)) (tr_f ntr) ∗ (* add f (1 + 2n) additive time receipts. *)
          P. (* Result. *)

  Local Definition physical_step_aux : seal ( @physical_step_def). Proof. by eexists. Qed.
  Definition physical_step := physical_step_aux.(unseal).
  Local Definition physical_step_unseal :
    @physical_step = @physical_step_def := physical_step_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?physical_step_unseal /physical_step_def.

  (** The notation uses a ⧗ to symbolize a single step, but otherwise resembles the |={ E }▷=>
      notation used by step_fupd.
  *)
  Notation "|={ E }⧗=> P" := (physical_step E P)
    (at level 99, P at level 200, E at level 50, format "|={ E }⧗=>  P") : bi_scope.

  Lemma physical_step_step {E} n P:
    (|={E, ∅}=> ⧖ n) ∧ (£ (tr_f (S n)) -∗ ⧗ (tr_f (S n)) ={E, ∅}=∗ |={∅}▷=>^(S $ tr_f $ n) |={∅, E}=> P) -∗
    |={E}⧗=> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "H" (nsup ntr) "Hsup H£".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hmask".
    iApply step_fupdN_S_fupd_l.
    iModDecide (_ ≤ _)%nat gives Hle.
    { iDestruct "H" as "[H _]".
      iMod "Hmask". iMod "H".
      iApply (tr_supply_valid_strong with "[$] [$]").
    }
    iMod "Hmask" as "_".
    iMod (tr_supply_incr _ _ (tr_f (1 + 2*nsup)) with "[$]") as "Hsup".
    iDestruct (tr_supply_tr_2 _ (tr_f ntr) ((ntr + tr_f (1 + 2*nsup) - tr_f ntr)) with "[Hsup]") as "[Hsup H⧗]".
    { pose proof (tr_f_mono ntr (1 + 2*nsup)).
      by replace (tr_f ntr + (ntr + tr_f (1 + 2 * nsup) - tr_f ntr)) with (ntr + tr_f (1 + 2*nsup)) by lia. }
    iDestruct (lc_weaken (tr_f (S n)) with "[$]") as "H£".
    { apply tr_f_mono. lia. }
    iDestruct (tr_weaken (tr_f (S n)) with "H⧗") as "H⧗".
    { apply Nat.le_add_le_sub_l.
      pose proof (tr_f_subadditive' ntr (S n) (1 + 2*nsup)).
      lia. }
    iMod ("H" with "[$] [$]") as "HP". iModIntro.
    iApply (step_fupdN_wand with "[HP]").
    { iApply (step_fupdN_le with "[$]"); [|done].
      apply le_n_S, tr_f_mono. lia.
    }
    iIntros ">$". by iFrame.
  Qed.

  Lemma physical_step_intro_trp {E E'} P n :
    ⧖ n -∗ (£ (tr_f $ S $ n) -∗ ⧗ (tr_f $ S $ n) -∗ |={E}[E']▷=>^(S $ tr_f $ n) P) -∗ |={E}⧗=> P.
  Proof using HBUpdFUpd.
    iIntros "H⧖ HP".
    iApply physical_step_step; iSplit.
    { iMod (fupd_mask_subseteq ∅) as "_"; [set_solver|done]. }
    iIntros "??". iMod ("HP" with "[$] [$]") as "HP". iClear "H⧖".
    iMod (fupd_mask_subseteq ∅) as "Hcl"; [set_solver|]. do 3 iModIntro.
    iMod "Hcl" as "_". iMod "HP".
    iInduction (tr_f n) as [|n'].
    { simpl. iApply fupd_mask_intro_subseteq; set_solver. }
    iMod "HP". iMod (fupd_mask_subseteq ∅) as "Hcl"; [set_solver|].
    do 3 iModIntro. iMod "Hcl" as "_". iMod "HP".
    by iApply "IHn'".
  Qed.

  Lemma physical_step_wand_later {E} P Q:
    (|={E}⧗=> P) -∗ ▷(P -∗ Q) -∗ |={E}⧗=> Q.
  Proof using HBUpdFUpd.
    unseal. iIntros "HP HPQ" (nsup ntr) "Hsup H£".
    iMod ("HP" with "[$] [$]") as "HP".
    rewrite !Nat.iter_succ_r. iModIntro.
    iApply (step_fupdN_wand with "[$]").
    iIntros ">H". do 3 iModIntro.
    iMod "H" as ">($ & HP)".
    by iApply "HPQ".
  Qed.

  Lemma physical_step_wand {E} P Q:
    (|={E}⧗=> P) -∗ (P -∗ Q) -∗ |={E}⧗=> Q.
  Proof using HBUpdFUpd.
    iIntros "HP HPQ".
    iApply (physical_step_wand_later with "[$] [$]").
  Qed.

  Lemma physical_step_fupd {E} P :
    (|={E}⧗=> (|={E}=> P)) ⊣⊢ |={E}⧗=> P.
  Proof.
    unseal.
    do 7 f_equiv.
    induction (S (tr_f (2*a))) as [|n]; simpl; last first.
    { do 3 f_equiv. apply IHn. }
    iSplit; [iIntros ">[$>$] //"|iIntros ">[$$] //"].
  Qed.

  Lemma physical_step_fupd_l {E} P :
    (|={E}=> |={E}⧗=> P) ⊣⊢ |={E}⧗=> P.
  Proof.
    unseal. iSplit.
    - iIntros ">$".
    - iIntros "H !> //".
  Qed.

  Lemma physical_step_intro {E} P :
    ▷ P ⊢ |={E}⧗=> P.
  Proof using HBUpdFUpd.
    iIntros "HP".
    iApply physical_step_step; iSplit.
    - iMod tr_persistent_zero as "$".
      iMod (fupd_mask_subseteq ∅); [set_solver|done].
    - iIntros "? ? //".
      iApply fupd_mask_intro; [set_solver|].
      iIntros "Hclose". iApply (step_fupdN_intro); [done|].
      iModIntro. iNext. by iMod "Hclose".
  Qed.

  Lemma physical_step_tr_use {E} n P :
    ⧗ n -∗ (|={E}⧗=> (⧗ (tr_f n) -∗ £ (tr_f n) ={E}=∗ P)) -∗ |={E}⧗=> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "H⧗ HP" (nlc ntr) "Hsup H£".
    iDestruct (tr_supply_tr_1 with "[$] [$]") as "Hsup".
    iDestruct (tr_supply_snapshot with "[$]") as "[Hsup ?]".
    iDestruct (tr_supply_valid with "[$] [$]") as %?.
    iDestruct (lc_weaken (tr_f (1 + 2 * nlc - (ntr + n)) + tr_f n) with "H£") as "[H£₁ H£₂]".
    { apply tr_f_subadditive'; lia. }
    iMod ("HP" with "[$] [$]") as "HP".
    iApply step_fupdN_S_fupd.
    iApply (step_fupdN_wand with "[$]").
    iIntros "!> >(Hsup & HP)".
    iDestruct (tr_supply_tr_2 with "[Hsup]") as "[$ H⧗]".
    { pose proof (tr_f_mono ntr (ntr + n)).
      by replace (tr_f (ntr + n)) with (tr_f ntr + (tr_f (ntr + n) - tr_f ntr)) by lia. }
    iDestruct (tr_weaken (tr_f n) with "H⧗") as "H⧗".
    { apply Nat.le_add_le_sub_l, tr_f_subadditive'. lia. }
    iMod (fupd_mask_subseteq ∅) as "Hcl"; [set_solver|].
    iModIntro. iMod "Hcl".
    iApply ("HP" with "[$] [$]").
  Qed.

  Local Lemma step_fupdN_sep n (P Q : iProp Σ):
    (|={∅}▷=>^n P) -∗ (|={∅}▷=>^ n Q) -∗ |={∅}▷=>^n P ∗ Q.
  Proof using HBUpdFUpd.
    iIntros "HP HQ".
    iInduction n as [|n] "IH"; first by iFrame.
    simpl. iMod "HP". iMod "HQ". do 2 iModIntro. iMod "HP". iMod "HQ". iModIntro.
    iApply ("IH" with "[$] [$]").
  Qed.

  Lemma physical_step_atomic {E₁} E₂ (P : iProp Σ) :
    (|={E₁, E₂}=> |={E₂}⧗=> |={E₂, E₁}=> P) ⊢ |={E₁}⧗=> P.
  Proof using HBUpdFUpd.
    unseal. iIntros ">H" (nlc ntr) "? ?".
    iMod ("H" with "[$] [$]").
    iApply (step_fupdN_wand with "[$]").
    iIntros "!> >($ & >$) //".
  Qed.

  Lemma physical_step_atomic_inv_subseteq {E₁} E₂ (P : iProp Σ) :
    E₂ ⊆ E₁ →
    (|={E₁}⧗=> P) -∗ (|={E₁, E₂}=> |={E₂}⧗=> |={E₂, E₁}=> P).
  Proof using HBUpdFUpd.
    iIntros (Hse) "H".
    iApply fupd_mask_intro; [done|].
    iIntros "Hback". iApply (physical_step_atomic E₁).
    iMod "Hback" as "_". iModIntro.
    iApply (physical_step_wand with "[$]"). iIntros "$".
    by iApply (fupd_mask_intro_subseteq).
  Qed.

  Lemma physical_step_subseteq {E₁} E₂ (P : iProp Σ) :
    E₂ ⊆ E₁ →
    (|={E₂}⧗=> P) -∗ |={E₁}⧗=> P.
  Proof using HBUpdFUpd.
    iIntros (Hle) "H".
    iApply (physical_step_atomic E₂).
    iMod (fupd_mask_subseteq E₂) as "Hclose"; [done|].
    iModIntro. iApply (physical_step_wand with "[$]").
    by iIntros "$".
  Qed.

  (** The fupdN rule for physical steps. This uses a conjunction to allow additional
      spatial time receipts ⧗ to be used to find the lower bound, but not irreversably
      converted into persistent time receipts.

      This corresponds to laterN in the paper.
  *)
  Lemma physical_step_fupdN_strong {E₁} E₂ n (P Q R : iProp Σ) :
    (|={E₁, ∅}=> ⧖ n) ∧ (
      |={E₁, E₂}=>
        (|={∅}▷=>^(S $ tr_f n) P ={E₂, E₁}=∗ Q) ∗
        (|={E₂}⧗=> P ∗ (Q ={E₁}=∗ R))) -∗
    |={E₁}⧗=> R.
  Proof using HBUpdFUpd.
    unseal. iIntros "H" (nlc ntr) "Hsup H£".
    iApply (fupd_mask_intro); [set_solver|].
    iIntros "Hclose" .
    iApply step_fupdN_S_fupd_l.
    iModDecide (_ ≤ _)%nat gives Hle'.
    { iMod "Hclose" as "_".
      iDestruct "H" as "[>H _]".
      iApply (tr_supply_valid_strong with "[$] [$]").
    }
    iMod "Hclose" as "_".
    iDestruct "H" as "[_ >(HP & HQ)]".
    iMod ("HQ" with "[$] [$]") as "HR".
    iModIntro.
    iDestruct (step_fupdN_sep with "[HP] [$]") as "H".
    { iApply (step_fupdN_le with "[$]"); [|done].
      apply le_n_S, tr_f_mono; lia.
    }
    iApply step_fupdN_S_fupd.
    iApply (step_fupdN_wand with "[$]").
    iIntros "(HPQ & >($ & HP & HQR))".
    iApply (fupd_trans _ E₂).
    iModIntro. iMod ("HPQ" with "HP").
    iMod ("HQR" with "[$]") as "$".
    iApply (fupd_mask_intro_subseteq); [set_solver|done].
  Qed.

  (** The fupdN rule for physical steps. This uses a conjunction to allow additional
      spatial time receipts ⧗ to be used to find the lower bound, but not irreversably
      converted into persistent time receipts.
  *)
  Lemma physical_step_fupdN {E₁} E₂ n (P Q : iProp Σ) :
    (|={E₁, ∅}=> ⧖ n) ∧
      ((|={E₁, E₂}=> |={∅}▷=>^(S $ tr_f n) |={E₂, E₁}=> P) ∗
        |={E₂}⧗=> (P ={E₁}=∗ Q)) -∗
    |={E₁}⧗=> Q.
  Proof using HBUpdFUpd.
    iIntros "H".
    iApply (physical_step_fupdN_strong E₂ n True).
    iSplit; [iDestruct "H" as "[$ _]"|].
    iDestruct "H" as "[_ [>Hupd H]]".
    iSplitR "H".
    - iModIntro.
      iApply (step_fupdN_wand with "[$]").
      iIntros "$ //".
    - iModIntro.
      iApply (physical_step_wand with "[$]").
      iIntros "$".
  Qed.

  (* Increase the persistent time receipt by 1 *)
  Lemma physical_step_incr {E} n (P : iProp Σ) :
    ⧖ n -∗ (|={E}⧗=> (⧖ (tr_f (S n)) ={E}=∗ P)) -∗ |={E}⧗=> P.
  Proof using HBUpdFUpd.
    unseal. iIntros "H⧖ HP" (nlc ntr) "Hsup H£".
    iDestruct (tr_supply_valid_strong with "[$] [$]") as "%".
    iClear "H⧖".
    iMod ("HP" with "[$] [$]") as "HP".
    iApply (step_fupdN_wand with "[$]").
    iIntros "!> >(Hsup & HP) //".
    iDestruct (tr_supply_snapshot with "[$]") as "[$ H⧖]".
    iApply "HP".
    iApply (tr_persistent_weaken with "[$]").
    pose proof (tr_f_mono (S n) (1 + 2*nlc)). lia.
  Qed.

  Global Instance physical_step_contractive {E} : Contractive (physical_step E).
  Proof.
    intros n P Q HPQ. unseal. rewrite /physical_step_def.
    do 7 f_equiv.
    rewrite !Nat.iter_succ.
    f_equiv. f_contractive. f_equiv.
    induction (tr_f (2*a)).
    - by repeat f_equiv.
    - rewrite !Nat.iter_succ.
      by do 3 f_equiv.
  Qed.

  (* Define multiple physical steps for use in soundness and adequacy of WP. *)
  Notation "|={ E }⧗=>^ n P" := (Nat.iter n (physical_step E) P)
    (at level 99, P at level 200, E at level 50, n at level 9, format "|={ E }⧗=>^ n  P") : bi_scope.

  Lemma physical_stepN_intro {E} n P :
    P ⊢ |={E}⧗=>^n P.
  Proof using HBUpdFUpd.
    iIntros. iInduction n as []; first done.
    iApply physical_step_intro.
    by iApply "IHn".
  Qed.

  Lemma physical_stepN_wand {E} n P Q :
    (|={E}⧗=>^n P) -∗ (P -∗ Q) -∗ |={E}⧗=>^n Q.
  Proof using HBUpdFUpd.
    iIntros "HP HPQ". iInduction n as [].
    - by iApply "HPQ".
    - simpl. iApply (physical_step_wand with "HP").
      iIntros "HP".
      iApply ("IHn" with "[$] [$]").
  Qed.

  Lemma physical_stepN_le {E} {n} m P :
    n ≤ m →
    (|={E}⧗=>^n P)%I -∗
    |={E}⧗=>^m P.
  Proof using HBUpdFUpd.
    intros. replace m with ((m - n) + n) by lia.
    rewrite Nat.iter_add.
    iIntros. by iApply physical_stepN_intro.
  Qed.

  Lemma physical_stepN_S_fupd {E} n P :
    (|={E}⧗=>^(S n) (|={E}=> P))%I ⊣⊢ |={E}⧗=>^(S n) P.
  Proof using HBUpdFUpd.
    induction n as [|n].
    { apply physical_step_fupd. }
    remember (S n) as m; simpl.
    iSplit; iIntros "H"; iApply (physical_step_wand with "H"); rewrite IHn; iIntros "$".
  Qed.

  Lemma physical_stepN_fupd_swap {E} n P :
    (|={E}=> |={E}⧗=>^n P) ⊣⊢ |={E}⧗=>^n |={E}=> P.
  Proof using HBUpdFUpd.
    destruct n; first done.
    rewrite physical_stepN_S_fupd physical_step_fupd_l //.
  Qed.

  (* Instances *)
  Global Instance elim_modal_upd_physical_step p E1 P Q :
    ElimModal True p false (|==> P) P (|={E1}⧗=> Q) (|={E1}⧗=> Q).
  Proof using HBUpdFUpd.
    rewrite /ElimModal intuitionistically_if_elim /=.
    iIntros (_) "[HP HPQ]". iApply physical_step_fupd_l.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_modal_fupd_physical_step p E1 P Q :
    ElimModal True p false (|={E1}=> P) P (|={E1}⧗=> Q) (|={E1}⧗=> Q).
  Proof using HBUpdFUpd.
    rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r.
    iIntros (?) "H". by iApply physical_step_fupd_l.
  Qed.

  Global Instance elim_modal_fupd_physical_step_weak p E1 E2 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|={E1}⧗=> Q) (|={E2}⧗=> |={E2,E1}=> Q) | 100.
  Proof using HBUpdFUpd.
    rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r.
    iIntros (_) "H". by iApply physical_step_atomic.
  Qed.

  Global Instance is_except_zero_physical_step E1 P :
    IsExcept0 (|={E1}⧗=> P).
  Proof using HBUpdFUpd.
    unfold IsExcept0. iIntros "HP".
    iApply physical_step_fupd_l.
    by iMod "HP" as "$".
Qed.

  (* Elimination instance for conjunctions. *)
  Global Instance elim_modal_conj (P P' Q₁ Q₂ Q₁' Q₂' : iProp Σ) :
    ElimModal True false false P P' Q₁ Q₁' →
    ElimModal True false false P P' Q₂ Q₂' →
    ElimModal True false false P P' (Q₁ ∧ Q₂) (Q₁' ∧ Q₂')%I.
  Proof.
    rewrite /ElimModal //=.
    iIntros (H1 H2 Hle) "[H HR]".
    iSplit.
    - iApply H1; first done.
      iFrame. iIntros. iDestruct ("HR" with "[$]") as "[$ _]".
    - iApply H2; first done.
      iFrame. iIntros. iDestruct ("HR" with "[$]") as "[_ $]".
  Qed.

End physical_step.

(* Redefine the notations outside of the section. *)
Notation "|={ E }⧗=> P" := (physical_step E P)
  (at level 99, P at level 200, E at level 50, format "|={ E }⧗=>  P") : bi_scope.
Notation "|={ E }⧗=>^ n P" := (Nat.iter n (physical_step E) P)
  (at level 99, P at level 200, E at level 50, n at level 9, format "|={ E }⧗=>^ n  P") : bi_scope.

Section soundness.

  Context `{!tr_generation} `{!BiFUpd (iProp Σ), HBUpdFUpd: !BiBUpdFUpd (iProp Σ)}.

  (* The largest possible persistent time receipt after `ns` steps, given `m` time receipts before the first step. *)
  Local Definition half_tr_per_step m ns :=
    Nat.iter ns (λ n, n + tr_f (1 + 2*n)) m.

  (* The number of later credits necessary to take `k` steps, given `m` time receipts before the first step.
     As we need to know the number of later credits before invoking `physical_stepN_soundness` (fancy_updates.v),
     we give this as a definition.
  *)
  Local Definition lc_up_to_steps m k :=
    sum_list_with (λ ns, tr_f (1 + 2 * half_tr_per_step m ns)) (seq 0 k).

  Local Definition laters_up_to_steps m k :=
    sum_list_with (λ ns, S $ tr_f (2 * half_tr_per_step m ns)) (seq 0 k).

  Local Lemma physical_step_soundness `{!lcGS Σ} `{!trGS Σ} {E} m P :
    tr_supply m 0 -∗ £ (tr_f (1 + 2*m)) -∗ (|={E}⧗=> P) -∗ |={E, ∅}=> |={∅}▷=>^(1 + tr_f (2*m)) |={∅, E}=> tr_supply (m + tr_f (1 + 2*m)) 0 ∗ P.
  Proof using HBUpdFUpd.
    iIntros "? H£ HP". rewrite physical_step_unseal.
    iApply step_fupdN_S_fupd_l.
    iMod ("HP" with "[$] [H£]") as "HP".
    { by rewrite Nat.sub_0_r. }
    do 2 iModIntro. iApply (step_fupdN_wand with "HP").
    iIntros ">(Hsup & $)".
    by rewrite tr_f_zero.
  Qed.

  Lemma physical_stepN_soundness_local `{!lcGS Σ} `{!trGS Σ} {E} m k P :
    tr_supply m 0 -∗
    £ (lc_up_to_steps m k) -∗
    (|={E}⧗=>^k P) -∗
    |={E, ∅}=> |={∅}▷=>^(laters_up_to_steps m k) |={∅, E}=>
        tr_supply (half_tr_per_step m k) 0 ∗ P.
  Proof using HBUpdFUpd.
    iIntros "? H£ HP".
    iInduction k as [] forall (m P).
    { simpl. iFrame. iApply fupd_mask_intro_subseteq; [set_solver|done]. }
    rewrite Nat.iter_succ_r.
    rewrite /lc_up_to_steps /laters_up_to_steps !seq_S !sum_list_with_app !Nat.iter_add /= Nat.add_0_r.
    iDestruct "H£" as "[H£ H£']".
    iDestruct ("IHk" with "[$] [$] [$]") as ">HP".
    iApply (step_fupdN_wand with "[$]").
    iIntros "!> HP".
    iApply step_fupdN_S_fupd_l. iMod "HP" as "[Hsup HP]".
    iApply (physical_step_soundness with "[$] [$] [$]").
  Qed.
End soundness.

From iris.base_logic.lib Require Export later_credits fancy_updates.
Lemma physical_stepN_soundness `{!invGpreS Σ, !trGpreS Σ, !tr_generation} (P : iProp Σ) `{!Plain P} (hlc : has_lc) n k :
    (∀ {Hinv : invGS_gen hlc Σ} {Htr: trGS Σ}, ⧗ n ∗ £ n ⊢ |={⊤}=> |={⊤}⧗=>^k |={⊤, ∅}=> P) → ⊢ P.
Proof.
  intros HP.
  eapply (step_fupdN_soundness_gen _ hlc _ _).
  iIntros (Hinv) "[H£ H£']".
  iMod (tr_supply_alloc n) as "(%Htr & Hsup)".
  replace n with (0 + n) by done.
  iDestruct (tr_supply_tr_2 with "Hsup") as "(Hsup&H⧗)". simpl.
  iDestruct (HP with "[$]") as ">HP".
  iDestruct (physical_stepN_soundness_local with "[$] [$] [$]") as ">HP'".
  iApply step_fupdN_fupd_swap. iApply (step_fupdN_wand with "[$]").
  iIntros "[_ >>$] //".
Qed.


