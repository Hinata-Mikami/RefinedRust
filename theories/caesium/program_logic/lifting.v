(** From the CPP'26 paper "Building Blocks for Step-Indexed Program Logics",
    by Thomas Somers, Jonas Kastberg Hinrichsen, Lennard Gäher, and Robbert Krebbers.
*)
(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From caesium.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma wp_lift_step_physical_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt -∗
    (|={E,∅}=> ⌜if s is NotStuck then reducible e1 σ1 else True⌝) ∧
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
      |={E}⧗=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->.
  iIntros "H" (?????) "Hstate". iSplit.
  - by iDestruct ("H" with "[$]") as "[>$ _]".
  - iIntros (????).
    iDestruct ("H" with "[$] [//]") as "H".
    iApply (physical_step_wand with "[$]").
    iIntros "$".
Qed.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ (tr_f 1) ={∅}▷=∗ |={∅,E}=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hwp". rewrite -wp_lift_step_physical_step; [|done].
  iIntros (?????) "Hσ". iSplit.
  { by iDestruct ("Hwp" with "[$]") as ">[$ _]". }
  iIntros (????). iApply (physical_step_step). iSplit.
  { iMod (tr_persistent_zero) as "$". iApply (fupd_mask_intro); [set_solver|iIntros]. done. }
  iIntros "H£ H⧗".
  iMod ("Hwp" with "Hσ") as "[_ Hwp]".
  iDestruct ("Hwp" with "[//] [$]") as "Hwp".
  iModIntro. rewrite tr_f_zero. iApply (step_fupd_wand with "Hwp").
  iIntros ">($ & $ & $) //".
Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 ns κ κs nt) "Hσ".
  iDestruct ("H" with "Hσ") as "H".
  iSplit; iMod "H" as "%H"; first done.
  destruct H as [_ Hirr].
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ (tr_f 1) ={∅,E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % Hcred !> !>". by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork_pstep `{!Inhabited (state Λ)} s E Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ -∗ |={E}⧗=> WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_physical_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 ns κ κs nt) "Hσ". iSplit.
  { iMod (fupd_mask_subseteq ∅) as "_"; [set_solver|]. iModIntro. iPureIntro. destruct s; done. }
  iIntros (e2 σ2 efs ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iApply physical_step_fupd. iApply (physical_step_wand with "(H [//])").
  iIntros "$". iMod (fupd_mask_subseteq ∅) as "Hcl"; [set_solver|].
  iMod (state_interp_mono with "Hσ") as "$".
  iMod "Hcl". by simpl.
Qed.

Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E}[E']▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ -∗ £ (tr_f 1) -∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 ns κ κs nt) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?) "Hcred".
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod (state_interp_mono with "Hσ") as "$".
  iMod "Hclose" as "_". iMod "H". iModIntro.
  by iDestruct ("H" with "[//] Hcred") as "$".
Qed.

Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ (tr_f 1) ={E1}[E2]▷=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 efs ?) "Hcred". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#] Hcred") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply fupd_mask_intro_subseteq; [set_solver|].
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ (tr_f 1) ={E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "Hcred !> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step_no_fork_pstep `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}⧗=>  WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork_pstep s E); try done.
  { naive_solver. }
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> £ (tr_f 1) -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_physical_step `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}⧗=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; first done.
  iApply wp_lift_pure_det_step_no_fork_pstep.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - simpl. iApply (physical_step_wand with "Hwp").
    iApply "IH".
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n £ (tr_f 1 * n) -∗ ⧗ (tr_f 1 * n) -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". iApply wp_pure_step_physical_step; [done|].
  clear Hexec.
  iInduction n as [|n]; simpl.
  { rewrite !Nat.mul_0_r. iMod tr_zero as "?". iMod lc_zero as "?".
    iApply ("Hwp" with "[$] [$]"). }
  iMod tr_persistent_zero as "H⧖".
  iApply (physical_step_intro_trp with "[$]"); simpl.
  iIntros "H£ H⧗". iMod "Hwp". do 2 iModIntro. iMod "Hwp". iModIntro.
  rewrite tr_f_zero !Nat.mul_succ_r /=. iApply "IHn". iApply (step_fupdN_wand with "[$]").
  iIntros "Hcl H£' H⧗'".
  iCombine "H£' H£" as "?". iCombine "H⧗' H⧗" as "?".
  iApply ("Hcl" with "[$] [$]").
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n (£ (tr_f 1 * n)  -∗ ⧗ (tr_f 1 * n) -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P ⊢ |={E}▷=>^n P) as Hwp by apply Hwp. intros ?.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.

