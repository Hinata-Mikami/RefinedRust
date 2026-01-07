From caesium Require Export tactics lifting proofmode.
Set Default Proof Using "Type".

Section derived.
  Context `{refinedcG Σ} `{ALG : LayoutAlg}.

  Lemma wps_annot A (a : A) π Q Ψ s:
    (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗ WPs{π} AnnotStmt 1 a s {{ Q , Ψ }}.
  Proof using ALG.
    iIntros "Hs".
    rewrite /AnnotStmt /SkipES /=.
    wps_bind. iApply wp_skip.
    iApply (physical_step_wand with "Hs"). iIntros "Hs".
    iApply wps_exprs.
    iApply physical_step_intro.
    iNext. done.
  Qed.

  Lemma step_fupdN_add (Ei Eo : coPset) (n m : nat) (P : iProp Σ) :
    (|={Eo}[Ei]▷=>^(n + m) P)%I ⊣⊢ (|={Eo}[Ei]▷=>^n (|={Eo}[Ei]▷=>^m P))%I.
  Proof.
    induction n as [ | n IH]; simpl; first done.
    rewrite IH. done.
  Qed.

  Lemma step_fupd_fupdN_commute (Ei Eo : coPset) (n : nat) (P : iProp Σ) :
    (|={Eo}[Ei]▷=> (|={Eo}[Ei]▷=>^n P))%I ⊣⊢ (|={Eo}[Ei]▷=>^n (|={Eo}[Ei]▷=> P))%I.
  Proof.
    induction n as [ | n IH]; simpl; first done.
    rewrite IH. done.
  Qed.

  Lemma step_fupdN_commute (Ei Eo : coPset) (n m : nat) (P : iProp Σ) :
    (|={Eo}[Ei]▷=>^m (|={Eo}[Ei]▷=>^n P))%I ⊣⊢ (|={Eo}[Ei]▷=>^n (|={Eo}[Ei]▷=>^m P))%I.
  Proof.
    induction n as [ | n IH]; simpl; first done.
    rewrite -IH. rewrite -step_fupd_fupdN_commute. done.
  Qed.

  Lemma step_fupd_fupdN_fupd Ei Eo n (P : iProp Σ) :
    (|={Eo}[Ei]▷=> (|={Eo}[Ei]▷=>^n P))%I ⊣⊢ (|={Eo}[Ei]▷=> (|={Eo}[Ei]▷=>^n |={Eo}=> P))%I.
  Proof.
    induction n as [ | n IH]; simpl.
    - iSplit.
      + simpl. iIntros "Ha". iApply (step_fupd_wand with "Ha"). iApply fupd_intro.
      + rewrite (fupd_trans Ei Eo Eo). eauto.
    - rewrite IH. done.
  Qed.

  Lemma step_fupd_fupd' Ei Eo (P : iProp Σ)  :
    ⊢ ((|={Eo}[Ei]▷=> |={Eo}=> P) -∗ |={Eo}[Ei]▷=> P)%I.
  Proof.
    rewrite -step_fupd_fupd. eauto.
  Qed.

  Lemma fupd_fupdN_fupd Ei Eo n (P : iProp Σ)  :
    ⊢ ((|={Eo}=> |={Eo}[Ei]▷=>^n |={Eo}=> P) -∗ |={Eo}=> |={Eo}[Ei]▷=>^n P)%I.
  Proof.
    induction n; simpl.
    - iIntros ">>Ha". eauto.
    - iIntros ">Ha". iModIntro.
      iApply step_fupd_fupd'.
      iApply (step_fupd_wand with "Ha"). iIntros "Ha". iApply (IHn with "[Ha]").
      eauto.
  Qed.

  Lemma fupd_step_fupdN_S E E' n (P : iProp Σ) :
    E' ⊆ E →
    (|={E}=> P) -∗ (|={E}[E']▷=>^(S n) P).
  Proof.
    iIntros (?) "HP".
    simpl. rewrite step_fupd_fupdN_fupd. iApply step_fupd_intro; first done.
    iNext. iApply step_fupdN_intro; first done. done.
  Qed.

  Lemma step_fupdN_S_fupd E E' n (P : iProp Σ) :
    E' ⊆ E →
    (|={E}[E']▷=>^(S n) P) ⊣⊢ (|={E}[E']▷=>^(S n) |={E}=> P).
  Proof.
    iIntros (?). iSplit.
    - iIntros "Ha". iApply (step_fupdN_wand with "Ha"). eauto.
    - iIntros "Ha". simpl. iApply step_fupd_fupd.
      iApply (step_fupd_wand with "Ha"). iIntros "Ha".
      iApply fupd_fupdN_fupd. eauto.
  Qed.

  Lemma step_fupdN_succ E E' n (P : iProp Σ) :
    (|={E}[E']▷=> |={E}[E']▷=>^n P) ⊣⊢ |={E}[E']▷=>^(S n) P.
  Proof. done. Qed.

  Lemma step_fupdN_mono_n (n m : nat) E1 E2 (P : iProp Σ) :
    E2 ⊆ E1 → n ≤ m → ⊢ (|={E1}[E2]▷=>^n P) -∗ |={E1}[E2]▷=>^m P.
  Proof.
    iIntros (? Hle) "HP".
    iInduction n as [ | n]  "IH" forall (m Hle).
    - iApply step_fupdN_intro; first done. simpl. eauto.
    - simpl. destruct m as [ | m]; first done.
      simpl. iApply (step_fupd_wand with "HP").
      iApply "IH". iPureIntro. lia.
  Qed.

  Lemma step_fupdN_zip n E (P Q : iProp Σ) :
    ⊢ (|={E}▷=>^n P) -∗ (|={E}▷=>^n Q) -∗ |={E}▷=>^n (P ∗ Q).
  Proof.
    iIntros "HP HQ".
    iInduction n as [ | n] "IH".
    - simpl. iFrame.
    - simpl. iMod "HP". iMod "HQ".
      iModIntro. iNext. iMod "HP". iMod "HQ".
      iModIntro. iApply ("IH" with "HP HQ").
  Qed.

  Lemma step_fupd_subseteq F1 F2 (P : iProp Σ) :
    F2 ⊆ F1 →
    (|={F2}▷=> P) -∗ |={F1}▷=> P.
  Proof.
    iIntros (?) "HP".
    iMod (fupd_mask_subseteq F2) as "Hcl"; first done.
    iMod "HP". iMod "Hcl" as "_".
    iModIntro. iNext.
    iMod (fupd_mask_subseteq F2) as "Hcl"; first done.
    iMod "HP". iMod "Hcl" as "_". done.
  Qed.

  Lemma step_fupdN_ne n Ei Eo :
    NonExpansive (Nat.iter n (fun (P : iProp Σ) => fupd Eo Ei (bi_later (fupd Ei Eo P)))).
  Proof.
    intros m P1 P2 Heq. induction n as [ | n IH].
    - f_equiv. apply Heq.
    - simpl. do 3 f_equiv. apply IH.
  Qed.
End derived.
