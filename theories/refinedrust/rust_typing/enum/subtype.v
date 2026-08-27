From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.


Section subtype.
  Context `{!typeGS Σ}.

  (** Refinement-specific inclusion of the selected payload.  Layout equality
      also preserves the tag encoding and both padding regions. *)
  Definition enum_t_incl_precond {rt1 rt2} π pers
      (e1 : enum rt1) (e2 : enum rt2) r1 r2 : iProp Σ :=
    ⌜enum_els e1 = enum_els e2⌝ ∗
    ⌜enum_tag e1 r1 = enum_tag e2 r2⌝ ∗
    ⌜ty_syn_type (enum_ty e1 r1) MetaNone = ty_syn_type (enum_ty e2 r2) MetaNone⌝ ∗
    □?pers owned_type_incl π (enum_r e1 r1) (enum_r e2 r2)
      (enum_ty e1 r1) (enum_ty e2 r2).

  Lemma enum_t_own_val_mono {rt1 rt2} π pers
      (e1 : enum rt1) (e2 : enum rt2) r1 r2 m v :
    enum_t_incl_precond π pers e1 e2 r1 r2 -∗
    v ◁ᵥ{π, m} r1 @ enum_t e1 -∗ v ◁ᵥ{π, m} r2 @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & %Hst & Hincl) Hv".
    iPoseProof (bi.intuitionistically_if_elim with "Hincl") as "(_ & _ & Hincl)".
    rewrite /ty_own_val /= enum_own_val_unfold /enum_own_val_def.
    iDestruct "Hv" as "(%el & %tag & %ly & -> & %Halg & %Ht & %Hlook & %Hly & Htag & Hpad & Hv & Htail)".
    rewrite -Hels -Htag -Hst.
    iExists el, tag, ly. do 5 (iSplitR; first done).
    iFrame. by iApply "Hincl".
  Qed.

  Definition enum_t_incl_precond_strong {rt1 rt2}
      (e1 : enum rt1) (e2 : enum rt2) r1 r2 : iProp Σ :=
    ⌜enum_els e1 = enum_els e2⌝ ∗
    ⌜enum_tag e1 r1 = enum_tag e2 r2⌝ ∗
    ⌜∀ m, ty_syn_type (enum_ty e1 r1) m = ty_syn_type (enum_ty e2 r2) m⌝ ∗
    type_incl (enum_r e1 r1) (enum_r e2 r2) (enum_ty e1 r1) (enum_ty e2 r2).
  Global Instance enum_t_incl_precond_strong_pers {rt1 rt2}
      (e1 : enum rt1) (e2 : enum rt2) r1 r2 :
    Persistent (enum_t_incl_precond_strong e1 e2 r1 r2).
  Proof. apply _. Qed.

  Lemma enum_t_incl_precond_from_strong {rt1 rt2} π
      (e1 : enum rt1) (e2 : enum rt2) r1 r2 :
    enum_t_incl_precond_strong e1 e2 r1 r2 -∗
    enum_t_incl_precond π true e1 e2 r1 r2.
  Proof.
    iIntros "(%Hels & %Htag & %Hst & #Hincl)". iR. iR. iR.
    iApply (type_incl_owned_type_incl with "[] Hincl").
    iPureIntro. intros m. rewrite Hst. apply syn_type_size_eq_refl.
  Qed.

  Lemma enum_t_shr_mono {rt1 rt2}
      (e1 : enum rt1) (e2 : enum rt2) r1 r2 κ π m l :
    enum_t_incl_precond_strong e1 e2 r1 r2 -∗
    l ◁ₗ{π, m, κ} r1 @ enum_t e1 -∗ l ◁ₗ{π, m, κ} r2 @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & %Hst & #Hincl) Hl".
    iDestruct "Hincl" as "(_ & _ & #Hincl)".
    rewrite /ty_shr /= enum_shr_unfold /enum_shr_def.
    iDestruct "Hl" as "(%el & %tag & %ly & -> & %Halg & %Ht & %Hlook & %Hly & %Hloc & Htag & Hpad & Hl & Htail)".
    rewrite -Hels -Htag -Hst.
    iExists el, tag, ly. do 6 (iSplitR; first done).
    iFrame. by iApply "Hincl".
  Qed.

  Lemma enum_t_type_incl {rt1 rt2} (e1 : enum rt1) (e2 : enum rt2) r1 r2 :
    enum_t_incl_precond_strong e1 e2 r1 r2 -∗
    type_incl r1 r2 (enum_t e1) (enum_t e2).
  Proof.
    iIntros "#Hincl". iSplitR; first done. iSplit; iModIntro.
    - iIntros (π m v). iApply (enum_t_own_val_mono _ true).
      by iApply enum_t_incl_precond_from_strong.
    - iIntros (κ π m l). by iApply enum_t_shr_mono.
  Qed.

  Lemma enum_own_val_mono {rt} (e1 e2 : enum rt) r m :
    enum_incl e1 e2 -∗
    ∀ π v, v ◁ᵥ{π, m} r @ enum_t e1 -∗ v ◁ᵥ{π, m} r @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & #Hincl)".
    iIntros (π v) "Hv".
    rewrite /ty_own_val/= enum_own_val_unfold/enum_own_val_def.
    iDestruct "Hv" as "(%el & %tag & %variant_ly & -> & %Hst & %Htag' & %Hlook & %Hst'  & Htag & Hpad1 & Hdata & Hpad2)".
    iDestruct ("Hincl" $! r) as "(%Heq & %Hst_eq & Hincl')".
    iDestruct "Hincl'" as "(_ & #Hvincl & _)".
    rewrite -Hels. rewrite -Htag.
    iExists _, _, _. iR. iR. iR. iR.
    rewrite -Hst_eq. iR.
    iFrame.
    iApply "Hvincl".
    destruct Heq. done.
  Qed.
  Lemma enum_shr_mono {rt} (e1 e2 : enum rt) r m :
    enum_incl e1 e2 -∗
    ∀ κ π l, l ◁ₗ{π, m, κ} r @ enum_t e1 -∗ l ◁ₗ{π, m, κ} r @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & #Hincl)".
    iIntros (κ π l) "Hl".
    rewrite /ty_shr/= enum_shr_unfold/enum_shr_def.
    iDestruct "Hl" as "($ & %el & %tag & %variant_ly & -> & %Hst & %Htag' & %Hlook & %Hst'  & %Hlyl & Htag & Hpad1 & Hdata & Hpad2)".
    iDestruct ("Hincl" $! r) as "(%Heq & %Hst_eq & Hincl')".
    iDestruct "Hincl'" as "(_ & _ & #Hsincl)".
    rewrite -Hels. rewrite -Htag.
    iExists el, tag, variant_ly.
    iR. iR. iR. iR.
    rewrite -Hst_eq. iR.
    iR. iFrame.
    iApply "Hsincl".
    destruct Heq. done.
  Qed.

  Lemma enum_type_incl {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    type_incl r r (enum_t e1) (enum_t e2).
  Proof.
    iIntros "#Hincl".
    iPoseProof "Hincl" as "(%Hels & %Htag & #Hincl')".
    iR.
    iSplit; iModIntro.
    - iIntros (???) "?". by iApply enum_own_val_mono.
    - iIntros (????) "?". by iApply enum_shr_mono.
  Qed.

  Lemma enum_full_subtype E L {rt} (e1 e2 : enum rt) :
    full_enum_incl E L e1 e2 →
    full_subtype E L (enum_t e1) (enum_t e2).
  Proof.
    intros Hsubt r. iIntros (?) "HL #HE".
    simpl.
    iPoseProof (Hsubt with "HL HE") as "(%Hst_eq & % & ?)".
    rewrite Hst_eq. iR.
    iApply enum_type_incl. iR. iR. done.
  Qed.
End subtype.
