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

  (* homogeneous subtyping.
     We basically only want this for type parameters of an enum.
     If T <: U, then option T <: option U.
     otherwise, don't need anything.
  *)
  Import EqNotations.
  Definition enum_incl {rt} (e1 e2 : enum rt) : iProp Σ :=
    ⌜e1.(enum_els) = e2.(enum_els)⌝ ∗
    ⌜e1.(enum_tag) = e2.(enum_tag)⌝ ∗
    (∀ r, ∃ (Heq : e1.(enum_rt) r = e2.(enum_rt) r),
      ⌜(st_of (enum_ty e1 r) MetaNone) = (st_of (enum_ty e2 r) MetaNone)⌝ ∗
      type_incl (rew [RT_rt]Heq in e1.(enum_r) r) (e2.(enum_r) r) (rew Heq in e1.(enum_ty) r) (e2.(enum_ty) r))
  .
  Global Instance enum_incl_pers {rt} (e1 e2 : enum rt) : Persistent (enum_incl e1 e2).
  Proof. apply _. Qed.

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
    iDestruct "Hl" as "(%el & %tag & %variant_ly & -> & %Hst & %Htag' & %Hlook & %Hst'  & %Hlyl & Htag & Hpad1 & Hdata & Hpad2)".
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

  Definition full_enum_incl E L {rt} (e1 e2 : enum rt) : Prop :=
    ∀ qL : Qp, llctx_interp_noend L qL -∗ elctx_interp E -∗ enum_incl e1 e2.

  Lemma enum_incl_refl {rt} (e : enum rt) : ⊢ enum_incl e e.
  Proof.
    iR. iR. iIntros (r). iExists eq_refl. iR. iApply type_incl_refl.
  Qed.

  Lemma enum_incl_trans {rt} (e1 e2 e3 : enum rt) :
    enum_incl e1 e2 -∗ enum_incl e2 e3 -∗ enum_incl e1 e3.
  Proof.
    iIntros "(%Hels1 & %Htag1 & #H12) (%Hels2 & %Htag2 & #H23)".
    iSplitR; first (iPureIntro; congruence).
    iSplitR; first (iPureIntro; congruence).
    iIntros (r).
    iDestruct ("H12" $! r) as "(%H12 & %Hst12 & H12')".
    iDestruct ("H23" $! r) as "(%H23 & %Hst23 & H23')".
    iExists (eq_trans H12 H23). iSplitR; first (iPureIntro; congruence).
    iClear "H12 H23". iRevert "H12' H23'".
    generalize (enum_r e3 r), (enum_ty e3 r), (enum_r e2 r), (enum_ty e2 r),
      (enum_r e1 r), (enum_ty e1 r).
    generalize H12, H23.
    generalize (enum_rt e1 r), (enum_rt e2 r), (enum_rt e3 r).
    intros rt1 rt2 rt3 -> -> r3 ty3 r2 ty2 r1 ty1. simpl.
    iIntros "H12 H23". iApply (type_incl_trans with "H12 H23").
  Qed.

  Global Instance full_enum_incl_refl E L {rt} : Reflexive (full_enum_incl E L (rt:=rt)).
  Proof. intros e. iIntros (?) "_ _". iApply enum_incl_refl. Qed.

  Lemma full_enum_incl_trans E L {rt} (e1 e2 e3 : enum rt) :
    full_enum_incl E L e1 e2 → full_enum_incl E L e2 e3 → full_enum_incl E L e1 e3.
  Proof.
    intros H12 H23. iIntros (?) "HL HE".
    iPoseProof (H12 with "HL HE") as "#H12".
    iPoseProof (H23 with "HL HE") as "#H23".
    iApply (enum_incl_trans with "H12 H23").
  Qed.

  Lemma full_enum_incl_acc E L {rt} (e1 e2 : enum rt) :
    full_enum_incl E L e1 e2 →
    elctx_interp E -∗ llctx_interp L -∗ enum_incl e1 e2.
  Proof.
    intros Hincl. iIntros "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iApply (Hincl with "HL HE").
  Qed.

  (** Structural parameter subtyping preserves the refinement projection. *)
  Lemma full_enum_incl_intro E L {rt} (e1 e2 : enum rt)
      (Heq : ∀ r, enum_rt e1 r = enum_rt e2 r) :
    enum_els e1 = enum_els e2 →
    enum_tag e1 = enum_tag e2 →
    (∀ r, rew [RT_rt] (Heq r) in enum_r e1 r = enum_r e2 r) →
    (∀ r, full_subtype E L (rew [type] (Heq r) in enum_ty e1 r) (enum_ty e2 r)) →
    full_enum_incl E L e1 e2.
  Proof.
    intros Hels Htag Hr Hsub. iIntros (qL) "HL #HE".
    iR. iR. iIntros (r). iExists (Heq r).
    iPoseProof (full_subtype_acc_noend with "HE HL") as "(%Hst & #Hincl)"; first apply (Hsub r).
    iSplitR.
    { iPureIntro. specialize (Hst MetaNone). revert Hst.
      generalize (Heq r). intros H. destruct H. done. }
    rewrite Hr. iApply "Hincl".
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
