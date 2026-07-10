From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.


Section subtype.
  Context `{!typeGS Σ}.

  (* TODO: should probably have a subtyping condition on enum that lifts this element-wise. *)

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
