From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype.
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
      type_incl (rew [RT_rt]Heq in e1.(enum_r) r) (e2.(enum_r) r) (rew Heq in e1.(enum_ty) r) (e2.(enum_ty) r))
  .
  Global Instance enum_incl_pers {rt} (e1 e2 : enum rt) : Persistent (enum_incl e1 e2).
  Proof. apply _. Qed.

  Lemma enum_own_val_mono {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    ∀ π v, v ◁ᵥ{π} r @ enum_t e1 -∗ v ◁ᵥ{π} r @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & #Hincl)".
    iIntros (π v) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%ly & %tag & %Hst & %Htag' & Hv)".
    iDestruct ("Hincl" $! r) as "(%Heq & Hincl')".
    iExists ly, tag.
    rewrite -Hels. iR. rewrite -Htag. iR.
    simpl.
    (* TODO: somehow specializing with Hv doesn't work *)
    iApply (struct_t_own_val_mono with "[]"); last done.
    rewrite /struct_t_incl_precond. simpl.
    iFrame.
    iSplit. { rewrite Hels. iApply type_incl_refl. }
    iSplit; last done.
    simpl. iApply active_union_type_incl; first done.
    destruct Heq. done.
  Qed.
  Lemma enum_shr_mono {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    ∀ κ π l, l ◁ₗ{π, κ} r @ enum_t e1 -∗ l ◁ₗ{π, κ} r @ enum_t e2.
  Proof.
    iIntros "(%Hels & %Htag & #Hincl)".
    iIntros (κ π l) "Hl".
    rewrite /ty_shr/=.
    iDestruct "Hl" as "(%ly & %tag & %Hst & %Htag' & Hl)".
    iDestruct ("Hincl" $! r) as "(%Heq & Hincl')".
    iExists ly, tag.
    rewrite -Hels. rewrite -Htag. iR. iR.
    iApply (struct_t_shr_mono with "[] Hl").
    rewrite /struct_t_incl_precond. simpl.
    iSplit. { rewrite Hels. iApply type_incl_refl. }
    iSplit; last done.
    simpl. iApply active_union_type_incl; first done. destruct Heq. done.
  Qed.

  Lemma enum_type_incl {rt} (e1 e2 : enum rt) r :
    enum_incl e1 e2 -∗
    type_incl r r (enum_t e1) (enum_t e2).
  Proof.
    iIntros "#Hincl".
    iPoseProof "Hincl" as "(%Hels & %Htag & #Hincl')".
    iSplitR. { simpl. rewrite Hels //. }
    iSplitR. { iModIntro. simpl. eauto. }
    iSplit; iModIntro.
    - by iApply enum_own_val_mono.
    - by iApply enum_shr_mono.
  Qed.

  Definition full_enum_incl E L {rt} (e1 e2 : enum rt) : Prop :=
    ∀ qL : Qp, llctx_interp_noend L qL -∗ elctx_interp E -∗ enum_incl e1 e2.

  Lemma enum_full_subtype E L {rt} (e1 e2 : enum rt) :
    full_enum_incl E L e1 e2 →
    full_subtype E L (enum_t e1) (enum_t e2).
  Proof.
    intros Hsubt r. iIntros (?) "HL #HE".
    iApply enum_type_incl.
    iApply (Hsubt with "HL HE").
  Qed.
End subtype.
