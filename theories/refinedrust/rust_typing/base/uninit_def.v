From refinedrust Require Export type.
From refinedrust Require Import options.

(** * Uninitialized memory *)

(** This file just contains the uninit type definition (without rules), because we need it for the struct ltype definition.
  The rules are in [uninit.v]. *)

(** The [uninit] type allows to give a predicate that needs to hold for all bytes
  owned by the type. *)
Section uninit.
  Context `{!typeGS Σ}.

  Program Definition uninit (st : syn_type) : type unitRT := {|
    st_own π _ v :=
        (∃ ly, ⌜syn_type_has_layout st ly⌝ ∗
        ⌜v `has_layout_val` ly⌝)%I;
    st_has_op_type ot :=
      ∃ ly, syn_type_has_layout st ly ∧
          ot = UntypedOp ly;
    st_syn_type := UntypedSynType st;
  |}.
  Next Obligation.
    intros. simpl. iIntros "(%ly & %Hst & %)".
    iExists ly. iPureIntro. split; last done.
    by apply syn_type_has_layout_untyped.
  Qed.
  Next Obligation.
    intros st ot (ly & Hst & ?).
    apply syn_type_has_layout_untyped.
    subst. done.
  Qed.
  Next Obligation.
    intros st ot (ly & Hst & Hot).
    subst; constructor.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. iIntros (st ot st' π [] v (ly & Hst & Hot)) "(%ly' & %Hst' & %Hly')".
    subst ot.
    iExists (OVUntyped ly v). iPureIntro.
    simp decode_op_val.
    rewrite bool_decide_true; last first.
    { assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj. done. }
    done.
  Qed.
  Next Obligation.
    simpl. iIntros (st ot st' π [] v ov (ly & Hst & Hot) Hsame) "(%ly' & %Hst' & %Hly')".
    subst ot.
    iExists ly. iPureIntro. split; first done.
    pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly.
    rewrite /has_layout_val /= in Hly. done.
  Qed.
  Next Obligation.
    intros st ly Hst.
    simpl in Hst.
    apply syn_type_has_layout_untyped_inv in Hst.
    exists ly. done.
  Qed.

  Global Instance uninit_copy st : Copyable (uninit st).
  Proof. apply _. Qed.

  Global Instance uninit_sized st : TySized (uninit st).
  Proof. apply _. Qed.

  Lemma uninit_own_spec π v st m r :
    (v ◁ᵥ{π, m} r @ uninit st)%I ≡ (⌜m = MetaNone⌝ ∗ ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝)%I.
  Proof.
    rewrite /ty_own_val/=; iSplit.
    - iIntros "(-> & %ly & ? & ?)"; iR. iExists ly. by iFrame.
    - iIntros "(-> & %ly & ? & ?)"; iR. iExists ly. iFrame.
  Qed.
End uninit.

Section lemmas.
  Context `{!typeGS Σ}.
  Implicit Types (rt : RT).

  Lemma owned_type_incl_uninit' π {rt1 : RT} (r1 : rt1) r2 (ty1 : type rt1) st :
    syn_type_size_eq (ty_syn_type ty1 MetaNone) st →
    ⊢ owned_type_incl π r1 r2 ty1 (uninit st).
  Proof.
    iIntros (Hst). iSplitR; last iSplitR.
    - iPureIntro. simpl.
      trans st; first done.
      eapply syn_type_size_eq_untyped_r.
    - simpl. eauto.
    - iIntros (v) "Hv".
      rewrite uninit_own_spec.
      iEval (rewrite /ty_own_val/=).
      iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Hst' & %Hly)".
      iR.
      apply Hst in Hst' as (ly2 & Hst' & ?).
      iExists ly2. iR. iPureIntro. rewrite /has_layout_val Hly.
      done.
  Qed.
  Lemma owned_type_incl_uninit π {rt1 : RT} (r1 : rt1) r2 (ty1 : type rt1) st :
    st = ty_syn_type ty1 MetaNone →
    ⊢ owned_type_incl π r1 r2 ty1 (uninit st).
  Proof.
    iIntros (Hst). iSplitR; last iSplitR.
    - iPureIntro.
      simpl. subst st.
      apply syn_type_size_eq_untyped_r.
    - simpl. eauto.
    - iIntros (v) "Hv". rewrite uninit_own_spec.
      iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst' & %Hly)".
      iR.
      iExists ly. subst st. iR. done.
  Qed.

  Lemma owned_type_incl_uninit_size_eq π st1 st2 :
    syn_type_size_eq st1 st2 →
    ⊢ owned_type_incl π () () (uninit st1) (uninit st2).
  Proof.
    iIntros (?). iApply owned_type_incl_uninit'.
    etrans; first apply syn_type_size_eq_untyped_l.
    done.
  Qed.
End lemmas.

Notation "uninit< st >" := (uninit st) (only printing, format "'uninit<' st '>'") : printing_sugar.
