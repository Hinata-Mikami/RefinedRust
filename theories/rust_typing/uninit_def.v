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
    st_has_op_type ot mt :=
      ∃ ly, syn_type_has_layout st ly ∧
      match mt with
      | MCId =>
          ot = UntypedOp ly
      | _ =>
          ot_layout ot = ly
      end;
    st_syn_type := st;
  |}.
  Next Obligation.
    intros. simpl. iIntros "(%ly & ? & ?)"; eauto.
  Qed.
  Next Obligation.
    intros st ot mt (ly & Hst & ?).
    destruct mt; subst; done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. iIntros (st ot mt ? π ? v (ly & ? & Heq)) "(%ly' & % & %)".
    assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
    destruct mt.
    - done.
    - subst. iExists (ot_layout ot). iPureIntro; split; first done.
      apply has_layout_val_mem_cast. done.
    - subst. done.
  Qed.
  Next Obligation.
    intros st mt ly Hst.
    simpl. exists ly. split; first done.
    destruct mt; done.
  Qed.

  Global Instance uninit_copy st : Copyable (uninit st).
  Proof. apply _. Qed.

  Lemma uninit_own_spec π v st r :
    (v ◁ᵥ{π} r @ uninit st)%I ≡ (∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝)%I.
  Proof.
    rewrite /ty_own_val/=; iSplit.
    - iIntros "(%ly & ? & ?)"; iExists ly. iFrame.
    - iIntros "(%ly & ? & ?)"; iExists ly. iFrame.
  Qed.

  Lemma uninit_memcast π v r st ot hst :
    v ◁ᵥ{π} r @ uninit st -∗
    mem_cast v ot hst ◁ᵥ{π} r @ uninit st.
  Proof.
    rewrite !uninit_own_spec.
    iIntros "(%ly & %Hst & %Hly)".
    iExists ly. iR. iPureIntro.
    by apply has_layout_val_mem_cast.
  Qed.
End uninit.

Notation "uninit< st >" := (uninit st) (only printing, format "'uninit<' st '>'") : printing_sugar.
