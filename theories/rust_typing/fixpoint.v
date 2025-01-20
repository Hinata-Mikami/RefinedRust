From refinedrust Require Import type.
From iris.prelude Require Import options.

Section fixpoint_def.
  Context `{!typeGS Σ}.

  (* We need [Inhabited T_rt] because of [ty_rt_inhabited]. *)
  Context {T_rt : Type} `{!Inhabited T_rt} (T : type T_rt → type T_rt) {HT : TypeContractive T}.

  Global Program Instance simple_type_inhabited : Inhabited (simple_type T_rt) := populate {|
      st_own π r v := ⌜v = []⌝%I;
      st_syn_type := UnitSynType;
      st_has_op_type ot _ := ot = UntypedOp unit_sl;
  |}.
  Next Obligation.
    simpl. 
    iIntros (??? ->).
    iExists unit_sl. iPureIntro. 
    split. 
    - by apply syn_type_has_layout_unit.
    - done.
  Qed.
  Next Obligation.
    simpl. intros ? ? ->. done.
  Qed.
  Next Obligation.
    simpl. intros ??? ??? ->.
    iIntros "->".
    destruct mt; simpl; iPureIntro; done.
  Qed.
  Global Instance type_inhabited : Inhabited (type T_rt) := populate (ty_of_st _ inhabitant).

  Local Instance type_2_contractive : Contractive (Nat.iter 2 T).
  Proof using Type*.
    intros n ? **. simpl.
    by apply dist_later_S, type_dist2_dist_later, HT, HT, type_later_dist2_later.
  Qed.

  Definition type_fixpoint : type T_rt := fixpointK 2 T.
End fixpoint_def.

Lemma type_fixpoint_ne `{!typeGS Σ} {rt} `{!Inhabited rt} (T1 T2 : type rt → type rt)
    `{!TypeContractive T1, !TypeContractive T2} n :
  (∀ t, T1 t ≡{n}≡ T2 t) → type_fixpoint T1 ≡{n}≡ type_fixpoint T2.
Proof. eapply fixpointK_ne; apply type_contractive_ne, _. Qed.

Section fixpoint.
  Context `{!typeGS Σ}.
  Context {rt} `{!Inhabited rt} (T : type rt → type rt) {HT: TypeContractive T}.

  Global Instance type_fixpoint_copy :
    (∀ `(!Copyable ty), Copyable (T ty)) → Copyable (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply copy_equiv.
    - exists inhabitant. apply _.
    - done.
    - (* If Copy was an Iris assertion, this would be trivial -- we'd just
         use limit_preserving_and directly. However, on the Coq side, it is
         more convenient as a record -- so this is where we pay. *)
      eapply (limit_preserving_ext (λ _, _ ∧ _)).
      { split; (intros [H1 H2]; split; [apply H1|apply H2]). }
      apply limit_preserving_and; repeat (apply limit_preserving_forall=> ?).
      { apply bi.limit_preserving_Persistent; solve_proper. }
      apply limit_preserving_impl'. 
      { intros ?? [? ??? ->]. done. }
      apply limit_preserving_impl', bi.limit_preserving_emp_valid;
        solve_proper_core ltac:(fun _ => eapply ty_size_ne || f_equiv).
  Qed.

  (*
  Global Instance type_fixpoint_send :
    (∀ `(!Send ty), Send (T ty)) → Send (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply send_equiv.
    - exists bool. apply _.
    - done.
    - repeat (apply limit_preserving_forall=> ?).
      apply bi.limit_preserving_entails; solve_proper.
  Qed.

  Global Instance type_fixpoint_sync :
    (∀ `(!Sync ty), Sync (T ty)) → Sync (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply sync_equiv.
    - exists bool. apply _.
    - done.
    - repeat (apply limit_preserving_forall=> ?).
      apply bi.limit_preserving_entails; solve_proper.
  Qed.
  *)

  Lemma type_fixpoint_unfold : type_fixpoint T ≡ T (type_fixpoint T).
  Proof. apply fixpointK_unfold. by apply type_contractive_ne. Qed.

  Lemma fixpoint_unfold_eqtype E L r : eqtype E L r r (type_fixpoint T) (T (type_fixpoint T)).
  Proof. 
    apply eqtype_unfold.
    iIntros (?) "HL HE".
    iSplitR; last iSplitR; last iSplitR.
    - iPureIntro. by rewrite {1}type_fixpoint_unfold.
    - rewrite {1}type_fixpoint_unfold. eauto.
    - iModIntro. iIntros (??).
      rewrite {1}type_fixpoint_unfold. eauto.
    - iModIntro. iIntros (???).
      rewrite {1}type_fixpoint_unfold. eauto.
  Qed.
End fixpoint.
