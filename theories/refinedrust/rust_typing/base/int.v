From refinedrust Require Export type.
From refinedrust Require Import options.

(** * Integer types *)

Open Scope Z_scope.

Section int.
  Context `{!typeGS Σ}.

  Definition int_own_val_def (it : int_type) (tid : thread_id) (z : Z) (v : val) : iProp Σ :=
    ⌜val_to_Z v it = Some z⌝%I.
  Definition int_own_val_aux : seal (@int_own_val_def).
  Proof. by eexists. Qed.
  Definition int_own_val := int_own_val_aux.(unseal).
  Definition int_own_val_unfold : @int_own_val = @int_own_val_def := int_own_val_aux.(seal_eq).

  Lemma int_own_val_to_is_Some it tid z v :
    int_own_val it tid z v -∗ ⌜is_Some (val_to_Z v it)⌝.
  Proof. rewrite int_own_val_unfold. iIntros "%Hv". eauto. Qed.

  Lemma int_own_val_to_eq it tid z v :
    int_own_val it tid z v -∗ ⌜val_to_Z v it = Some z⌝.
  Proof. rewrite int_own_val_unfold. iIntros "%Hv". done. Qed.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition int (it : int_type) : type ZRT := {|
    st_own tid z v := int_own_val it tid z v;
    st_has_op_type ot := is_int_ot ot it;
    st_syn_type := IntSynType it;
  |}%I.
  Next Obligation.
    intros it π r v.
    rewrite int_own_val_unfold.
    iIntros (Hv). iPureIntro.
    exists (it_layout it). split; last by eapply val_to_Z_length.
    apply syn_type_has_layout_int; first done.
  Qed.
  Next Obligation.
    intros it ot Hot. simpl. rewrite (is_int_ot_layout _ _ Hot).
    destruct ot; try done.
    all: by eapply syn_type_has_layout_int.
  Qed.
  Next Obligation.
    intros it ot Hit.
    destruct ot; done.
  Qed.
  Next Obligation. rewrite int_own_val_unfold. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    intros it ot st π r v Hot.
    rewrite int_own_val_unfold.
    simpl.
    iPureIntro. intros Hv.
    destruct ot; simpl in *; try done; subst.
    + eexists (OVInt _ _). simp decode_op_val. rewrite Hv. done.
    + eexists (OVUntyped _ _). simp decode_op_val.
      rewrite bool_decide_true; last by eapply val_to_Z_length.
      done.
  Qed.
  Next Obligation.
    intros it ot st π r v v' Hot Hsame.
    rewrite int_own_val_unfold.
    simpl. iIntros "%Hv". iPureIntro.
    destruct ot; simpl in Hot; try done.
    - subst. destruct Hsame as [Heq _].
      simp decode_op_val in Heq. rewrite Hv in Heq.
      destruct (val_to_Z v' i) eqn:Hz'; simpl in Heq; inversion Heq; subst; done.
    - subst. pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
      rewrite /has_layout_val /= in Hly'.
      pose proof (is_same_decoded_val_at_untyped_inv st v v' (it_layout it) ltac:(by eapply val_to_Z_length) Hly' Hsame) as <-.
      done.
  Qed.
  Next Obligation.
    intros ?? Hst. apply syn_type_has_layout_int_inv in Hst as ->.
    done.
  Qed.

  Lemma ty_own_int_in_range l π n it m : l ◁ᵥ{π, m} n @ int it -∗ ⌜m = MetaNone⌝ ∗ ⌜n ∈ it⌝.
  Proof. rewrite /ty_own_val /= int_own_val_unfold. iIntros "(-> & %Hl)". iR. iPureIntro. by eapply val_to_Z_in_range. Qed.

  Lemma ty_shr_int_in_range l π κ n m it : l ◁ₗ{π, m, κ} n @ int it -∗ ▷ ⌜n ∈ it⌝.
  Proof.
    rewrite /ty_shr /= int_own_val_unfold.
    iIntros "(_ & %v & (%ly & -> & Hv & Ha & Halg & Hl))" => /=. iNext. iDestruct "Ha" as "%Hn".
    iPureIntro. by eapply val_to_Z_in_range.
  Qed.

  Global Instance int_copyable it : Copyable (int it).
  Proof. apply _. Qed.

  Global Instance int_timeless l z it m π :
    Timeless (l ◁ᵥ{π, m} z @ int it)%I.
  Proof. rewrite /ty_own_val /= int_own_val_unfold. apply _. Qed.

End int.

Global Hint Unfold int : ty_unfold.
Notation "int< it >" := (int it) (only printing, format "'int<' it '>'") : printing_sugar.

(** This represents the Rust bool type, which just has valid bit patterns 0x01 and 0x00 *)
Section boolean.
  Context `{!typeGS Σ}.

  Definition bool_own_val_def (tid : thread_id) (b : bool) (v : val) : iProp Σ :=
    ⌜val_to_bool v = Some b⌝%I.
  Definition bool_own_val_aux : seal (@bool_own_val_def).
  Proof. by eexists. Qed.
  Definition bool_own_val := bool_own_val_aux.(unseal).
  Definition bool_own_val_unfold : @bool_own_val = @bool_own_val_def := bool_own_val_aux.(seal_eq).

  Lemma bool_own_val_to_eq tid b v :
    bool_own_val tid b v -∗ ⌜val_to_bool v = Some b⌝.
  Proof. rewrite bool_own_val_unfold. iIntros "%Hb". done. Qed.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition bool_t : type boolRT := {|
    st_own tid b v := bool_own_val tid b v;
    st_syn_type := BoolSynType;
    st_has_op_type ot := is_bool_ot ot;
  |}%I.
  Next Obligation.
    intros π r v.
    rewrite bool_own_val_unfold.
    iIntros (Hv). iExists U8. iPureIntro.
    split; first by apply syn_type_has_layout_bool.
    unfold has_layout_val. erewrite val_to_bool_length; done.
  Qed.
  Next Obligation.
    intros ot Hot. simpl in *. rewrite (is_bool_ot_layout _ Hot). by apply syn_type_has_layout_bool.
  Qed.
  Next Obligation.
    destruct ot; done.
  Qed.
  Next Obligation. rewrite bool_own_val_unfold. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    intros ot st π r v Hot.
    rewrite bool_own_val_unfold.
    simpl.
    destruct ot; simpl in *; try done.
    - iPureIntro. intros Hv.
      eexists (OVBool _). simpl.
      simp decode_op_val.
      rewrite Hv. done.
    - iPureIntro. iIntros (Hv).
      eexists (OVUntyped _ _). simp decode_op_val.
      subst.
      rewrite bool_decide_true; last by eapply val_to_bool_length.
      done.
  Qed.
  Next Obligation.
    intros ot st π r v v' Hot Hsame.
    rewrite bool_own_val_unfold.
    simpl. iIntros "%Hv". iPureIntro.
    destruct ot; simpl in Hot; try done.
    - destruct Hsame as [Heq _].
      simp decode_op_val in Heq. rewrite Hv in Heq.
      destruct (val_to_bool v') eqn:Hb'; simpl in Heq; inversion Heq; subst; done.
    - subst. pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
      rewrite /has_layout_val /= in Hly'.
      pose proof (is_same_decoded_val_at_untyped_inv st v v' U8 ltac:(by eapply val_to_bool_length) Hly' Hsame) as <-.
      done.
  Qed.
  Next Obligation.
    intros ? Hst. apply syn_type_has_layout_bool_inv in Hst as ->.
    done.
  Qed.

  Lemma bool_own_val_eq v π b m :
    (v ◁ᵥ{π, m} b @ bool_t)%I ≡ (⌜m = MetaNone⌝ ∗ ⌜val_to_bool v = Some b⌝)%I.
  Proof. rewrite /ty_own_val /= bool_own_val_unfold. done. Qed.

  Global Instance bool_timeless π l b m:
    Timeless (l ◁ᵥ{π, m} b @ bool_t)%I.
  Proof. rewrite /ty_own_val /= bool_own_val_unfold. apply _. Qed.

  Global Instance bool_copy : Copyable bool_t.
  Proof. apply _. Qed.
End boolean.

Global Hint Unfold bool_t : ty_unfold.
Notation "'bool'" := (bool_t) (only printing, format "'bool'") : printing_sugar.

(** This represents the Rust char type. *)
Section char.
  Context `{!typeGS Σ}.

  Definition char_own_val_def (tid : thread_id) (z : Z) (v : val) : iProp Σ :=
    ⌜val_to_char v = Some z⌝%I.
  Definition char_own_val_aux : seal (@char_own_val_def).
  Proof. by eexists. Qed.
  Definition char_own_val := char_own_val_aux.(unseal).
  Definition char_own_val_unfold : @char_own_val = @char_own_val_def := char_own_val_aux.(seal_eq).

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition char_t : type ZRT := {|
    st_own tid z v := char_own_val tid z v;
    st_syn_type := CharSynType;
    st_has_op_type ot := is_char_ot ot;
  |}%I.
  Next Obligation.
    intros π r v.
    rewrite char_own_val_unfold.
    iIntros (Hv). iExists U32. iPureIntro.
    split; first by apply syn_type_has_layout_char.
    unfold has_layout_val. erewrite val_to_char_length; done.
  Qed.
  Next Obligation.
    intros ot Hot. simpl in *. rewrite (is_char_ot_layout _ Hot). by apply syn_type_has_layout_char.
  Qed.
  Next Obligation. intros. destruct ot; try done. Qed.
  Next Obligation. rewrite char_own_val_unfold. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    intros ot st π r v Hot.
    rewrite char_own_val_unfold.
    simpl.
    destruct ot; simpl in *; try done.
    - iPureIntro. iIntros (Hv).
      eexists (OVUntyped _ _). simp decode_op_val.
      subst.
      rewrite bool_decide_true; last by eapply val_to_char_length.
      done.
    - iPureIntro. intros Hv.
      eexists (OVChar _). simpl.
      simp decode_op_val.
      rewrite Hv. done.
  Qed.
  Next Obligation.
    intros ot st π r v v' Hot Hsame.
    rewrite char_own_val_unfold.
    simpl. iIntros "%Hv". iPureIntro.
    destruct ot; simpl in Hot; try done.
    - subst. pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
      rewrite /has_layout_val /= in Hly'.
      pose proof (is_same_decoded_val_at_untyped_inv st v v' U32 ltac:(by eapply val_to_char_length) Hly' Hsame) as <-.
      done.
    - destruct Hsame as [Heq _].
      simp decode_op_val in Heq. rewrite Hv in Heq.
      destruct (val_to_char v') eqn:Hz'; simpl in Heq; inversion Heq; subst; done.
  Qed.
  Next Obligation.
    intros ? Hst. apply syn_type_has_layout_char_inv in Hst as ->.
    done.
  Qed.

  Lemma char_own_val_eq v π m z :
    (v ◁ᵥ{π, m} z @ char_t)%I ≡ (⌜m = MetaNone⌝ ∗ ⌜val_to_char v = Some z⌝)%I.
  Proof. rewrite /ty_own_val /= char_own_val_unfold. done. Qed.

  Global Instance char_timeless π l b m:
    Timeless (l ◁ᵥ{π, m} b @ char_t)%I.
  Proof. rewrite /ty_own_val /= char_own_val_unfold. apply _. Qed.

  Global Instance char_copy : Copyable char_t.
  Proof. apply _. Qed.
End char.

Global Hint Unfold char_t : ty_unfold.
Notation "'char'" := (char_t) (only printing, format "'char'") : printing_sugar.
