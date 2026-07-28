From refinedrust Require Export type ltypes programs.
From refinedrust Require Import memcasts ltype_rules.
From refinedrust Require Import options.

(** * The value type *)
(** The value type just says that there is a particular sequence of bytes which can be read and written from memory at a particular [op_type]. *)


Definition use_op_alg_typed `{!LayoutAlg} (typed : bool) (st : syn_type) : option op_type :=
  use_op_alg (if typed then st else UntypedSynType st).

Lemma use_op_alg_typed_inv `{!LayoutAlg} typed st ot :
  use_op_alg_typed typed st = Some ot →
  ∃ ot1, use_op_alg st = Some ot1 ∧ ot = if typed then ot1 else UntypedOp (ot_layout ot1).
Proof.
  unfold use_op_alg_typed.  destruct typed; simpl.
  - eauto.
  - intros (ly & Hly & ->)%use_op_alg_untyped_inv.
    apply syn_type_has_layout_untyped_inv in Hly.
    apply syn_type_has_layout_op_alg in Hly as (ot1 & Hot1 & <-).
    eauto.
Qed.
Lemma use_op_alg_typed_Some `{!LayoutAlg} (typed : bool) st ot ot1 :
  use_op_alg st = Some ot1 →
  ot = (if typed then ot1 else UntypedOp (ot_layout ot1)) →
  use_op_alg_typed typed st = Some ot.
Proof.
  intros Hot ->.
  unfold use_op_alg_typed.
  destruct typed; simpl; first done.
  eapply use_op_alg_untyped; first done.
  apply syn_type_has_layout_untyped.
  by eapply use_op_alg_layout_alg.
Qed.

Lemma use_op_alg_typed_array `{!LayoutAlg} typed st n ly ot :
  syn_type_has_layout (ArraySynType st n) (mk_array_layout ly n) →
  use_op_alg st = Some ot →
  use_op_alg_typed typed (ArraySynType st n) =
    Some (if typed then ArrayOp ot n else UntypedOp (mk_array_layout ly n)).
Proof.
  intros Hst Hot. rewrite /syn_type_has_layout in Hst.
  destruct typed; rewrite /use_op_alg_typed /=.
  - by eapply use_op_alg_array.
  - apply bind_Some. eexists. split; last done.
    by apply syn_type_has_layout_untyped.
Qed.
Lemma use_op_alg_typed_array_inv `{!LayoutAlg} typed st n ly ot :
  syn_type_has_layout (ArraySynType st n) (mk_array_layout ly n) →
  use_op_alg_typed typed (ArraySynType st n) = Some ot →
  ∃ element_ot,
    use_op_alg st = Some element_ot ∧
    ot = if typed then ArrayOp element_ot n else UntypedOp (mk_array_layout ly n).
Proof.
  intros Hst Hot.
  apply syn_type_has_layout_array_inv in Hst as (ly' & Hst' & Heq & Hsize).
  pose proof Hst' as Hst_layout.
  apply syn_type_has_layout_op_alg in Hst' as (element_ot & Helement & Hlayout).
  exists element_ot. split; first done.
  assert (Harray : syn_type_has_layout (ArraySynType st n) (mk_array_layout ly' n)).
  { apply syn_type_has_layout_array with (ly := ly'); [reflexivity | exact Hst_layout |].
    apply (f_equal ly_size) in Heq.
    rewrite !ly_size_mk_array_layout in Heq, Hsize |- *. lia. }
  rewrite (use_op_alg_typed_array typed st n ly' element_ot Harray Helement) in Hot.
  destruct typed; simpl in *; congruence.
Qed.

Lemma is_same_decoded_val_array_app_inv r1 r2 v1 v2 ot n1 n2 :
  length r1 = (n1 * ly_size (ot_layout ot))%nat →
  length r2 = (n2 * ly_size (ot_layout ot))%nat →
  length v1 = (n1 * ly_size (ot_layout ot))%nat →
  length v2 = (n2 * ly_size (ot_layout ot))%nat →
  is_same_decoded_val (r1 ++ r2) (ArrayOp ot (n1 + n2)) (v1 ++ v2) →
  is_same_decoded_val r1 (ArrayOp ot n1) v1 ∧
  is_same_decoded_val r2 (ArrayOp ot n2) v2.
Proof.
  intros Hr1_len Hr2_len Hv1_len Hv2_len Hsame.
  assert (Hparts : ∀ hst,
      is_same_decoded_val_at hst r1 (ArrayOp ot n1) v1 ∧
      is_same_decoded_val_at hst r2 (ArrayOp ot n2) v2).
  { intros hst. destruct (Hsame hst) as [Heq [ov Hr]].
    assert (Hv : decode_op_val (v1 ++ v2) (ArrayOp ot (n1 + n2)) hst = Some ov)
      by congruence.
    pose proof (decode_op_val_has_type _ _ _ _ Hr) as Hty.
    inversion Hty; subst ov.
    destruct (decode_op_val_array_app_inv r1 r2 ot n1 n2 hst elements
      Hr1_len Hr2_len Hr) as (elements1 & elements2 & Hr1 & Hr2 & Helements).
    destruct (decode_op_val_array_app_inv v1 v2 ot n1 n2 hst elements
      Hv1_len Hv2_len Hv) as (elements1' & elements2' & Hv1 & Hv2 & Helements').
    pose proof (decode_op_val_has_type _ _ _ _ Hr1) as Hty1.
    pose proof (decode_op_val_has_type _ _ _ _ Hv1) as Hty1'.
    inversion Hty1; inversion Hty1'; subst.
    destruct (app_inj_1 elements1 elements1' elements2 elements2' ltac:(lia)
      ltac:(congruence)) as [-> ->].
    split; split; try congruence; eauto. }
  split; intros hst; [exact (proj1 (Hparts hst)) | exact (proj2 (Hparts hst))].
Qed.

(** [ot] is the optype of the value, [ot'] is the optype we are accessing it at *)
Definition is_value_ot_core (ot : op_type) (ot' : op_type) : Prop :=
  (∃ ly, ot' = UntypedOp ly ∧ ly = ot_layout ot) ∨
  (ot' = ot).
Lemma is_value_ot_core_layout ot ot' :
  is_value_ot_core ot ot' → ot_layout ot' = ot_layout ot.
Proof.
  unfold is_value_ot_core.
  intros [(ly & -> & ->) | ->]; naive_solver.
Qed.
Lemma is_value_ot_core_refl ot :
  is_value_ot_core ot ot.
Proof.
  unfold is_value_ot_core.
  destruct ot; simpl; naive_solver.
Qed.
Lemma is_value_ot_core_untyped ot ly :
  ly = ot_layout ot →
  is_value_ot_core ot (UntypedOp ly).
Proof.
  intros ->. left.
  eauto.
Qed.

Definition is_value_ot `{!LayoutAlg} (typed : bool) (st : syn_type) (ot : op_type) : Prop :=
  ∃ ot',
    use_op_alg_typed typed st = Some ot' ∧
    is_value_ot_core ot' ot ∧
    (* needed because use_op_alg does less checks *)
    syn_type_has_layout st (ot_layout ot')
  .

Global Typeclasses Opaque is_value_ot.

Lemma is_value_ot_literal `{!LayoutAlg} t st ly :
  syn_type_has_layout st ly →
  is_value_ot t (LiteralSynType ly) (UntypedOp ly).
Proof.
  intros Halg. eexists (UntypedOp ly). split_and!.
  - destruct t; rewrite /use_op_alg_typed /use_op_alg /=.
    + apply bind_Some. eexists. split; last done.
      by eapply syn_type_has_layout_make_literal.
    + apply bind_Some. eexists. split; last done.
      apply syn_type_has_layout_untyped.
      by eapply syn_type_has_layout_make_literal.
  - left. eauto.
  - by eapply syn_type_has_layout_make_literal.
Qed.
(* We can only do accesses at [st] if this is actually typed *)
Lemma is_value_ot_typed_use_op_alg `{!LayoutAlg} st ly :
  syn_type_has_layout st ly →
  is_value_ot true st (use_op_alg' st).
Proof.
  intros Ha.
  specialize (syn_type_has_layout_op_alg _ _ Ha) as (ot & Hot & <-).
  rewrite /use_op_alg' Hot /=.
  eexists _.
  split; first done.
  split; last done.
  right. done.
Qed.
(* Otherwise, we can only do untyped accesses *)
Lemma is_value_ot_untyped_use_op_alg `{!LayoutAlg} st ly :
  syn_type_has_layout st ly →
  is_value_ot false st (UntypedOp ly).
Proof.
  intros Hst.
  specialize (syn_type_has_layout_op_alg _ _ Hst) as (ot & Hot & <-).
  rewrite /is_value_ot.
  exists (UntypedOp (ot_layout ot)).
  simpl. split_and!; last done.
  - eapply use_op_alg_untyped; first done.
    by apply syn_type_has_layout_untyped.
  - left. eauto.
Qed.

Section value.
  Context `{!typeGS Σ}.

  (** A value with layout given by [st]. If [typed = true], it is valid at that type.
    The main use case for [typed=false] is specifying&verifying things like [ptr::copy_nonoverlapping],
    which does untyped copies for arbitrary byte sequences.
    Use cases for [typed=true] are diverse, including giving specs to [ptr::read] and [ptr::write], which do typed copies.
  *)
  (*
    invariant will later say:
    - if typed, then it's decodable
    - option 1: if I decode both, they give the same structured value
    - option 2: existing roundtrip

    The relevant thing is: what values can I merge it with again later?
    if it's typed, it has been potentially roundtripped, so then the type to merge needs to be compatible with that.
    *)
  Program Definition value_t (typed : bool) (st : syn_type) : type valRT := {|
    st_own π vs v :=
      (∃ ot,
        ⌜use_op_alg_typed typed st = Some ot⌝ ∗
        ⌜is_same_decoded_val vs ot v⌝ ∗
        ⌜v `has_layout_val` (ot_layout ot)⌝ ∗
        ⌜syn_type_has_layout st (ot_layout ot)⌝)%I;
    st_syn_type := if typed then st else UntypedSynType st;
    st_has_op_type ot' := is_value_ot typed st ot';
  |}.
  Next Obligation.
    iIntros (typed st π vs v) "(%ot & % & % & % & %)".
    destruct typed.
    - eauto.
    - iPureIntro. eexists _. split; first by apply syn_type_has_layout_untyped. done.
  Qed.
  Next Obligation.
    simpl. intros typed st ot' (ot & Halg & Hot & Hst).
    rewrite (is_value_ot_core_layout _ _ Hot).
    destruct typed.
    - done.
    - by apply syn_type_has_layout_untyped.
  Qed.
  Next Obligation.
    intros typed st ot Hot.
    destruct Hot as (ot' & Hot & Hot' & ?).
    destruct Hot' as [(ly & -> & ->) | ->].
    - done.
    - by eapply use_op_alg_wf.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    intros typed st ot' hst π vs v (ot & Halg & Hot & Hst).
    iIntros "(%ot'' & %Halg' & %Hvs & %Hly & %Hst')".
    eapply use_op_alg_typed_inv in Halg' as (ot1 & Halg' & ->).
    apply use_op_alg_typed_inv in Halg as (ot2 & Hot2 & ->).
    assert (ot2 = ot1) as -> by by eapply use_op_alg_inj.
    iPureIntro. destruct Hot as [(ly & -> & ->) | ->].
    - exists (OVUntyped (ot_layout (if typed then ot1 else UntypedOp (ot_layout ot1))) v). simp decode_op_val.
      rewrite /has_layout_val in Hly. case_bool_decide; done || lia.
    - by eapply is_same_decoded_val_decodable_r.
  Qed.
  Next Obligation.
    (* decode compatibility *)
    intros typed st ot' hst π vs v v' (ot & Halg & Hot & Hst) Hsame.
    iIntros "(%ot'' & %Halg' & %Hvs & %Hly & %Hst')".
    eapply use_op_alg_typed_inv in Halg' as (ot1 & Halg' & ->).
    apply use_op_alg_typed_inv in Halg as (ot2 & Hot2 & ->).
    assert (ot2 = ot1) as -> by by eapply use_op_alg_inj.
    iPureIntro. eexists _. split_and!; [ | | | done].
    + eapply use_op_alg_typed_Some; first done. done.
    + destruct Hot as [(ly & -> & ->) | ->].
      * pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
        pose proof (is_same_decoded_val_at_untyped_inv hst v v'
          (ot_layout (if typed then ot1 else UntypedOp (ot_layout ot1))) Hly Hly' Hsame) as ->.
        done.
      * eapply is_same_decoded_val_trans; first done.
        by eapply is_same_decoded_val_of_at.
    + destruct Hot as [(ly & -> & ->) | ->].
      * pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hly'.
        pose proof (is_same_decoded_val_at_untyped_inv hst v v'
          (ot_layout (if typed then ot1 else UntypedOp (ot_layout ot1))) Hly Hly' Hsame) as ->.
        done.
      * by eapply is_same_decoded_val_at_has_layout_r.
  Qed.
  Next Obligation.
    intros typed st ly Hst. simpl.
    unfold is_value_ot.
    destruct typed.
    - specialize (syn_type_has_layout_op_alg st ly Hst) as (ot & Hot & <-).
      exists (ot).
      split_and!.
      + done.
      + left. eexists. done.
      + done.
    - apply syn_type_has_layout_untyped_inv in Hst.
      specialize (syn_type_has_layout_op_alg st ly Hst) as (ot & Hot & <-).
      exists (UntypedOp (ot_layout ot)).
      rewrite /use_op_alg_typed.
      split_and!.
      + eapply use_op_alg_untyped; first done.
        by apply syn_type_has_layout_untyped.
      + left. eexists. split; done.
      + done.
  Qed.

  Global Instance value_copy typed st : Copyable (value_t typed st).
  Proof. apply _. Qed.

  Global Instance value_sized typed st : TySized (value_t typed st).
  Proof. apply _. Qed.
End value.

Section lemmas.
  Context `{!typeGS Σ}.

  Lemma value_syn_type_inv st typed ly :
    syn_type_has_layout (st_of (value_t typed st) MetaNone) ly →
    syn_type_has_layout st ly.
  Proof.
    destruct typed; first done.
    apply syn_type_has_layout_untyped_inv.
  Qed.
  Lemma value_syn_type st typed ly :
    syn_type_has_layout st ly →
    syn_type_has_layout (st_of (value_t typed st) MetaNone) ly.
  Proof.
    destruct typed; first done.
    apply syn_type_has_layout_untyped.
  Qed.

  Lemma value_has_length π v v1 st ly typed m :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} v1 @ value_t typed st -∗
    ⌜length v1 = ly_size ly⌝ ∗ ⌜length v = ly_size ly⌝.
  Proof.
    rewrite /ty_own_val/=.
    iDestruct 1 as "(-> & %ot & %Hot & %Hmc & %Hly & %Hst)".
    assert (ly = ot_layout ot) as -> by by eapply syn_type_has_layout_inj.
    iL. iPureIntro. apply is_same_decoded_val_length in Hmc as ->; done.
  Qed.

  Lemma value_has_layout π typed st v vs m :
    v ◁ᵥ{π, m} vs @ value_t typed st -∗
    ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝.
  Proof.
    rewrite /ty_own_val.
    iDestruct 1 as "(-> & %ot & %Hot & %Hmv & %Hv & %Hst)".
    iExists (ot_layout ot). iR. done.
  Qed.

  Lemma own_val_split_value π {rt} (ty : type rt) r v ly :
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) →
    v ◁ᵥ{π, MetaNone} r @ ty -∗
    v ◁ᵥ{π, MetaNone} v @ value_t true (ty_syn_type ty MetaNone) ∗ v ◁ᵥ{π, MetaNone} r @ ty.
  Proof.
    iIntros (Hly Htyot) "Hv".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    subst.
    specialize (syn_type_has_layout_op_alg _ _ Hly) as (ot & Hot & <-).
    rewrite /use_op_alg' Hot /= in Htyot.
    iPoseProof (ty_decodable _ ty ot inhabitant π r v with "Hv") as (ov) "%Hdec"; [done |].
    iFrame.
    iR.
    iExists ot. iSplitR; first done.
    iSplitR. { iPureIntro. eapply is_same_decoded_val_of_at.
      by apply is_same_decoded_val_at_refl; eauto. }
    done.
  Qed.

  Lemma own_val_split_value_untyped π {rt} (ty : type rt) r v ly m :
    syn_type_has_layout (ty_syn_type ty m) ly →
    v ◁ᵥ{π, m} r @ ty -∗
    v ◁ᵥ{π, MetaNone} v @ value_t false (ty_syn_type ty m) ∗ v ◁ᵥ{π, m} r @ ty.
  Proof.
    iIntros (Hly) "Hv".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    subst. iFrame.
    specialize (syn_type_has_layout_op_alg _ _ Hly) as (ot & Hot & <-).
    iR. iPureIntro.
    exists (UntypedOp (ot_layout ot)).
    split_and!.
    - eapply use_op_alg_untyped; first done.
      by apply syn_type_has_layout_untyped.
    - apply is_same_decoded_val_refl. intros hst.
      exists (OVUntyped (ot_layout ot) v). simp decode_op_val.
      rewrite /has_layout_val in Hv. case_bool_decide; done || lia.
    - done.
    - done.
  Qed.

  Lemma own_val_merge_value_typed π {rt} (ty : type rt) r v vs :
    (* TODO: this requirement should become trivial soon *)
    ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) →
    vs ◁ᵥ{π, MetaNone} v @ value_t true (ty_syn_type ty MetaNone) -∗
    v ◁ᵥ{π, MetaNone} r @ ty -∗
    vs ◁ᵥ{π, MetaNone} r @ ty.
  Proof.
    iIntros (Hot) "Hv1 Hv2".
    iEval (rewrite /ty_own_val/=) in "Hv1".
    iDestruct "Hv1" as "(_ & (%ot & %Hot' & %Hmc & %Hvs & %Hst))".
    rewrite /use_op_alg_typed in Hot'.
    rewrite /use_op_alg'/= Hot'/= in Hot.
    iApply (ty_decode_compat with "Hv2"); [done | exact (Hmc inhabitant)].
  Qed.

  Lemma own_val_merge_value_untyped π {rt} (ty : type rt) st r v vs :
    vs ◁ᵥ{π, MetaNone} v @ value_t false st -∗
    v ◁ᵥ{π, MetaNone} r @ ty -∗
    vs ◁ᵥ{π, MetaNone} r @ ty.
  Proof.
    iIntros "Hv1 Hv2".
    iEval (rewrite /ty_own_val/=) in "Hv1".
    iDestruct "Hv1" as "(_ & (%ot & %Hot' & %Hmc & %Hvs & %Hst))".
    rewrite /use_op_alg_typed/= in Hot'.
    apply use_op_alg_untyped_inv in Hot' as (ly & Hot' & ->).
    pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc) as Hly.
    pose proof (is_same_decoded_val_untyped_inv _ _ _ Hly Hvs Hmc) as ->.
    done.
  Qed.

  Lemma value_array_merge π typed v1 v2 r1 r2 st n1 n2 n m ly :
    n = n1 + n2 →
    syn_type_has_layout (ArraySynType st n) ly →
    v1 ◁ᵥ{π, m} r1 @ value_t typed (ArraySynType st n1) -∗
    v2 ◁ᵥ{π, m} r2 @ value_t typed (ArraySynType st n2) -∗
    (v1 ++ v2) ◁ᵥ{π, m} (r1 ++ r2) @ value_t typed (ArraySynType st n).
  Proof.
    iIntros (-> Hst_n) "Hv1 Hv2".
    rewrite /ty_own_val /=.
    iDestruct "Hv1" as "(-> & %ot1 & %Heq1 & %Hmc1 & %Hly1 & %Halg1)".
    iDestruct "Hv2" as "(_ & %ot2 & %Heq2 & %Hmc2 & %Hly2 & %Halg2)".
    apply syn_type_has_layout_array_inv in Hst_n as (ly_st & Hst & -> & Hsz).
    apply syn_type_has_layout_array_inv in Halg1 as (ly1 & Hst1 & Hot1 & Hsz1).
    apply syn_type_has_layout_array_inv in Halg2 as (ly2 & Hst2 & Hot2 & Hsz2).
    assert (ly1 = ly_st) as -> by by eapply syn_type_has_layout_inj.
    assert (ly2 = ly_st) as -> by by eapply syn_type_has_layout_inj.
    rewrite Hot1 ly_size_mk_array_layout in Hsz1.
    rewrite Hot2 ly_size_mk_array_layout in Hsz2.
    assert (ly_size ly_st * n1 ≤ MaxInt ISize)%Z as Hsz1' by lia.
    assert (ly_size ly_st * n2 ≤ MaxInt ISize)%Z as Hsz2' by lia.
    pose proof (syn_type_has_layout_array st n1 ly_st (mk_array_layout ly_st n1) eq_refl Hst Hsz1') as Halg1.
    pose proof (syn_type_has_layout_array st n2 ly_st (mk_array_layout ly_st n2) eq_refl Hst Hsz2') as Halg2.
    destruct (use_op_alg_typed_array_inv typed st n1 ly_st ot1 Halg1 Heq1)
      as (element_ot1 & Helement1 & Hot1').
    destruct (use_op_alg_typed_array_inv typed st n2 ly_st ot2 Halg2 Heq2)
      as (element_ot2 & Helement2 & Hot2').
    assert (element_ot2 = element_ot1) as -> by by eapply use_op_alg_inj.
    assert (Helement_layout : ot_layout element_ot1 = ly_st).
    { pose proof (use_op_alg_layout_alg _ _ Helement1) as Hlayout.
      rewrite /syn_type_has_layout in Hst. congruence. }
    assert (Halg : syn_type_has_layout (ArraySynType st (n1 + n2))
        (mk_array_layout ly_st (n1 + n2))).
    { eapply syn_type_has_layout_array; [done | done |].
      rewrite ly_size_mk_array_layout in Hsz. lia. }
    destruct typed; simpl in Hot1', Hot2'; subst ot1 ot2.
    - pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc1) as Hrly1.
      pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc2) as Hrly2.
      rewrite /has_layout_val /= !ly_size_mk_array_layout Helement_layout in Hrly1, Hrly2, Hly1, Hly2.
      assert (Hrly1' : length r1 = n1 * ly_size (ot_layout element_ot1)).
      { rewrite Helement_layout. lia. }
      assert (Hrly2' : length r2 = n2 * ly_size (ot_layout element_ot1)).
      { rewrite Helement_layout. lia. }
      assert (Hly1' : length v1 = n1 * ly_size (ot_layout element_ot1)).
      { rewrite Helement_layout. lia. }
      assert (Hly2' : length v2 = n2 * ly_size (ot_layout element_ot1)).
      { rewrite Helement_layout. lia. }
      iR. iExists (ArrayOp element_ot1 (n1 + n2)).
      iSplitR. { iPureIntro.
        exact (use_op_alg_typed_array true st (n1 + n2) ly_st element_ot1 Halg Helement1). }
      iSplitR. { iPureIntro. intros hst. split.
        + rewrite (decode_op_val_array_app r1 r2 element_ot1 n1 n2 hst Hrly1' Hrly2').
          rewrite (decode_op_val_array_app v1 v2 element_ot1 n1 n2 hst Hly1' Hly2').
          by rewrite (proj1 (Hmc1 hst)) (proj1 (Hmc2 hst)).
        + destruct (Hmc1 hst) as [_ [ov1 Hdec1]].
          destruct (Hmc2 hst) as [_ [ov2 Hdec2]].
          rewrite (decode_op_val_array_app r1 r2 element_ot1 n1 n2 hst Hrly1' Hrly2').
          rewrite Hdec1 Hdec2 /=.
          pose proof (decode_op_val_has_type _ _ _ _ Hdec1) as Hty1.
          pose proof (decode_op_val_has_type _ _ _ _ Hdec2) as Hty2.
          inversion Hty1; inversion Hty2; subst. eauto. }
      iSplitR. { iPureIntro. rewrite /has_layout_val /= length_app ly_size_mk_array_layout
          Helement_layout. lia. }
      iPureIntro. simpl. rewrite Helement_layout. exact Halg.
    - iR. iExists (UntypedOp (mk_array_layout ly_st (n1 + n2))).
      iSplitR. { iPureIntro.
        exact (use_op_alg_typed_array false st (n1 + n2) ly_st element_ot1 Halg Helement1). }
      iSplitR. {
        iPureIntro.
        pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc1) as Hrly1.
        pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc2) as Hrly2.
        pose proof (is_same_decoded_val_untyped_inv _ _ _ Hrly1 Hly1 Hmc1) as ->.
        pose proof (is_same_decoded_val_untyped_inv _ _ _ Hrly2 Hly2 Hmc2) as ->.
        apply is_same_decoded_val_refl. intros hst.
        exists (OVUntyped (mk_array_layout ly_st (n1 + n2)) (v1 ++ v2)). simp decode_op_val.
        rewrite /has_layout_val length_app.
        rewrite /has_layout_val in Hly1, Hly2.
        rewrite !ly_size_mk_array_layout in Hly1, Hly2.
        rewrite ly_size_mk_array_layout.
        case_bool_decide; done || lia. }
    iSplitR. {
      iPureIntro. rewrite /has_layout_val length_app.
      rewrite /has_layout_val in Hly1, Hly2.
      rewrite !ly_size_mk_array_layout in Hly1, Hly2, Hsz. simpl.
      rewrite ly_size_mk_array_layout. lia. }
    iPureIntro. eapply syn_type_has_layout_array; [done | done |].
    rewrite ly_size_mk_array_layout in Hsz. lia.
  Qed.

  Lemma value_array_split n n1 n2 typed st ly π v v1 v2 r r1 r2 m :
    syn_type_has_layout st ly →
    n = n1 + n2 →
    v = v1 ++ v2 →
    r = r1 ++ r2 →
    length v1 = n1 * ly_size ly →
    length v2 = n2 * ly_size ly →
    length r1 = n1 * ly_size ly →
    length r2 = n2 * ly_size ly →
    v ◁ᵥ{π, m} r @ value_t typed (ArraySynType st n) -∗
    v1 ◁ᵥ{π, m} r1 @ value_t typed (ArraySynType st n1) ∗
    v2 ◁ᵥ{π, m} r2 @ value_t typed (ArraySynType st n2).
  Proof.
    iIntros (Hst1 -> -> -> Hv1_len Hv2_len Hr1_len Hr2_len) "Hv".
    rewrite /ty_own_val/=. iDestruct "Hv" as "(-> & %ot & %Hot & %Hmc & %Hly & %Hst)".
    apply syn_type_has_layout_array_inv in Hst as (ly_st & Hst & Hotly & Hsz).
    assert (ly_st = ly) as -> by by eapply syn_type_has_layout_inj.
    rewrite Hotly in Hsz.
    rewrite ly_size_mk_array_layout in Hsz.
    assert (ly_size ly * (n1 + n2)%nat ≤ MaxInt ISize)%Z as Hsz' by lia.
    pose proof (syn_type_has_layout_array st (n1 + n2) ly (mk_array_layout ly (n1 + n2)) eq_refl Hst1 Hsz') as Halg.
    destruct (use_op_alg_typed_array_inv typed st (n1 + n2) ly ot Halg Hot)
      as (element_ot & Helement & Hot').
    assert (Helement_layout : ot_layout element_ot = ly).
    { pose proof (use_op_alg_layout_alg _ _ Helement) as Hlayout.
      rewrite /syn_type_has_layout in Hst1. congruence. }
    assert (Halg1 : syn_type_has_layout (ArraySynType st n1) (mk_array_layout ly n1)).
    { eapply syn_type_has_layout_array; [done | done |]. lia. }
    assert (Halg2 : syn_type_has_layout (ArraySynType st n2) (mk_array_layout ly n2)).
    { eapply syn_type_has_layout_array; [done | done |]. lia. }
    destruct typed; simpl in Hot'; subst ot.
    - pose proof (is_same_decoded_val_array_app_inv r1 r2 v1 v2 element_ot n1 n2
        ltac:(rewrite Helement_layout; lia) ltac:(rewrite Helement_layout; lia)
        ltac:(rewrite Helement_layout; lia) ltac:(rewrite Helement_layout; lia) Hmc) as Hsame.
      destruct Hsame as [Hsame1 Hsame2]. iSplit.
      + iR. iExists (ArrayOp element_ot n1).
        iSplitR. { iPureIntro.
          exact (use_op_alg_typed_array true st n1 ly element_ot Halg1 Helement). }
        iSplitR; first done.
        iSplitR. { iPureIntro. rewrite /has_layout_val /= ly_size_mk_array_layout Helement_layout. lia. }
        iPureIntro. simpl. rewrite Helement_layout. exact Halg1.
      + iR. iExists (ArrayOp element_ot n2).
        iSplitR. { iPureIntro.
          exact (use_op_alg_typed_array true st n2 ly element_ot Halg2 Helement). }
        iSplitR; first done.
        iSplitR. { iPureIntro. rewrite /has_layout_val /= ly_size_mk_array_layout Helement_layout. lia. }
        iPureIntro. simpl. rewrite Helement_layout. exact Halg2.
    - pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc) as Hrly.
      pose proof (is_same_decoded_val_untyped_inv _ _ _ Hrly Hly Hmc) as Happ.
      destruct (app_inj_1 r1 v1 r2 v2 ltac:(lia) Happ) as [-> ->].
      iSplit.
      + iR. iExists (UntypedOp (mk_array_layout ly n1)).
        iSplitR. { iPureIntro.
          exact (use_op_alg_typed_array false st n1 ly element_ot Halg1 Helement). }
        iSplitR. { iPureIntro. apply is_same_decoded_val_refl. intros hst.
          exists (OVUntyped (mk_array_layout ly n1) v1). simp decode_op_val.
          rewrite /has_layout_val ly_size_mk_array_layout.
          case_bool_decide; done || lia. }
        iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
        done.
      + iR. iExists (UntypedOp (mk_array_layout ly n2)).
        iSplitR. { iPureIntro.
          exact (use_op_alg_typed_array false st n2 ly element_ot Halg2 Helement). }
        iSplitR. { iPureIntro. apply is_same_decoded_val_refl. intros hst.
          exists (OVUntyped (mk_array_layout ly n2) v2). simp decode_op_val.
          rewrite /has_layout_val ly_size_mk_array_layout.
          case_bool_decide; done || lia. }
        iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
        done.
  Qed.

  Lemma value_t_splittable_type_app π typed st n1 n2 (vs1 vs2 : val) :
    length vs1 = n1 * size_of_st st →
    length vs2 = n2 * size_of_st st →
    @splittable_type _ _ valRT π st (n1 + n2) n1 n2 (vs1 ++ vs2) vs1 vs2
      (value_t typed (ArraySynType st (n1 + n2)))
      (value_t typed (ArraySynType st n1))
      (value_t typed (ArraySynType st n2)).
  Proof.
    intros Hvs1 Hvs2.
    rewrite /splittable_type /=. split_and!; try done.
    1-6: destruct typed; first [done | apply syn_type_compat_untyped_l | apply syn_type_compat_untyped_r]; done.
    intros Hbound v v1 v2 -> Hv1 Hv2. iSplit.
    - iIntros "Hv".
      iDestruct "Hv" as "(_ & %ot & %Hot & %Hmc & %Hly & %Hly_arr)".
      apply syn_type_has_layout_array_inv in Hly_arr as (ly_st & Hst & Hotly & Hsz).
      rewrite Hotly in Hly.
      iAssert ((v1 ++ v2) ◁ᵥ{π, MetaNone} (vs1 ++ vs2) @ value_t typed (ArraySynType st (n1 + n2)))%I
        with "[]" as "Hv".
      { rewrite /ty_own_val/=. iR. iExists ot. rewrite Hotly. iSplitR; first done. iSplitR; first done.
        iSplit; first done.
        iPureIntro. eapply syn_type_has_layout_array; [done | done |].
        move: Hsz. rewrite Hotly ly_size_mk_array_layout. lia. }
      iApply (value_array_split (n1 + n2) n1 n2 typed st ly_st with "Hv"); try done.
      + rewrite /size_of_st in Hv1. erewrite use_layout_alg_eq' in Hv1; last done. done.
      + rewrite /size_of_st in Hv2. erewrite use_layout_alg_eq' in Hv2; last done. done.
      + rewrite /size_of_st in Hvs1. erewrite use_layout_alg_eq' in Hvs1; last done. done.
      + rewrite /size_of_st in Hvs2. erewrite use_layout_alg_eq' in Hvs2; last done. done.
    - iIntros "(Hv1 & Hv2)".
      iDestruct "Hv1" as "(_ & %ot1 & %Hot1 & %Hmc1 & %Hly1 & %Hly_arr1)".
      iDestruct "Hv2" as "(_ & %ot2 & %Hot2 & %Hmc2 & %Hly2 & %Hly_arr2)".
      apply syn_type_has_layout_array_inv in Hly_arr1 as (ly_st & Hst & Hotly1 & Hsz1).
      rewrite Hotly1 in Hly1.
      iAssert (v1 ◁ᵥ{π, MetaNone} vs1 @ value_t typed (ArraySynType st n1))%I with "[]" as "Hv1".
      { rewrite /ty_own_val/=. iR. iExists ot1. rewrite Hotly1. iSplitR; first done. iSplitR; first done.
        iSplit; first done.
        iPureIntro. eapply syn_type_has_layout_array; [done | done |].
        move: Hsz1. rewrite Hotly1 ly_size_mk_array_layout. lia. }
      iAssert (v2 ◁ᵥ{π, MetaNone} vs2 @ value_t typed (ArraySynType st n2))%I with "[]" as "Hv2".
      { rewrite /ty_own_val/=. iR. iExists ot2. iSplitR; first done. iSplitR; first done.
        iSplit; iPureIntro; done. }
      iApply (value_array_merge with "Hv1 Hv2"); first done.
      eapply syn_type_has_layout_array; [done | done |].
      move: Hbound. rewrite /size_of_st. erewrite use_layout_alg_eq'; last done. lia.
  Qed.
End lemmas.

Section types.
  Context `{!typeGS Σ}.

  Lemma type_loc_value π v (l : loc) :
    val_decodes_to_loc v l →
    loc_a l ∈ USize →
    ⊢ v ◁ᵥ{ π, MetaNone} (l2v l) @ value_t true PtrSynType.
  Proof.
    iIntros (Hv ?).
    rewrite /ty_own_val/=.
    iR. iExists PtrOp.
    iR. iPureIntro. split_and!.
    - intros hst. split.
      + rewrite Hv.
        simp decode_op_val.
        by rewrite (val_to_loc_Some_l2v l).
      + exists (OVPtr l). simp decode_op_val.
        by rewrite (val_to_loc_Some_l2v l).
    - rewrite /has_layout_val.
      erewrite val_decodes_to_loc_length; done.
    - by apply syn_type_has_layout_ptr.
  Qed.
End types.

Section ofty_lemmas.
  Context `{!typeGS Σ}.

  Lemma ofty_value_has_length F π l typed st ly v1 :
    lftE ⊆ F →
    syn_type_has_layout st ly →
    l ◁ₗ[π, Owned] #v1 @ (◁ value_t typed st) ={F}=∗
    ⌜length v1 = ly_size ly⌝ ∗ l ◁ₗ[π, Owned] #v1 @ (◁ value_t typed st).
  Proof.
    iIntros (??) "Hl".
    rewrite ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Hst & % & ? & ? & %r' & <- & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (value_has_length with "Hv") as "(% & %)"; first done.
    apply value_syn_type_inv in Hst.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iR. iModIntro. iExists _. iFrame.
    iSplitR. { iPureIntro. by apply value_syn_type. }
    done.
  Qed.

  Lemma ofty_own_split_value_typed π F l {rt} (ty : type rt) r :
    lftE ⊆ F →
    ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) →
    (l ◁ₗ[π, Owned] #r @ ◁ ty)%I -∗ |={F}=> ∃ v,
    v ◁ᵥ{π, MetaNone} r @ ty ∗ l ◁ₗ[π, Owned] #v @ ◁ (value_t true (ty_syn_type ty MetaNone)).
  Proof.
    iIntros (? Hot) "Hty".
    rewrite (ltype_own_ofty_unfold ty) /lty_of_ty_own.
    iDestruct "Hty" as "(%ly' & % & % & Hsc & Hlb & %r' & <- & Hb)".
    (*assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.*)
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (own_val_split_value with "Hv") as "(Hv' & Hv)"; [done | done |].
    iExists v. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl.
    iR. iR. by iFrame.
  Qed.

  Lemma ofty_own_split_value_untyped π F l {rt} (ty : type rt) r :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned] #r @ ◁ ty)%I -∗ |={F}=> ∃ v,
    v ◁ᵥ{π, MetaNone} r @ ty ∗ l ◁ₗ[π, Owned] #v @ ◁ (value_t false (ty_syn_type ty MetaNone)).
  Proof.
    iIntros (?) "Hty".
    rewrite (ltype_own_ofty_unfold ty) /lty_of_ty_own.
    iDestruct "Hty" as "(%ly' & % & % & Hsc & Hlb & %r' & <- & Hb)".
    (*assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.*)
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (own_val_split_value_untyped _ _ _ _ with "Hv") as "(Hv' & Hv)".
    { done. }
    iExists v. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl.
    iSplitR. { iPureIntro. by apply syn_type_has_layout_untyped. }
    iR. iR. iFrame. done.
  Qed.

  Lemma ofty_own_merge_value_typed {rt} π (ty : type rt) v r l :
    ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) →
    v ◁ᵥ{ π, MetaNone} r @ ty -∗
    l ◁ₗ[ π, Owned] #v @ (◁ value_t true (ty_syn_type ty MetaNone)) -∗
    l ◁ₗ[ π, Owned] #r @ (◁ ty).
  Proof.
    iIntros (?) "Hv Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & % & Hsc & Hlb & %r' & Hrfn & Hb)".
    simpl in Halg.
    iExists ly.
    iFrame "%".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    iFrame "Hlb".
    iExists r. iR.
    iMod "Hb" as "(%v' & Hl & Hv')". iModIntro.
    iDestruct "Hrfn" as "<-".
    iExists v'. iFrame.
    iApply (own_val_merge_value_typed with "Hv' Hv"). done.
  Qed.

  Lemma ofty_own_merge_value_untyped {rt} π (ty : type rt) v r st l ly :
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    syn_type_has_layout st ly →
    v ◁ᵥ{ π, MetaNone} r @ ty -∗
    l ◁ₗ[ π, Owned] #v @ (◁ value_t false st) -∗
    l ◁ₗ[ π, Owned] #r @ (◁ ty).
  Proof.
    iIntros (??) "Hv Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly1 & %Halg & % & Hsc & Hlb & %r' & Hrfn & Hb)".
    simpl in Halg.
    apply syn_type_has_layout_untyped_inv in Halg.
    assert (ly1 = ly) as -> by by eapply syn_type_has_layout_inj.
    iExists ly.
    iFrame "%".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    iFrame "Hlb".
    iExists r. iR.
    iMod "Hb" as "(%v' & Hl & Hv')". iModIntro.
    iDestruct "Hrfn" as "<-".
    iExists v'. iFrame.
    by iApply (own_val_merge_value_untyped with "Hv'").
  Qed.

  Lemma ofty_value_array_merge F n1 n2 n3 vs1 vs2 π l st ly typed :
    lftE ⊆ F →
    n3 = n1 + n2 →
    syn_type_has_layout (ArraySynType st n3) ly →
    (l ◁ₗ[π, Owned] #vs1 @ ◁ value_t typed (ArraySynType st n1)) -∗
    ((l offsetst{st}ₗ n1) ◁ₗ[π, Owned] #vs2 @ ◁ value_t typed (ArraySynType st n2)) ={F}=∗
    (l ◁ₗ[π, Owned] #(vs1++vs2 : val) @ ◁ value_t typed (ArraySynType st n3)).
  Proof.
    iIntros (? -> Hst') "Hl1 Hl2".
    apply syn_type_has_layout_array_inv in Hst' as (ly_st & Hst & -> & Hsz).
    iMod (ofty_value_has_length with "Hl1") as "(%Hlen1 & Hl1)"; [done | |].
    { eapply syn_type_has_layout_array; [done | done |].
      move: Hsz. rewrite ly_size_mk_array_layout. lia. }
    iMod (ofty_value_has_length with "Hl2") as "(%Hlen2 & Hl2)"; [done | |].
    { eapply syn_type_has_layout_array; [done | done |].
      move: Hsz. rewrite ly_size_mk_array_layout. lia. }
    iApply (@ofty_array_merge _ _ F valRT π st (n1 + n2) n1 n2 l
      (vs1 ++ vs2) vs1 vs2
      (value_t typed (ArraySynType st (n1 + n2)))
      (value_t typed (ArraySynType st n1))
      (value_t typed (ArraySynType st n2)) with "Hl1 Hl2"); [done | done | |].
    - move: Hsz. rewrite ly_size_mk_array_layout /size_of_st.
      erewrite use_layout_alg_eq'; last done. lia.
    - apply value_t_splittable_type_app.
      + rewrite Hlen1 ly_size_mk_array_layout /size_of_st.
        erewrite use_layout_alg_eq'; last done. lia.
      + rewrite Hlen2 ly_size_mk_array_layout /size_of_st.
        erewrite use_layout_alg_eq'; last done. lia.
  Qed.

  Lemma ofty_value_array_split F π l (v1 v2 v3 : val) n1 n2 n3 st ly typed :
    lftE ⊆ F →
    v1 = v2 ++ v3 →
    n1 = n2 + n3 →
    syn_type_has_layout st ly →
    length v2 = n2 * ly_size ly →
    length v3 = n3 * ly_size ly →
    l ◁ₗ[π, Owned] #v1 @ (◁ value_t typed (ArraySynType st n1)) ={F}=∗
    l ◁ₗ[π, Owned] #v2 @ (◁ value_t typed (ArraySynType st n2)) ∗
    (l offsetst{st}ₗ n2) ◁ₗ[π, Owned] #v3 @ ◁ value_t typed (ArraySynType st n3).
  Proof.
    iIntros (? -> -> Hst Hlen2 Hlen3) "Hl".
    iApply (@ofty_array_split _ _ F valRT π st (n2 + n3) n2 n3 l
      (v2 ++ v3) v2 v3
      (value_t typed (ArraySynType st (n2 + n3)))
      (value_t typed (ArraySynType st n2))
      (value_t typed (ArraySynType st n3)) with "Hl"); [done | done |].
    apply value_t_splittable_type_app.
    - rewrite Hlen2 /size_of_st. erewrite use_layout_alg_eq'; last done. done.
    - rewrite Hlen3 /size_of_st. erewrite use_layout_alg_eq'; last done. done.
  Qed.
End ofty_lemmas.

(** A few lemmas about untyped values with a [LiteralSynType] layout.
  Mostly useful for manual manipulation when interfacing with low-level allocation APIs. *)
Section byte_lemmas.
  Context `{!typeGS Σ}.

  (** For untyped values, we can freely convert to and from a raw [LiteralSynType]. *)
  Lemma value_untyped_to_literal v π m vs st ly  :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} vs @ value_t false st -∗
    v ◁ᵥ{π, MetaNone} vs @ value_t false (LiteralSynType ly).
  Proof.
    iIntros (Hst) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(-> & %ot & %Hot & %Hmc & %Hv & %Hst')".
    iR. apply use_op_alg_typed_inv in Hot as (ot1 & Hot & ->).
    assert (ly = ot_layout ot1) as -> by by eapply syn_type_has_layout_inj.
    iExists (UntypedOp (ot_layout ot1)).
    iPureIntro. split_and!.
    - eapply use_op_alg_untyped; first done.
      apply syn_type_has_layout_untyped.
      by eapply syn_type_has_layout_make_literal.
    - done.
    - done.
    - by eapply syn_type_has_layout_make_literal.
  Qed.
  Lemma value_untyped_from_literal v π m vs st ly  :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} vs @ value_t false (LiteralSynType ly) -∗
    v ◁ᵥ{π, MetaNone} vs @ value_t false st.
  Proof.
    iIntros (Hst) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(-> & %ot & %Hot & %Hmc & %Hv & %Hst')".
    iR. apply use_op_alg_typed_inv in Hot as (ot1 & Hot & ->).
    apply syn_type_has_layout_literal_inv in Hst' as (<- & Hwf & Hsz & Hal).
    simpl in *.
    iExists (UntypedOp (ot_layout ot1)).
    iPureIntro. split_and!.
    - eapply use_op_alg_untyped; first done.
      by apply syn_type_has_layout_untyped.
    - done.
    - done.
    - done.
  Qed.

  Lemma ofty_value_untyped_from_literal st l π vs ly :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned] vs @ ◁ value_t false (LiteralSynType ly)) -∗
    l ◁ₗ[π, Owned] vs @ ◁ value_t false st.
  Proof.
    iIntros (Hst) "Hl".
    iApply (ofty_mono_ly_strong with "[] [] Hl"); simpl.
    - apply syn_type_has_layout_untyped.
      by eapply syn_type_has_layout_make_literal.
    - by apply syn_type_has_layout_untyped.
    - done.
    - done.
    - iIntros (v r) "Hv".
      by iApply value_untyped_from_literal.
    - eauto.
  Qed.
  Lemma ofty_value_untyped_to_literal l π vs st ly :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned] vs @ ◁ value_t false st) -∗
    (l ◁ₗ[π, Owned] vs @ ◁ value_t false (LiteralSynType ly)).
  Proof.
    iIntros (Hst) "Hl".
    iApply (ofty_mono_ly_strong with "[] [] Hl"); simpl.
    - by apply syn_type_has_layout_untyped.
    - apply syn_type_has_layout_untyped.
      by eapply syn_type_has_layout_make_literal.
    - done.
    - done.
    - iIntros (v r) "Hv".
      by iApply value_untyped_to_literal.
    - eauto.
  Qed.

  Lemma ofty_uninit_to_untyped_value F π l st :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned] .@ ◁ (uninit st))%I ={F}=∗
    ∃ v, l ◁ₗ[π, Owned] #v @ (◁ value_t false st)%I.
  Proof.
    iIntros (?) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    iMod (ofty_own_split_value_untyped with "Ha") as "(%v & _ & Ha)"; [done.. | ].
    iPoseProof (ofty_value_untyped_to_literal with "Ha") as "Ha".
    { done. }
    apply syn_type_has_layout_untyped_inv in Hst.
    iPoseProof (ofty_value_untyped_from_literal st with "Ha") as "Ha".
    { done. }
    iExists v. done.
  Qed.

  Lemma value_untyped_layout_mono ly2 ly1 π v vs  m :
    ly_size ly1 = ly_size ly2 →
    (layout_wf ly1 → layout_wf ly2) →
    (ly_align_in_bounds ly1 → ly_align_in_bounds ly2) →
    v ◁ᵥ{π, m} vs @ value_t false (LiteralSynType ly1) -∗
    v ◁ᵥ{π, MetaNone} vs @ value_t false (LiteralSynType ly2).
  Proof.
    iIntros (Hsz Hwf Hal) "Hv". rewrite /ty_own_val /=.
    iDestruct "Hv" as "(-> & %ot & %Heq & %Hmc & %Hly & %Hst)".
    apply use_op_alg_typed_inv in Heq as (ot1 & Hot1 & ->).
    simpl in Hst, Hmc, Hly.
    apply syn_type_has_layout_literal_inv in Hst as (Hotly & Hwf' & Hsz_le & Hal').
    rewrite Hotly in Hmc, Hly.
    iR. iExists (UntypedOp ly2). iSplitR.
    { iPureIntro. rewrite /use_op_alg_typed.
      eapply use_op_alg_untyped; first done.
      apply syn_type_has_layout_untyped.
      eapply syn_type_has_layout_literal; first done.
      - by apply Hwf.
      - lia.
      - by apply Hal. }
    iSplitR. { iPureIntro.
      pose proof (is_same_decoded_val_has_layout_l _ _ _ Hmc) as Hvs.
      pose proof (is_same_decoded_val_untyped_inv _ _ _ Hvs Hly Hmc) as ->.
      apply is_same_decoded_val_refl. intros hst.
      exists (OVUntyped ly2 v). simp decode_op_val.
      rewrite /has_layout_val in Hly. rewrite Hly Hsz.
      case_bool_decide; done || lia. }
    simpl. iSplitR. { rewrite /has_layout_val -Hsz //. }
    iPureIntro.
    eapply syn_type_has_layout_literal.
    - done.
    - by apply Hwf.
    - lia.
    - by apply Hal.
  Qed.

  Lemma ofty_value_untyped_update_layout ly2 ly1 π l vs  :
    ly_size ly1 = ly_size ly2 →
    l `has_layout_loc` ly2 →
    layout_wf ly2 →
    (ly_align_in_bounds ly1 → ly_align_in_bounds ly2) →
    (l ◁ₗ[π, Owned] vs @ ◁ value_t false (LiteralSynType ly1)) -∗
    (l ◁ₗ[π, Owned] vs @ ◁ value_t false (LiteralSynType ly2)).
  Proof.
    iIntros (Hsz Halign ? Halmon) "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & #_)".
    simp_ltypes in Halg. simpl in Halg.
    apply syn_type_has_layout_untyped_inv in Halg.
    apply syn_type_has_layout_literal_inv in Halg as (-> & Hwf1 & Hsz_le & Hal).
    iApply (ofty_mono_ly_strong with "[] [] Hl").
    + simpl.
      apply syn_type_has_layout_untyped.
      eapply syn_type_has_layout_literal; done.
    + simpl.
      apply syn_type_has_layout_untyped.
      eapply syn_type_has_layout_literal; first done.
      - done.
      - lia.
      - by apply Halmon.
    + done.
    + done.
    + iIntros (??). iApply value_untyped_layout_mono; [done.. | ]. eauto.
    + simpl. done.
  Qed.

  (** Convert to an array of bytes *)
  Local Lemma ofty_value_untyped_to_bytes π l vn ly :
    l ◁ₗ[π, Owned] #vn @ (◁ value_t false (LiteralSynType ly)) -∗
    l ◁ₗ[π, Owned] #vn @ (◁ value_t false (LiteralSynType $ mk_array_layout U8 (ly_size ly))).
  Proof.
    (* We can always go to something with a lower alignment *)
    iIntros "Hl". iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Halg & %Hly)".
    simp_ltypes in Halg. simpl in Halg.
    apply syn_type_has_layout_untyped_inv in Halg.
    apply syn_type_has_layout_literal_inv in Halg as (-> & ? & ?).
    iApply (ofty_value_untyped_update_layout with "Hl").
    - rewrite /mk_array_layout{2}/ly_size/=. lia.
    - rewrite /has_layout_loc/ly_align/mk_array_layout/=.
      rewrite /aligned_to.
      apply Z.divide_1_l.
    - rewrite /layout_wf/ly_align/=. apply Z.divide_1_l.
    - done.
  Qed.
  Lemma ofty_value_untyped_to_byte_array π l vn ly :
    l ◁ₗ[π, Owned] #vn @ (◁ value_t false (LiteralSynType ly)) -∗
    l ◁ₗ[π, Owned] #vn @ (◁ value_t false (ArraySynType (IntSynType U8) (ly_size ly))).
  Proof.
    iIntros "Hv".
    iPoseProof (ltype_own_has_layout with "Hv") as "(%ly' & %Hst & %)".
    simp_ltypes in Hst. simpl in Hst.
    apply syn_type_has_layout_untyped_inv in Hst.
    apply syn_type_has_layout_literal_inv in Hst as (-> & ? & ? & ?).
    iPoseProof (ofty_value_untyped_update_layout with "Hv") as "Hv"; first last.
    { iApply ofty_value_untyped_from_literal; last done.
      eapply syn_type_has_layout_array.
      - done.
      - by apply syn_type_has_layout_int.
      - rewrite {1}/ly_size/=.
        unfold_common_radium_defs. simpl. lia. }
    - intros. done.
    - apply array_layout_wf.
      apply int_type_layout_wf.
    - rewrite /has_layout_loc ly_align_mk_array_layout.
      rewrite {1}/ly_align/=.
      apply Z.divide_1_l.
    - rewrite ly_size_mk_array_layout.
      rewrite {1}/ly_size/=.
      unfold_common_radium_defs. simpl. lia.
  Qed.

End byte_lemmas.


(** ** value rules *)
Section rules.
  Context `{!typeGS Σ}.
  (** *** Rules converting other types to/from values*)
  (** NOTE: This needs to have lower priority than the below subsumption instances that specialize to the case where [ty = value_t _].
     In addition, other rules for other types should similarly be able to implement their own proof strategies.
     Namely, this rule makes a pretty strong commitment (having an exactly fitting value assignment available),
     so we should really try it as a last resort. So we give it a pretty low priority. *)

  (* No instances, as we cannot use the universally quantified [v] for evar instantiation.
    Should be manually applied if needed. *)
  Lemma owned_subltype_step_to_typed_value π E L step {rt} l v' st (ty : type rt) r T:
    (⌜ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone))⌝ ∗
    ∀ v, v ◁ᵥ{π, MetaNone} r @ ty -∗
      owned_subltype_step π E L step l (#v) (#v') (◁ value_t true (ty_syn_type ty MetaNone)) (◁ value_t true st) T)
    ⊢ owned_subltype_step π E L step l (#r) (#v') (◁ ty) (◁ value_t true st) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%Hot & HT)" (????) "#CTX #HE HL Hty".
    iMod (ofty_own_split_value_typed with "Hty") as "(%v & Hv & Hty)"; [done.. | ].
    iDestruct ("HT" with "Hv") as "HT".
    by iApply ("HT" with "[//] [//] [//] CTX HE HL").
  Qed.
  Lemma owned_subltype_step_to_untyped_value π E L step {rt} l v' st (ty : type rt) r T:
    (∀ v, v ◁ᵥ{π, MetaNone} r @ ty -∗
      owned_subltype_step π E L step l (#v) (#v') (◁ value_t false (ty_syn_type ty MetaNone)) (◁ value_t false st) T)
    ⊢ owned_subltype_step π E L step l (#r) (#v') (◁ ty) (◁ value_t false st) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "HT" (????) "#CTX #HE HL Hty".
    iMod (ofty_own_split_value_untyped with "Hty") as "(%v & Hv & Hty)"; [done.. | ].
    iDestruct ("HT" with "Hv") as "HT".
    by iApply ("HT" with "[//] [//] [//] CTX HE HL").
  Qed.

  Definition owned_subtype_value_id π E L step st r1 r2 typed := owned_subtype_id π E L step r1 r2 (value_t typed st).
  Definition owned_subtype_value_id_inst := [instance @owned_subtype_value_id].
  Global Existing Instance owned_subtype_value_id_inst | 10.

  Lemma owned_subtype_merge_typed_value {rt} π E L (ty : type rt) r v' st T :
    prove_with_subtype E L false ProveDirect (v' ◁ᵥ{π, MetaNone} r @ ty) True (λ L' _ R,
      introduce_with_hooks E L' R (λ L2,
      ⌜ty_has_op_type ty (use_op_alg' (ty.(ty_syn_type) MetaNone))⌝ ∗
      ⌜ty_syn_type ty MetaNone = st⌝ ∗
      T L2))
    ⊢ owned_subtype π E L false v' r (value_t true st) (ty) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" $! _ True%I with "[//] [//] [//] CTX HE HL []") as "(%L2 & %κs & %R & >(HR & Hv' & _) & HL & HT)".
    { iApply maybe_logical_step_intro. done. }
    iMod ("HT" with "[//] CTX HE HL HR") as "(%L3 & HL & %Hot & <- & HT)".
    iExists _. iFrame. iModIntro.
    iPoseProof (ty_own_val_sidecond with "Hv'") as "#$".
    iSplitR. { iPureIntro. apply syn_type_size_eq_refl. }
    iSplitR; first by eauto.
    iIntros (v) "Hv".
    by iApply (own_val_merge_value_typed with "Hv Hv'").
  Qed.
  (* shouldn't have super high priority because the conclusion is very general *)
  Definition owned_subtype_merge_typed_value_inst := [instance @owned_subtype_merge_typed_value].
  Global Existing Instance owned_subtype_merge_typed_value_inst | 30.

  Lemma owned_subtype_merge_untyped_value {rt} π E L (ty : type rt) r v' st T :
    prove_with_subtype E L false ProveDirect (v' ◁ᵥ{π, MetaNone} r @ ty) True (λ L' _ R,
      introduce_with_hooks E L' R (λ L2,
      li_tactic (compute_layout_goal (ty_syn_type ty MetaNone)) (λ ly,
        ⌜syn_type_has_layout st ly⌝ ∗
        T L2)))
    ⊢ owned_subtype π E L false v' r (value_t false st) (ty) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" $! _ True%I with "[//] [//] [//] CTX HE HL []") as "(%L2 & %κs & %R & >(HR & Hv' & _) & HL & HT)".
    { iApply maybe_logical_step_intro. done. }
    rewrite /compute_layout_goal.
    iMod ("HT" with "[//] CTX HE HL HR") as "(%L3 & HL & %ly & %Hst1 & %Hst2 & HT)".
    iExists _. iFrame. iModIntro.
    iPoseProof (ty_own_val_sidecond with "Hv'") as "#$".
    iSplitR. { iPureIntro. simpl.
      eapply syn_type_size_eq_prove; [ | done..].
      by apply syn_type_has_layout_untyped. }
    iSplitR; first by eauto.
    iIntros (v) "Hv".
    by iApply (own_val_merge_value_untyped with "Hv Hv'").
  Qed.
  (* shouldn't have super high priority because the conclusion is very general *)
  Definition owned_subtype_merge_untyped_value_inst := [instance @owned_subtype_merge_untyped_value].
  Global Existing Instance owned_subtype_merge_untyped_value_inst | 30.
End rules.

Section unify_loc.
  Context `{!typeGS Σ}.

  Lemma owned_subltype_step_ofty_value_unify_vs π E L step l vs1 vs2 typed st T :
    ⌜vs1 = vs2⌝ ∗ T L True%I
    ⊢ owned_subltype_step π E L step l (#vs1) (#vs2) (◁ value_t typed st) (◁ value_t typed st) T.
  Proof.
    iIntros "(-> & HT)" (????) "#CTX #HE HL Hl".
    iExists L, True%I. iFrame.
    iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition owned_subltype_step_ofty_value_unify_vs_inst := [instance @owned_subltype_step_ofty_value_unify_vs].
  Global Existing Instance owned_subltype_step_ofty_value_unify_vs_inst | 5.

  (* instantiate in case [st2] is an evar *)
  Lemma owned_subltype_step_ofty_value_st_evar π E L step l typed1 typed2 st1 st2 vs1 vs2 `{!ContainsProtected st2} T :
    ⌜st1 = st2⌝ ∗
    owned_subltype_step π E L step l (#vs1) (#vs2) (◁ value_t typed1 st1) (◁ value_t typed2 st1) T
    ⊢ owned_subltype_step π E L step l (#vs1) (#vs2) (◁ value_t typed1 st1) (◁ value_t typed2 st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Definition owned_subltype_step_ofty_value_st_evar_inst := [instance @owned_subltype_step_ofty_value_st_evar].
  Global Existing Instance owned_subltype_step_ofty_value_st_evar_inst | 10.

  (* instantiate in case [typed2] is an evar *)
  Lemma owned_subltype_step_ofty_value_typed_evar π E L step l typed1 typed2 st1 st2 vs1 vs2 `{!IsProtected typed2} T :
    ⌜typed1 = typed2⌝ ∗
    owned_subltype_step π E L step l (#vs1) (#vs2) (◁ value_t typed1 st1) (◁ value_t typed1 st2) T
    ⊢ owned_subltype_step π E L step l (#vs1) (#vs2) (◁ value_t typed1 st1) (◁ value_t typed2 st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Definition owned_subltype_step_ofty_value_typed_evar_inst := [instance @owned_subltype_step_ofty_value_typed_evar].
  Global Existing Instance owned_subltype_step_ofty_value_typed_evar_inst | 11.

  (* if both are untyped, and have not been handled by the previous instance,
     check if the sizes of the layout are the same;
     - if so, fully subsume the values
     - else if the size of the first layout is smaller, prove that the left one is a prefix of the latter, and continue searching for the rest.
     - else, the goal refers to a subset of the current chunk and we split off. *)
  Lemma owned_subltype_step_ofty_value_literal_full π E L step l vs1 vs2 ly1 ly2 T `{!LayoutSizeEq ly1 ly2} :
    (⌜l `has_layout_loc` ly1⌝ -∗
      ⌜ly_align_in_bounds ly1⌝ -∗
      ⌜l `has_layout_loc` ly2⌝ ∗ ⌜vs1 = vs2⌝ ∗ ⌜ly_align_in_bounds ly2⌝ ∗ ⌜layout_wf ly2⌝ ∗ T L True%I)
    ⊢ owned_subltype_step π E L step l vs1 vs2
      (◁ value_t false (LiteralSynType ly1)) (◁ value_t false (LiteralSynType ly2)) T.
  Proof.
    iIntros "HT".
    iIntros (F ???) "#CTX #HE HL Hl". iModIntro. iExists L, True%I. iFrame.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hly' & %Hlyl)". simp_ltypes in Hly'. simpl in *.
    apply syn_type_has_layout_untyped_inv in Hly'.
    apply syn_type_has_layout_literal_inv in Hly' as (-> & ? & ? & ?).
    iPoseProof ("HT" with "[//] [//]") as "(% & -> & % & % & HT)".
    iPoseProof (ofty_value_untyped_update_layout ly2 with "Hl") as "Hl".
    { done. }
    { done. }
    { done. }
    { done. }
    iFrame. iApply (maybe_logical_step_intro). iL. done.
  Qed.
  Definition owned_subltype_step_ofty_value_literal_full_inst := [instance @owned_subltype_step_ofty_value_literal_full].
  Global Existing Instance owned_subltype_step_ofty_value_literal_full_inst | 6.

  Lemma owned_subltype_step_ofty_value_array_typed π E L step l vs1 vs2 st1 st2 n1 n2  T :
    ⌜fast_eq_hint (st1 = st2)⌝ ∗ ⌜fast_lia_hint (n1 = n2)⌝ ∗
    ⌜vs1 = vs2⌝ ∗
    T L True%I
    ⊢ owned_subltype_step π E L step l vs1 vs2 (◁ value_t true (ArraySynType st1 n1)) (◁ value_t true (ArraySynType st2 n2)) T.
  Proof.
    iIntros "(<- & <- & <- & HT)".
    iIntros (????) "CTX HE ? ?".
    iFrame. iApply maybe_logical_step_intro.
    by iFrame.
  Qed.
  Definition owned_subltype_step_ofty_value_array_typed_inst := [instance @owned_subltype_step_ofty_value_array_typed].
  Global Existing Instance owned_subltype_step_ofty_value_array_typed_inst | 15.

  (** For untyped values, we can collapse UntypedSynType *)
  Lemma owned_subltype_step_ofty_value_untyped_l π E L step l vs1 vs2 st1 st2 T :
    owned_subltype_step  π E L step l vs1 vs2
      (◁ value_t false st1) (◁ value_t false st2) T
    ⊢ owned_subltype_step π E L step l vs1 vs2
      (◁ value_t false (UntypedSynType st1)) (◁ value_t false st2) T.
  Proof.
    iIntros "HT".
    iIntros (F ???) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hly' & %Hlyl)". simp_ltypes in Hly'. simpl in *.
    apply syn_type_has_layout_untyped_inv in Hly'.
    (*iPoseProof ("HT" with "[//] [//]") as "(% & -> & % & % & HT)".*)
    iPoseProof (ofty_value_untyped_to_literal with "Hl") as "Hl".
    { done. }
    iPoseProof (ofty_value_untyped_from_literal st1 with "Hl") as "Hl".
    { apply syn_type_has_layout_untyped_inv in Hly'. done. }
    iApply ("HT" with "[] [] [] CTX HE HL Hl"); done.
  Qed.
  Definition owned_subltype_step_ofty_value_untyped_l_inst := [instance @owned_subltype_step_ofty_value_untyped_l].
  Global Existing Instance owned_subltype_step_ofty_value_untyped_l_inst | 14.

  Lemma owned_subltype_step_ofty_value_untyped_r π E L step l vs1 vs2 st1 st2 T :
    owned_subltype_step  π E L step l vs1 vs2
      (◁ value_t false st1) (◁ value_t false st2) T
    ⊢ owned_subltype_step π E L step l vs1 vs2
      (◁ value_t false st1) (◁ value_t false (UntypedSynType st2)) T.
  Proof.
    iIntros "HT".
    iIntros (F ???) "#CTX #HE HL Hl".
    iMod ("HT" with "[] [] [] CTX HE HL Hl") as "(%L2 & %R & Hstep & HL & HT)"; [done.. | ].
    iFrame.
    iApply (maybe_logical_step_wand with "[] Hstep").
    iIntros "(Hl & $)".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hly' & %Hlyl)". simp_ltypes in Hly'. simpl in *.
    iPoseProof (ofty_value_untyped_to_literal with "Hl") as "Hl".
    { apply syn_type_has_layout_untyped_inv in Hly'. done. }
    iPoseProof (ofty_value_untyped_from_literal (UntypedSynType st2) with "Hl") as "Hl".
    { done. }
    done.
  Qed.
  Definition owned_subltype_step_ofty_value_untyped_r_inst := [instance @owned_subltype_step_ofty_value_untyped_r].
  Global Existing Instance owned_subltype_step_ofty_value_untyped_r_inst | 14.

  Lemma owned_subltype_step_ofty_untyped π E L step l vs1 vs2 st1 st2 T :
    ⌜syn_type_compat st1 st2⌝ ∗ ⌜vs1 = vs2⌝ ∗
    T L True%I
    ⊢ owned_subltype_step π E L step l vs1 vs2 (◁ value_t false st1) (◁ value_t false st2) T.
  Proof.
    iIntros "(%Hcomp & <- & HT)".
    iIntros (????) "CTX HE ? Hl".
    iFrame. iApply maybe_logical_step_intro.
    iL.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hly' & %Hlyl)". simp_ltypes in Hly'. simpl in *.
    iPoseProof (ofty_value_untyped_to_literal with "Hl") as "Hl".
    { apply syn_type_has_layout_untyped_inv in Hly'. done. }

    iPoseProof (ofty_value_untyped_from_literal st2 with "Hl") as "Hl".
    { apply Hcomp. by apply syn_type_has_layout_untyped_inv. }
    done.
  Qed.
  Definition owned_subltype_step_ofty_untyped_inst := [instance @owned_subltype_step_ofty_untyped].
  Global Existing Instance owned_subltype_step_ofty_untyped_inst | 40.
End unify_loc.

Section unify_val.
  Context `{!typeGS Σ}.

  (** Same instances for the case that we have just values *)

  (* if both are using the same st, unify the values *)
  Lemma owned_subtype_value_unify_vs E L π vs1 vs2 typed st T :
    ⌜vs1 = vs2⌝ ∗ T L
    ⊢ owned_subtype π E L false vs1 vs2 (value_t typed st) (value_t typed st) T.
  Proof.
    iIntros "(-> & HT)". iApply owned_subtype_id. iFrame. done.
  Qed.
  Definition owned_subtype_value_unify_vs_inst := [instance @owned_subtype_value_unify_vs].
  Global Existing Instance owned_subtype_value_unify_vs_inst | 5.

  (* instantiate in case [st2] is an evar *)
  Lemma owned_subtype_value_st_evar E L π typed1 typed2 st1 st2 vs1 vs2 `{!IsProtected st2} T :
    ⌜st1 = st2⌝ ∗ owned_subtype π E L false vs1 vs2 (value_t typed1 st1) (value_t typed2 st1) T
    ⊢ owned_subtype π E L false vs1 vs2 (value_t typed1 st1) (value_t typed2 st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Definition owned_subtype_value_st_evar_inst := [instance @owned_subtype_value_st_evar].
  Global Existing Instance owned_subtype_value_st_evar_inst | 10.

  (* instantiate in case [typed2] is an evar *)
  Lemma owned_subtype_value_typed_evar E L π typed1 typed2 st1 st2 vs1 vs2 `{!IsProtected typed2} T :
    ⌜typed1 = typed2⌝ ∗ owned_subtype π E L false vs1 vs2 (value_t typed1 st1) (value_t typed1 st2) T
    ⊢ owned_subtype π E L false vs1 vs2 (value_t typed1 st1) (value_t typed2 st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Definition owned_subtype_value_typed_evar_inst := [instance @owned_subtype_value_typed_evar].
  Global Existing Instance owned_subtype_value_typed_evar_inst | 11.

  (* for untyped, require compatibility of the layouts *)
  Lemma owned_subtype_value_literal_full π E L pers vs1 vs2 ly1 ly2 T `{!LayoutSizeEq ly1 ly2} :
    li_tactic (compute_layout_goal (LiteralSynType ly1)) (λ ly1',
    li_tactic (compute_layout_goal (LiteralSynType ly2)) (λ ly2',
    ⌜ly_align_log ly2 ≤ ly_align_log ly1⌝ ∗ ⌜vs1 = vs2⌝ ∗ T L))
    ⊢ owned_subtype π E L pers vs1 vs2 (value_t false (LiteralSynType ly1)) (value_t false (LiteralSynType ly2)) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1' & %Halg1 & %ly2' & %Halg2 & %Hal & -> & HT)".
    assert (Halg1' := Halg1). assert (Halg2' := Halg2).
    apply syn_type_has_layout_literal_inv in Halg1 as (-> & ?).
    apply syn_type_has_layout_literal_inv in Halg2 as (-> & ?).
    iIntros (????) "#CTX #HE HL".
    iExists L. iFrame. iModIntro.
    iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplitR.
    { iPureIntro. eapply syn_type_size_eq_prove.
      - apply value_syn_type. exact Halg1'.
      - apply value_syn_type. exact Halg2'.
      - done. }
    iSplitR; first by eauto.
    iIntros (v) "Hv".
    iApply value_untyped_layout_mono; last done.
    - done.
    - intros. by eapply layout_wf_mono.
    - intros. by eapply ly_align_in_bounds_mono.
  Qed.
  Definition owned_subtype_value_literal_full_inst := [instance @owned_subtype_value_literal_full].
  Global Existing Instance owned_subtype_value_literal_full_inst | 6.

  Lemma owned_subtype_value_array π E L pers vs1 vs2 typed1 typed2 st1 st2 n1 n2 T :
    ⌜fast_eq_hint (typed1 = typed2)⌝ ∗
    ⌜fast_eq_hint (st1 = st2)⌝ ∗
    ⌜fast_lia_hint (n1 = n2)⌝ ∗
    ⌜vs1 = vs2⌝ ∗
    T L
    ⊢ owned_subtype π E L pers vs1 vs2 (value_t typed1 (ArraySynType st1 n1)) (value_t typed2 (ArraySynType st2 n2)) T.
  Proof.
    iIntros "(<- & <- & <- & <- & HT)".
    iApply owned_subtype_id. by iFrame.
  Qed.
  Definition owned_subtype_value_array_inst := [instance @owned_subtype_value_array].
  Global Existing Instance owned_subtype_value_array_inst | 15.
End unify_val.

Section typed_value.
  Context `{!typeGS Σ}.

  (** A thin wrapper that abstracts over the value refinement.
      Basically says that there is a valid value for the given syntype.*)
  Program Definition typed_value_t (st : syn_type) : type unitRT := {|
    st_own π r v :=
      (∃ vs, v ◁ᵥ{π, MetaNone} vs @ value_t true st)%I;
    st_syn_type := st;
    st_has_op_type ot' := is_value_ot true st ot';
  |}.
  Next Obligation.
    iIntros (st π [] v) "(%vs & Hv)".
    by iPoseProof (ty_has_layout with "Hv") as "?".
  Qed.
  Next Obligation.
    simpl.
    intros st ot Hot.
    eapply (@ty_op_type_stable _ _ _ (value_t true st) ot).
    rewrite ty_has_op_type_unfold. done.
  Qed.
  Next Obligation.
    simpl. intros st ot Hot.
    eapply (ty_op_type_wf (value_t true st)).
    rewrite ty_has_op_type_unfold//.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (st ot hst π [] v Hot) "(%vs & Hv)".
    iApply (ty_decodable valRT (value_t true st) ot hst π vs v with "Hv").
    rewrite ty_has_op_type_unfold//.
  Qed.
  Next Obligation.
    iIntros (st ot hst π [] v v' Hot Hsame) "(%vs & Hv)".
    iExists vs. iApply (ty_decode_compat valRT (value_t true st) ot hst π vs v v' with "Hv"); [| done].
    rewrite ty_has_op_type_unfold//.
  Qed.
  Next Obligation.
    intros st ly Hst. simpl.
    opose proof* (ty_sized_has_op_type_untyped (value_t true st)) as Ha; first done.
    move: Ha. rewrite ty_has_op_type_unfold. done.
    Unshelve. apply _.
  Qed.

  Global Instance typed_value_copy st : Copyable (typed_value_t st).
  Proof. apply _. Qed.

  Global Instance typed_value_sized st : TySized (typed_value_t st).
  Proof. apply _. Qed.

  Lemma owned_type_incl_value_typed_value π v st :
    ⊢ owned_type_incl π v () (value_t true st) (typed_value_t st).
  Proof.
    iR. iSplitR. { eauto. }
    iIntros (vs) "Hv".
    iEval (rewrite /ty_own_val/=).
    by iFrame.
  Qed.

End typed_value.


Section move_value.
  Context `{!typeGS Σ}.

  (** These rules read a value, leave a value, and introduce the actual value type assignment into the context.
    This allows us to move the value back into the place we moved out of later on.

    We don't use this formulation for typed reads right now, as our assembly of loop invariants doesn't move values in currently.
    In the future, we could conceivably fix that.
    However, it is also not clear on the Rust semantics side if a move shouldn't actually overwrite with poison, in which case these rules wouldn't work.

    Notably, however, we use this formulation of rules for [UntypedOp] reads, which typically appear only in our low-level implementations of operations like [ptr::copy_nonoverlapping].
    *)


  Lemma type_read_ofty_move_owned_value E L {rt} π l (ty : type rt) r ot bmin `{Hstrong : !TCDone (place_update_kind_allows_strong_updates bmin)} (T : typed_read_end_cont_t bmin rt) :
    (⌜use_op_alg (ty_syn_type ty MetaNone) = Some ot⌝ ∗
      ⌜ty_has_op_type ty ot⌝ ∗
      ∀ v v', v ◁ᵥ{π, MetaNone} r @ ty -∗
      T L v' _ (value_t true (ty.(ty_syn_type) MetaNone)) v val
      (◁ value_t true (ty.(ty_syn_type) MetaNone)) (#v)
      (mkPUKRes (allowed:=bmin) UpdStrong I (opt_place_update_eq_strong _ Hstrong)))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned) bmin ot ReadDoMove T.
  Proof.
    iIntros "(%Hotalg & %Hot & Hs)" (F ????) "#CTX #HE HL Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (@ty_op_type_stable _ _ _ ty ot Hot) as Halg''.
    rewrite /use_op_alg' in Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv".
    iPoseProof (own_val_split_value with "Hv") as "(#Hv1 & Hv)".
    { done. }
    { rewrite /use_op_alg' Hotalg /=. done. }
    iMod ("Hcl" $! v _ (value_t true (ty.(ty_syn_type) MetaNone)) (v) with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { done. }
    iModIntro.

    iSpecialize ("Hs" with "Hv").
    iFrame.
    (* For this to work, we need Hotalg: ot to be the syntypes' canonical optype.
      From the fact that [ty] is compatible with an optype, it doesn't follow that the corresponding value is compatible.
      Maybe this is somethign we can fix?
    *)
    iPoseProof (ty_memcast_compat valRT (value_t true (ty.(ty_syn_type) MetaNone)) ot st with "Hv1") as "Hv2".
    { rewrite ty_has_op_type_unfold. exists ot. split_and!; first done; last done. by apply is_value_ot_core_refl. }
    iR. iR. iL. destruct bmin; done.
  Qed.
  (*Definition type_read_ofty_move_owned_value_inst := [instance @type_read_ofty_move_owned_value].*)
  (*Global Existing Instance type_read_ofty_move_owned_value_inst | 21.*)

  (* We have a more specialized instance for [Untyped] *)
  Lemma type_read_ofty_move_owned_value_untyped E L {rt} π l (ty : type rt) r ly bmin `{Hstrong : !TCDone (place_update_kind_allows_strong_updates bmin)} (T : typed_read_end_cont_t bmin rt) :
    (⌜use_layout_alg (ty_syn_type ty MetaNone) = Some ly⌝ ∗
      ⌜ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone))⌝ ∗
      ∀ v v', v ◁ᵥ{π, MetaNone} r @ ty -∗
      T L v' _ (value_t false (ty_syn_type ty MetaNone)) v val
      (◁ value_t true (ty.(ty_syn_type) MetaNone)) (#v)
      (mkPUKRes (allowed:=bmin) UpdStrong I (opt_place_update_eq_strong _ Hstrong)))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned) bmin (UntypedOp ly) ReadDoMove T.
  Proof.
    iIntros "(%Halg & %Htyot & Hs)" (F ????) "#CTX #HE HL Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly' & %Halg' & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iR. iR.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv".

    eapply syn_type_has_layout_op_alg in Halg as (ot & Hot & <-).
    iPoseProof (own_val_split_value with "Hv") as "(Hv' & Hv)".
    { done. }
    { done. }
    iPoseProof (own_val_split_value_untyped with "Hv") as "(Hv'' & Hv)".
    { done. }

    iMod ("Hcl" $! v _ (value_t true (ty.(ty_syn_type) MetaNone)) (v) with "Hl [//] [] Hv'") as "Hl".
    { simpl. done. }
    iModIntro.
    iSpecialize ("Hs" with "Hv").
    rewrite mem_cast_UntypedOp; last done.
    iFrame.
    iR. iL.
    destruct bmin; done.
  Qed.
  Definition type_read_ofty_move_owned_value_untyped_inst := [instance @type_read_ofty_move_owned_value_untyped].
  Global Existing Instance type_read_ofty_move_owned_value_untyped_inst | 20.
End move_value.

Section move_uninit.
  Context `{!typeGS Σ}.

  (** This alternative set of rules instead keeps a [typed_value_t] in the place we moved from, forgetting the concrete identity of the value, but keeping the knowledge that it is a valid byte sequence.

    We don't have a corresponding rule for Untyped reads right now, but could add one. *)

  Lemma type_read_ofty_move_owned_typed_value E L {rt} π l (ty : type rt) r ot bmin `{Hstrong : !TCDone (place_update_kind_allows_strong_updates bmin)} (T : typed_read_end_cont_t bmin rt) :
    (⌜use_op_alg (ty_syn_type ty MetaNone) = Some ot⌝ ∗
      ⌜ty_has_op_type ty ot⌝ ∗
      ∀ v,
      T L v _ ty r _
      (◁ typed_value_t (ty.(ty_syn_type) MetaNone)) (#())
      (mkPUKRes (allowed:=bmin) UpdStrong I (opt_place_update_eq_strong _ Hstrong)))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned) bmin ot ReadDoMove T.
  Proof.
    iIntros "(%Hotalg & %Hot & Hs)" (F ????) "#CTX #HE HL Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (@ty_op_type_stable _ _ _ ty ot Hot) as Halg''.
    rewrite /use_op_alg' in Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv".
    iPoseProof (own_val_split_value with "Hv") as "(#Hv1 & Hv)".
    { done. }
    { rewrite /use_op_alg' Hotalg /=. done. }

    iSpecialize ("Hs" $! _).
    iFrame.

    iMod ("Hcl" $! v _ (typed_value_t (ty.(ty_syn_type) MetaNone)) (tt) with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { iEval (rewrite /ty_own_val/=). iR. iExists v. by iFrame. }
    iModIntro.
    iFrame.

    (* For this to work, we need Hotalg: ot to be the syntypes' canonical optype.
      From the fact that [ty] is compatible with an optype, it doesn't follow that the corresponding value is compatible.
      Maybe this is somethign we can fix?
    *)
    iPoseProof (ty_memcast_compat valRT (value_t true (ty.(ty_syn_type) MetaNone)) ot st with "Hv1") as "Hv2".
    { rewrite ty_has_op_type_unfold. exists ot. split_and!; first done; last done. by apply is_value_ot_core_refl. }
    iPoseProof (own_val_merge_value_typed with "Hv2 Hv") as "$".
    { rewrite /use_op_alg' Hotalg//. }
    iR. iL. destruct bmin; done.
  Qed.
  Definition type_read_ofty_move_owned_typed_value_inst := [instance @type_read_ofty_move_owned_typed_value].
  Global Existing Instance type_read_ofty_move_owned_typed_value_inst | 21.

  (* We also have a corresponding rule for Uniq ownership that leaves [Opened].
    This allows us to move out of mutable references, as long as another object is moved in at a later point. *)
  Lemma type_read_ofty_move_uniq_typed_value E L {rt} π l (ty : type rt) κ γ r ot bmin `{Hstrong : !TCDone (place_update_kind_allows_strong_updates bmin)} (T : typed_read_end_cont_t bmin rt) :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    (⌜use_op_alg (ty_syn_type ty MetaNone) = Some ot⌝ ∗
      ⌜ty_has_op_type ty ot⌝ ∗
      ∀ v,
      T L2 v _ ty r _
      (OpenedLtype (◁ typed_value_t (ty.(ty_syn_type) MetaNone)) (◁ ty) (◁ ty) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs))
      (#())
      (mkPUKRes (allowed:=bmin) UpdStrong I (opt_place_update_eq_strong _ Hstrong))))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Uniq κ γ) bmin ot ReadDoMove T.
  Proof.
    iIntros "HT" (F ????) "#CTX #HE HL Hb".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "HT" as (κs L2) "(%Hal & %Hotalg & %Hot & HT)".

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Hcl_tok & HL)"; [done.. | ].
    iPoseProof (ofty_ltype_acc_uniq with "CTX Htok Hcl_tok Hb") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.

    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (@ty_op_type_stable _ _ _ ty ot Hot) as Halg''.
    rewrite /use_op_alg' in Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iMod "Hcl_F" as "_".
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iR. iR.

    iApply (logical_step_mask_mono lftE); first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "[_ Hcl] %st Hl Hv".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.

    iPoseProof (own_val_split_value with "Hv") as "(#Hv1 & Hv)".
    { done. }
    { rewrite /use_op_alg' Hotalg /=. done. }

    iSpecialize ("HT" $! _).
    iFrame "HT".

    iMod ("Hcl" $! v _ (typed_value_t (ty.(ty_syn_type) MetaNone)) (tt) with "Hl [//] [] []") as "Hl".
    { iEval (rewrite /ty_own_val/=). iR. iExists v. by iFrame. }
    { done. }
    iMod "Hcl_F" as "_".
    iFrame.

    (* For this to work, we need Hotalg: ot to be the syntypes' canonical optype.
      From the fact that [ty] is compatible with an optype, it doesn't follow that the corresponding value is compatible.
      Maybe this is somethign we can fix?
    *)
    iPoseProof (ty_memcast_compat valRT (value_t true (ty.(ty_syn_type) MetaNone)) ot st with "Hv1") as "Hv2".
    { rewrite ty_has_op_type_unfold. exists ot. split_and!; first done; last done. by apply is_value_ot_core_refl. }
    iPoseProof (own_val_merge_value_typed with "Hv2 Hv") as "$".
    { rewrite /use_op_alg' Hotalg//. }
    iFrame.
    iR. iL. destruct bmin; done.
  Qed.
  Definition type_read_ofty_move_uniq_typed_value_inst := [instance @type_read_ofty_move_uniq_typed_value].
  Global Existing Instance type_read_ofty_move_uniq_typed_value_inst | 21.
End move_uninit.

Section stratify.
  Context `{!typeGS Σ}.

  (* We only stratify values if enabled for this mode *)
  Lemma stratify_ltype_ofty_typed_value_owned π E L mdu ma {M} (m : M) l st v `{!StratifyLtypeShouldMoveValues m} (T : stratify_ltype_cont_t) :
    find_in_context (FindVal v) (λ '(existT rt (ty', r', π', m)),
      ⌜π' = π⌝ ∗ ⌜m = MetaNone⌝ ∗
      ⌜ty_has_op_type ty' (use_op_alg' (ty'.(ty_syn_type) m))⌝ ∗
      ⌜ty'.(ty_syn_type) m = st⌝ ∗
      stratify_ltype π E L mdu ma m l (◁ ty') (#r') (Owned) T)
    ⊢ stratify_ltype π E L mdu ma m l (◁ value_t true st)%I (#v) (Owned) T.
  Proof.
    iDestruct 1 as ([rt [[[ty' r'] π'] m']]) "(Hv & -> & -> & %Hot & %Heq & HT)" => /=.
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "#(%ly & %Hst &_)".
    subst st.
    iPoseProof (ofty_own_merge_value_typed with "Hv Hl") as "Ha".
    { done. }
    iMod ("HT" with "[//] [//] [//] CTX HE HL Ha") as "Ha".
    eauto.
  Qed.
  (* needs to have a higher priority than the ofty_resolve_ghost instance *)
  Definition stratify_ltype_ofty_typed_value_owned_inst := [instance @stratify_ltype_ofty_typed_value_owned].
  Global Existing Instance stratify_ltype_ofty_typed_value_owned_inst | 10.

  Lemma stratify_ltype_ofty_untyped_value_owned π E L mdu ma {M} (m : M) l st v `{!StratifyLtypeShouldMoveValues m} (T : stratify_ltype_cont_t) :
    find_in_context (FindVal v) (λ '(existT rt (ty', r', π', m)),
      ⌜π' = π⌝ ∗ ⌜m = MetaNone⌝ ∗
      ⌜fast_syntype_eq_hint (ty'.(ty_syn_type) m = st)⌝ ∗
      stratify_ltype π E L mdu ma m l (◁ ty') (#r') (Owned) T)
    ⊢ stratify_ltype π E L mdu ma m l (◁ value_t false st)%I (#v) (Owned) T.
  Proof.
    unfold fast_syntype_eq_hint.
    iDestruct 1 as ([rt [[[ty' r'] π'] m']]) "(Hv & -> & -> & %Heq & HT)" => /=.
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "#(%ly & %Hst &_)".
    subst st.
    simp_ltypes.  simpl.
    iPoseProof (ofty_own_merge_value_untyped with "Hv Hl") as "Ha".
    { apply value_syn_type_inv in Hst. done. }
    { apply value_syn_type_inv in Hst. done. }
    iMod ("HT" with "[//] [//] [//] CTX HE HL Ha") as "(% & % & % & % & % & ? & %Hcomp & ? & ?)".
    iFrame. iPureIntro. by apply syn_type_compat_untyped_l.
  Qed.
  (* needs to have a higher priority than the ofty_resolve_ghost instance *)
  Definition stratify_ltype_ofty_untyped_value_owned_inst := [instance @stratify_ltype_ofty_untyped_value_owned].
  Global Existing Instance stratify_ltype_ofty_untyped_value_owned_inst | 10.
End stratify.

Section op_rules.
  Context `{!typeGS Σ}.

  (** Rules for simplifying value hypotheses in operands *)

  Lemma simplify_hyp_value_merge_typed E L π v vs st T :
    find_in_context (FindVal vs) (λ '(existT rt (ty, r, π', m)),
      ⌜π' = π⌝ ∗ ⌜m = MetaNone⌝ ∗
      ⌜ty_has_op_type ty (use_op_alg' (st_of ty MetaNone))⌝ ∗
      ⌜st = st_of ty MetaNone⌝ ∗
      T v rt r ty)
    ⊢ simplify_hyp_value E L π (v ◁ᵥ{π, MetaNone} vs @ value_t true st) T.
  Proof.
    rewrite /FindVal.
    iIntros "(%ty & HT)".
    simpl. destruct ty as [rt (((ty & r) & π') & m)].
    simpl. iDestruct "HT" as "(Hv & -> & -> & %Hot & -> & HT)".
    iIntros (??) "CTX HE HL HP".
    iPoseProof (own_val_merge_value_typed with "HP Hv") as "Hv"; first done.
    by iFrame.
  Qed.
  Definition simplify_hyp_value_merge_typed_inst := [instance @simplify_hyp_value_merge_typed].
  Global Existing Instance simplify_hyp_value_merge_typed_inst.

  Lemma simplify_hyp_value_merge_untyped E L π v vs st T :
    find_in_context (FindVal vs) (λ '(existT rt (ty, r, π', m)),
      ⌜π' = π⌝ ∗ ⌜m = MetaNone⌝ ∗
      ⌜st = st_of ty MetaNone⌝ ∗
      T v rt r ty)
    ⊢ simplify_hyp_value E L π (v ◁ᵥ{π, MetaNone} vs @ value_t false st) T.
  Proof.
    rewrite /FindVal.
    iIntros "(%ty & HT)".
    simpl. destruct ty as [rt (((ty & r) & π') & m)].
    simpl. iDestruct "HT" as "(Hv & -> & -> & -> & HT)".
    iIntros (??) "CTX HE HL HP".
    iPoseProof (own_val_merge_value_untyped with "HP Hv") as "Hv".
    by iFrame.
  Qed.
  Definition simplify_hyp_value_merge_untyped_inst := [instance @simplify_hyp_value_merge_untyped].
  Global Existing Instance simplify_hyp_value_merge_untyped_inst.

  Lemma typed_un_op_simplify_hyp_value E L f v P op ot T :
    simplify_hyp_value E L f.1 P (λ v' rt r ty,
      typed_un_op E L f v (v' ◁ᵥ{f.1, MetaNone} r @ ty) op ot T)
    ⊢ typed_un_op E L f v P op ot T.
  Proof.
    iIntros "HT HP".
    iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("HT" with "[] CTX HE HL HP") as "(%v' & %rt & %ty & %r & HL & Hv & HT)"; [done.. | ].
    iApply ("HT" with "Hv CTX HE HL Hf Hcont").
  Qed.
  Definition typed_un_op_simplify_hyp_value_value_t E L f v vs m typed st op ot T :=
    typed_un_op_simplify_hyp_value E L f v (v ◁ᵥ{f.1, m} vs @ value_t typed st) op ot T.
  Definition typed_un_op_simplify_hyp_value_value_t_inst := [instance @typed_un_op_simplify_hyp_value_value_t].
  Global Existing Instance typed_un_op_simplify_hyp_value_value_t_inst | 1001.

  Lemma typed_bin_op_simplify_hyp_value_l E L f v1 P1 v2 P2 op ot1 ot2 T :
    simplify_hyp_value E L f.1 P1 (λ v' rt r ty,
      typed_bin_op E L f v1 (v' ◁ᵥ{f.1, MetaNone} r @ ty) v2 P2 op ot1 ot2 T)
    ⊢ typed_bin_op E L f v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "HT HP1 HP2".
    iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("HT" with "[] CTX HE HL HP1") as "(%v' & %rt & %ty & %r & HL & Hv & HT)"; [done.. | ].
    iApply ("HT" with "Hv HP2 CTX HE HL Hf Hcont").
  Qed.
  Definition typed_bin_op_simplify_hyp_value_value_t_l E L f v1 v2 P2 vs m typed st op ot1 ot2 T :=
    typed_bin_op_simplify_hyp_value_l E L f v1 (v1 ◁ᵥ{f.1, m} vs @ value_t typed st) v2 P2 op ot1 ot2 T.
  Definition typed_bin_op_simplify_hyp_value_value_t_l_inst := [instance @typed_bin_op_simplify_hyp_value_value_t_l].
  Global Existing Instance typed_bin_op_simplify_hyp_value_value_t_l_inst | 1001.

  Lemma typed_bin_op_simplify_hyp_value_r E L f v1 P1 v2 P2 op ot1 ot2 T :
    simplify_hyp_value E L f.1 P2 (λ v' rt r ty,
      typed_bin_op E L f v1 P1 v2 (v' ◁ᵥ{f.1, MetaNone} r @ ty) op ot1 ot2 T)
    ⊢ typed_bin_op E L f v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "HT HP1 HP2".
    iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("HT" with "[] CTX HE HL HP2") as "(%v' & %rt & %ty & %r & HL & Hv & HT)"; [done.. | ].
    iApply ("HT" with "HP1 Hv CTX HE HL Hf Hcont").
  Qed.
  Definition typed_bin_op_simplify_hyp_value_value_t_r E L f v1 v2 P1 vs m typed st op ot1 ot2 T :=
    typed_bin_op_simplify_hyp_value_r E L f v1 P1 v2 (v2 ◁ᵥ{f.1, m} vs @ value_t typed st) op ot1 ot2 T.
  Definition typed_bin_op_simplify_hyp_value_value_t_r_inst := [instance @typed_bin_op_simplify_hyp_value_value_t_r].
  Global Existing Instance typed_bin_op_simplify_hyp_value_value_t_r_inst | 1001.

  Lemma typed_if_simplify_hyp_value E L π v P T1 T2 :
    simplify_hyp_value E L π P (λ v' rt r ty,
      typed_if E L π v (v' ◁ᵥ{π, MetaNone} r @ ty) T1 T2)
    ⊢ typed_if E L π v P T1 T2.
  Proof.
    iIntros "HT". iIntros (??) "#CTX #HE HL HP".
    iMod ("HT" with "[//] CTX HE HL HP") as "(%v' & %rt & %ty & %r & HL & Hv & HT)".
    by iApply ("HT" with "[] CTX HE HL Hv").
  Qed.
  Definition typed_if_simplify_hyp_value_value_t E L π v vs m typed st T1 T2 :=
    typed_if_simplify_hyp_value E L π v (v ◁ᵥ{π, m} vs @ value_t typed st) T1 T2.
  Definition typed_if_simplify_hyp_value_value_t_inst := [instance @typed_if_simplify_hyp_value_value_t].
  Global Existing Instance typed_if_simplify_hyp_value_value_t_inst | 1001.

  Lemma typed_switch_simplify_hyp_value_value_t E L f v typed st vs it M s def fn R ϝ :
    simplify_hyp_value E L f.1 (v ◁ᵥ{f.1, MetaNone} vs @ value_t typed st) (λ v' rt' r' ty',
      ⌜v = v'⌝ ∗
      typed_switch E L f v ty' r' it M s def fn R ϝ)
    ⊢ typed_switch E L f v (value_t typed st) vs it M s def fn R ϝ.
  Proof.
    iIntros "HT".
    iIntros (??) "#CTX #HE HL HP".
    iMod ("HT" with "[//] CTX HE HL HP") as "(%v' & %rt & %ty & %r & HL & Hv & <- & HT)".
    by iApply ("HT" with "[] CTX HE HL Hv").
  Qed.
  Definition typed_switch_simplify_hyp_value_value_t_inst := [instance @typed_switch_simplify_hyp_value_value_t].
  Global Existing Instance typed_switch_simplify_hyp_value_value_t_inst.

  Lemma typed_assert_simplify_hyp_value_value_t E L f v typed st vs s fn R ϝ :
    simplify_hyp_value E L f.1 (v ◁ᵥ{f.1, MetaNone} vs @ value_t typed st) (λ v' rt' r' ty',
      ⌜v = v'⌝ ∗
      typed_assert E L f v ty' r' s fn R ϝ)
    ⊢ typed_assert E L f v (value_t typed st) vs s fn R ϝ.
  Proof.
    iIntros "HT".
    iIntros (??) "#CTX #HE HL Hf HP".
    iMod ("HT" with "[//] CTX HE HL HP") as "(%v' & %rt & %ty & %r & HL & Hv & <- & HT)".
    by iApply ("HT" with "[] CTX HE HL Hf Hv").
  Qed.
  Definition typed_assert_simplify_hyp_value_value_t_inst := [instance @typed_assert_simplify_hyp_value_value_t].
  Global Existing Instance typed_assert_simplify_hyp_value_value_t_inst.
End op_rules.


Global Typeclasses Opaque value_t.
Global Hint Unfold value_t : tyunfold.

Global Arguments use_op_alg_typed _ /! _ _ : simpl nomatch.



Section deinit.
  Context `{!typeGS Σ}.

  (** ** Instances for deinitializing a type *)
  (** Types have more specific instances that we generally prefer in [.../deinit.v] *)

  Lemma owned_subltype_step_ofty_val_eq π E L {rt} (lt : ltype rt) r st l `{Hst : !SynTypeEq (ltype_st lt) st} T :
    owned_subltype_step π E L true l (#r) (#()) lt (◁ typed_value_t st) T :-
    return cast_ltype_to_type E L lt (λ ty,
      ⌜ty_has_op_type ty (use_op_alg' (st_of ty MetaNone))⌝ ∗
      T L (ty_ghost_drop' ty π r)).
  Proof.
    unfold SynTypeEq in Hst. subst st.
    iDestruct 1 as "(%ty & %Heqt & %Hot & HT)".
    iIntros (????) "CTX HE HL Hl". simp_ltypes; simpl.

    iPoseProof (full_eqltype_acc with "CTX HE HL") as "(%Hst & #Hincl)"; first apply Heqt.
    iSpecialize ("Hincl" $! (Owned) (#r)).
    iDestruct "Hincl" as "(Hincl & _)". iDestruct "Hincl" as "(Hincl & _)".
    iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
    iExists _, _. iFrame.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst' & %)".
    simp_ltypes in Hst'.
    iMod (ofty_own_split_value_typed with "Hl") as "(%v & Hv & Hl)"; [done.. | ].
    iPoseProof (ty_own_ghost_drop with "Hv") as "Hb"; first done.
    iModIntro.
    iApply (logical_step_wand with "Hb"). iIntros "$".
    iApply (ofty_owned_subtype_aligned with "[] Hl").
    { simpl. rewrite Hst. done. }
    { done. }
    rewrite Hst.
    iApply owned_type_incl_value_typed_value.
  Qed.
  Definition owned_subltype_step_ofty_val_eq_inst := [instance owned_subltype_step_ofty_val_eq].
  Global Existing Instance owned_subltype_step_ofty_val_eq_inst | 100.
End deinit.
