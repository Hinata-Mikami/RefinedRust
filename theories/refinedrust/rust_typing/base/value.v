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
  - intros Ha%use_op_alg_untyped_inv. done.
Qed.
Lemma use_op_alg_typed_Some `{!LayoutAlg} (typed : bool) st ot ot1 :
  use_op_alg st = Some ot1 →
  ot = (if typed then ot1 else UntypedOp (ot_layout ot1)) →
  use_op_alg_typed typed st = Some ot.
Proof.
  intros Hot ->.
  unfold use_op_alg_typed.
  destruct typed; simpl; first done.
  by eapply use_op_alg_untyped.
Qed.

(* TODO: will change once we have [ArrayOp] *)
Lemma use_op_alg_typed_array `{!LayoutAlg} typed st n ly :
  syn_type_has_layout st ly →
  use_op_alg_typed typed (ArraySynType st n) = Some (UntypedOp (mk_array_layout ly n)).
Proof.
  intros Hst. rewrite /syn_type_has_layout in Hst.
  destruct typed; rewrite /use_op_alg_typed /use_op_alg /=; rewrite Hst; done.
Qed.
Lemma use_op_alg_typed_array_inv `{!LayoutAlg} typed st n ly ot :
  syn_type_has_layout st ly →
  use_op_alg_typed typed (ArraySynType st n) = Some ot →
  ot = UntypedOp (mk_array_layout ly n).
Proof.
  intros Hst Hot.
  rewrite (use_op_alg_typed_array typed st n ly Hst) in Hot.
  injection Hot as ->. done.
Qed.

(** [ot] is the optype of the value, [ot'] is the optype we are accessing it at *)
Definition is_value_ot_core (ot : op_type) (ot' : op_type) (mt : memcast_compat_type) : Prop :=
  (∃ ly, ot' = UntypedOp ly ∧ ly = ot_layout ot) ∨
  (ot' = ot ∧ mt ≠ MCId).
Lemma is_value_ot_core_layout ot ot' mt:
  is_value_ot_core ot ot' mt → ot_layout ot' = ot_layout ot.
Proof.
  unfold is_value_ot_core.
  intros [(ly & -> & ->) | (-> & ?)]; naive_solver.
Qed.
Lemma is_value_ot_core_refl ot mt :
  mt ≠ MCId → is_value_ot_core ot ot mt.
Proof.
  unfold is_value_ot_core.
  destruct ot; simpl; naive_solver.
Qed.

(* [is_memcast_val] is preserved by optypes behaving by [is_value_ot_core] *)
Lemma is_value_ot_core_is_memcast_val_pres (typed : bool) ot ot1 vs v st :
  vs `has_layout_val` ot_layout ot1 →
  op_type_wf ot1 →
  is_value_ot_core (if typed then ot1 else UntypedOp (ot_layout ot1)) ot MCCopy →
  is_memcast_val vs (if typed then ot1 else UntypedOp (ot_layout ot1)) v →
  is_memcast_val vs (if typed then ot1 else UntypedOp (ot_layout ot1)) (mem_cast v ot st).
Proof.
  intros ? ? Hot Hmc. destruct typed; simpl.
  - destruct Hot as [(ly & -> & ->) | (-> & ?)].
    + rewrite mem_cast_UntypedOp. done.
    + apply is_memcast_val_memcast; done.
  - apply is_memcast_val_untyped_inv in Hmc as ->.
    destruct Hot as [(ly & -> & ->) | (-> & ?)].
    + rewrite mem_cast_UntypedOp. by left.
    + rewrite mem_cast_UntypedOp. by left.
Qed.
Lemma is_value_ot_core_mcid (typed : bool) ot ot1 v :
  is_value_ot_core (if typed then ot1 else UntypedOp (ot_layout ot1)) ot MCId →
  mem_cast_id v ot.
Proof.
  intros [(ly & -> & ->) | (-> & ?)]; last done.
  unfold mem_cast_id.  intros.
  rewrite mem_cast_UntypedOp//.
Qed.


Definition is_value_ot `{!LayoutAlg} (typed : bool) (st : syn_type) (ot : op_type) (mt : memcast_compat_type) : Prop :=
  ∃ ot',
    use_op_alg_typed typed st = Some ot' ∧
    is_value_ot_core ot' ot mt ∧
    (* needed because use_op_alg does less checks *)
    syn_type_has_layout st (ot_layout ot')
  .

Global Typeclasses Opaque is_value_ot.

Lemma is_value_ot_literal `{!LayoutAlg} t st mt ly :
  syn_type_has_layout st ly →
  is_value_ot t (LiteralSynType ly) (UntypedOp ly) mt.
Proof.
  intros Halg. eexists (UntypedOp ly). split_and!.
  - destruct t; try done.
  - left. eauto.
  - by eapply syn_type_has_layout_make_literal.
Qed.
(* We can only do accesses at [st] if this is actually typed *)
Lemma is_value_ot_typed_use_op_alg `{!LayoutAlg} st ly mc :
  mc ≠ MCId →
  syn_type_has_layout st ly →
  is_value_ot true st (use_op_alg' st) mc.
Proof.
  intros ? Ha.
  specialize (syn_type_has_layout_op_alg _ _ Ha) as (ot & Hot & <-).
  rewrite /use_op_alg' Hot /=.
  eexists _.
  split; first done.
  split; last done.
  right. done.
Qed.
(* Otherwise, we can only do untyped accesses *)
Lemma is_value_ot_untyped_use_op_alg `{!LayoutAlg} st ly mc :
  syn_type_has_layout st ly →
  is_value_ot false st (UntypedOp ly) mc.
Proof.
  intros Hst.
  specialize (syn_type_has_layout_op_alg _ _ Hst) as (ot & Hot & <-).
  rewrite /is_value_ot.
  exists (UntypedOp (ot_layout ot)).
  simpl. split_and!; last done.
  - by eapply use_op_alg_untyped.
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
        ⌜is_memcast_val vs ot v⌝ ∗
        ⌜v `has_layout_val` (ot_layout ot)⌝ ∗
        ⌜syn_type_has_layout st (ot_layout ot)⌝)%I;
    (* TODO: probably should put UntypedSynType around it if untyped *)
    st_syn_type := st;
    st_has_op_type ot' mt := is_value_ot typed st ot' mt;
  |}.
  Next Obligation.
    iIntros (typed st π vs v) "(%ot & % & % & % & %)". eauto.
  Qed.
  Next Obligation.
    simpl. intros typed st ot' mt (ot & Halg & Hot & Hst).
    rewrite (is_value_ot_core_layout _ _ _ Hot).
    done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    (* mem-cast *)
    intros typed st ot' mt ? π vs v (ot & Halg & Hot & Hst).
    iIntros "(%ot'' & %Halg' & %Hmc & %Hly & %Hst')".
    eapply use_op_alg_typed_inv in Halg' as (ot1 & Halg' & ->).
    apply use_op_alg_typed_inv in Halg as (ot2 & Hot2 & ->).
    assert (ot2 = ot1) as -> by by eapply use_op_alg_inj.
    destruct mt; first done.
    - iPureIntro. eexists _. split_and!; [ | | | done].
      + eapply use_op_alg_typed_Some; first done. done.
      + specialize (is_memcast_val_has_layout_val' _ _ _ _ Hmc Hly) as Hly'.
        eapply is_value_ot_core_is_memcast_val_pres; try done.
        { destruct typed; done. }
        { by eapply use_op_alg_wf. }
      + by apply has_layout_val_mem_cast.
    - iPureIntro.
      by eapply is_value_ot_core_mcid.
  Qed.
  Next Obligation.
    intros typed st mt ly Hst. simpl.
    unfold is_value_ot.
    specialize (syn_type_has_layout_op_alg st ly Hst) as (ot & Hot & <-).
    exists (if typed then ot else UntypedOp (ot_layout ot)).
    split_and!.
    - destruct typed; first done.
      eapply use_op_alg_untyped;done.
    - left. eexists. split; first done.
      by destruct typed.
    - destruct typed; done.
  Qed.

  Global Instance value_copy typed st : Copyable (value_t typed st).
  Proof. apply _. Qed.

  Global Instance value_sized typed st : TySized (value_t typed st).
  Proof. apply _. Qed.
End value.

Section lemmas.
  Context `{!typeGS Σ}.


  Lemma value_has_length π v v1 st ly typed m :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} v1 @ value_t typed st -∗
    ⌜length v1 = ly_size ly⌝ ∗ ⌜length v = ly_size ly⌝.
  Proof.
    rewrite /ty_own_val/=.
    iDestruct 1 as "(-> & %ot & %Hot & %Hmc & %Hly & %Hst)".
    assert (ly = ot_layout ot) as -> by by eapply syn_type_has_layout_inj.
    iL. iPureIntro. apply is_memcast_val_length in Hmc as ->; done.
  Qed.

  Lemma value_has_layout π typed st v vs m :
    v ◁ᵥ{π, m} vs @ value_t typed st -∗
    ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜v `has_layout_val` ly⌝.
  Proof.
    rewrite /ty_own_val.
    iDestruct 1 as "(-> & %ot & %Hot & %Hmv & %Hv & %Hst)".
    iExists (ot_layout ot). iR. done.
  Qed.

  Lemma own_val_split_value π {rt} (ty : type rt) r v ly m :
    syn_type_has_layout (ty_syn_type ty m) ly →
    v ◁ᵥ{π, m} r @ ty -∗
    v ◁ᵥ{π, MetaNone} v @ value_t true (ty_syn_type ty m) ∗ v ◁ᵥ{π, m} r @ ty.
  Proof.
    iIntros (Hly) "Hv".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    subst. iFrame.
    specialize (syn_type_has_layout_op_alg _ _ Hly) as (ot & Hot & <-).
    iR.
    iExists ot. iSplitR; first done.
    iSplitR. { iLeft. done. }
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
    - by eapply use_op_alg_untyped.
    - by left.
    - done.
    - done.
  Qed.

  Lemma own_val_merge_value_typed π {rt} (ty : type rt) r v vs :
    (* TODO: this requirement should become trivial soon *)
    ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) MCCopy →
    vs ◁ᵥ{π, MetaNone} v @ value_t true (ty_syn_type ty MetaNone) -∗
    v ◁ᵥ{π, MetaNone} r @ ty -∗
    vs ◁ᵥ{π, MetaNone} r @ ty.
  Proof.
    iIntros (Hot) "Hv1 Hv2".
    iEval (rewrite /ty_own_val/=) in "Hv1".
    iDestruct "Hv1" as "(_ & (%ot & %Hot' & %Hmc & %Hvs & %Hst))".
    rewrite /use_op_alg_typed in Hot'.
    rewrite /use_op_alg'/= Hot'/= in Hot.
    destruct Hmc as [-> | (? & ->)]; first done.
    by iApply (ty_memcast_compat_copy with "Hv2").
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
    apply use_op_alg_untyped_inv in Hot' as (ot1 & Hot' & ->).
    destruct Hmc as [-> | (? & ->)]; first done.
    by rewrite mem_cast_UntypedOp.
  Qed.

  (* NOTE: removed
  Lemma value_untyped_make_typed π st ly v vs m :
    syn_type_has_layout st ly →
    v ◁ᵥ{π, m} vs @ value_t (UntypedSynType ly) -∗
    v ◁ᵥ{π, m} vs @ value_t st.
  Proof.
    iIntros "%Halg Hv".
    rewrite /ty_own_val /=. iDestruct "Hv" as "(-> & %ot & %Heq & %Hmc & %Hlyv & _)".
    injection Heq as <-.
    specialize (syn_type_has_layout_op_alg _ _ Halg) as (ot & Hop & <-).
    iR.
    iExists ot. iSplitR; first done.
    iSplitR. { iLeft. apply is_memcast_val_untyped_inv in Hmc. done. }
    iSplitR; first done. done.
  Qed.
  *)

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
    apply syn_type_has_layout_array_inv in Halg1 as (ly1 & Hst1 & _ & _).
    apply syn_type_has_layout_array_inv in Halg2 as (ly2 & Hst2 & _ & _).
    assert (ly1 = ly_st) as -> by by eapply syn_type_has_layout_inj.
    assert (ly2 = ly_st) as -> by by eapply syn_type_has_layout_inj.
    pose proof (use_op_alg_typed_array_inv typed st n1 ly_st ot1 Hst Heq1) as ->.
    pose proof (use_op_alg_typed_array_inv typed st n2 ly_st ot2 Hst Heq2) as ->.
    iR. iExists (UntypedOp (mk_array_layout ly_st (n1 + n2))).
    iSplitR. { iPureIntro. by apply use_op_alg_typed_array. }
    iSplitR. {
      iPureIntro. eapply is_memcast_val_array_op_merge; [| done..].
      by apply array_op_merge_untyped. }
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
    apply syn_type_has_layout_array_inv in Hst as (ly_st & Hst & _ & Hsz).
    assert (ly_st = ly) as -> by by eapply syn_type_has_layout_inj.
    pose proof (use_op_alg_typed_array_inv typed st (n1 + n2) ly ot Hst1 Hot) as ->.
    pose proof (is_memcast_val_array_op_split st n1 n2
      (UntypedOp (mk_array_layout ly (n1 + n2)))
      (UntypedOp (mk_array_layout ly n1))
      (UntypedOp (mk_array_layout ly n2)) r1 r2 v1 v2) as Hsplit.
    destruct Hsplit as [Hmc1 Hmc2].
    { by apply array_op_split_untyped. }
    { rewrite ly_size_mk_array_layout. lia. }
    { rewrite ly_size_mk_array_layout. lia. }
    { done. }
    iSplit.
    - iR. iExists (UntypedOp (mk_array_layout ly n1)).
      iSplitR. { iPureIntro. by apply use_op_alg_typed_array. }
      iSplitR. { done. }
      iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      iPureIntro. eapply syn_type_has_layout_array; [done | done |].
      rewrite ly_size_mk_array_layout in Hsz. lia.
    - iR. iExists (UntypedOp (mk_array_layout ly n2)).
      iSplitR. { iPureIntro. by apply use_op_alg_typed_array. }
      iSplitR. { done. }
      iSplitR. { iPureIntro. rewrite /has_layout_val ly_size_mk_array_layout. lia. }
      iPureIntro. eapply syn_type_has_layout_array; [done | done |].
      rewrite ly_size_mk_array_layout in Hsz. lia.
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
    iDestruct "Hl" as "(%ly' & % & % & ? & ? & %r' & <- & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (value_has_length with "Hv") as "(% & %)"; first done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iR. iModIntro. iExists _. by iFrame.
  Qed.

  Lemma ofty_own_split_value_typed π F l {rt} (ty : type rt) r :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned] #r @ ◁ ty)%I -∗ |={F}=> ∃ v,
    v ◁ᵥ{π, MetaNone} r @ ty ∗ l ◁ₗ[π, Owned] #v @ ◁ (value_t true (ty_syn_type ty MetaNone)).
  Proof.
    iIntros (?) "Hty".
    rewrite (ltype_own_ofty_unfold ty) /lty_of_ty_own.
    iDestruct "Hty" as "(%ly' & % & % & Hsc & Hlb & %r' & <- & Hb)".
    (*assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.*)
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iPoseProof (own_val_split_value _ _ _ _ with "Hv") as "(Hv' & Hv)".
    { done. }
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
    iR. iR. iFrame. done.
  Qed.

  Lemma ofty_own_merge_value_typed {rt} π (ty : type rt) v r l :
    ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) MCCopy →
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
    by iApply (own_val_merge_value_typed with "Hv' Hv").
  Qed.

  Lemma ofty_own_merge_value_untyped {rt} π (ty : type rt) `{!TySized ty} v r st l ly :
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

  (* NOTE removed
  Lemma ofty_value_untyped_make_typed π l vs st ly :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned] #vs @ ◁ value_t (UntypedSynType ly)) -∗
    l ◁ₗ[π, Owned] #vs @ ◁ value_t st.
  Proof.
    iIntros (?) "Ha".
    iApply (ofty_mono_ly_strong_in with "[] [] Ha").
    - simpl. by eapply syn_type_has_layout_make_untyped.
    - done.
    - done.
    - done.
    - iIntros (?). by iApply value_untyped_make_typed.
    - simpl. eauto.
  Qed.
  *)

  Lemma ofty_uninit_to_untyped_value F π l st :
    lftE ⊆ F →
    (l ◁ₗ[π, Owned] .@ ◁ (uninit st))%I ={F}=∗
    ∃ v, l ◁ₗ[π, Owned] #v @ (◁ value_t false st)%I.
  Proof.
    iIntros (?) "Ha".
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly & %Hst & %Hly)".
    simp_ltypes in Hst. simpl in Hst.
    iMod (ofty_own_split_value_untyped with "Ha") as "(%v & _ & Ha)"; [done.. | ].
    iExists v. done.
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
    - eapply use_op_alg_untyped; first last.
      { apply use_op_alg_literal. done. }
      done.
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
    - apply syn_type_has_layout_op_alg in Hst as (ot' & ? & Heq).
      eapply use_op_alg_untyped; last done.
      rewrite Heq. done.
    - done.
    - done.
    - done.
  Qed.

  Lemma ofty_value_untyped_from_literal st l π vs ly :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned] #vs @ ◁ value_t false (LiteralSynType ly)) -∗
    l ◁ₗ[π, Owned] #vs @ ◁ value_t false st.
  Proof.
    iIntros (Hst) "Hl".
    iApply (ofty_mono_ly_strong_in with "[] [] Hl"); simpl.
    - by eapply syn_type_has_layout_make_literal.
    - done.
    - done.
    - done.
    - iIntros (v) "Hv".
      by iApply value_untyped_from_literal.
    - eauto.
  Qed.
  Lemma ofty_value_untyped_to_literal l π vs st ly :
    syn_type_has_layout st ly →
    (l ◁ₗ[π, Owned] #vs @ ◁ value_t false st) -∗
    (l ◁ₗ[π, Owned] #vs @ ◁ value_t false (LiteralSynType ly)).
  Proof.
    iIntros (Hst) "Hl".
    iApply (ofty_mono_ly_strong_in with "[] [] Hl"); simpl.
    - done.
    - by eapply syn_type_has_layout_make_literal.
    - done.
    - done.
    - iIntros (v) "Hv".
      by iApply value_untyped_to_literal.
    - eauto.
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
    injection Heq as <-. iR. iExists _. iSplitR; first done.
    iSplitR. { apply is_memcast_val_untyped_inv in Hmc. by iLeft. }
    simpl. iSplitR. { rewrite /has_layout_val -Hsz //. }
    iPureIntro. simpl in Hst. apply syn_type_has_layout_literal_inv in Hst as (_ & Hwf' & Hsz_le & ?).
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
    apply syn_type_has_layout_literal_inv in Halg as (-> & Hwf1 & Hsz_le & Hal).
    iApply (ofty_mono_ly_strong with "[] [] Hl").
    + simpl. eapply syn_type_has_layout_literal; done.
    + simpl. eapply syn_type_has_layout_literal; first done.
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

  (** By default, we go to UntypedSynType, and can later on specialize if needed by subsumption (we cannot go the other way around due to memcast compatibility) *)
  (* NOTE: removed
  Lemma value_subsume_goal π {rt} (ty : type rt) (r : rt) v vs st m T :
    (∃ ly, ⌜syn_type_has_layout (ty.(ty_syn_type) m) ly⌝ ∗
      (v ◁ᵥ{π, m} r @ ty -∗ subsume (v ◁ᵥ{π, MetaNone} v @ value_t (UntypedSynType ly)) (v ◁ᵥ{π, MetaNone} vs @ value_t st) T))
    ⊢ subsume (v ◁ᵥ{π, m} r @ ty) (v ◁ᵥ{π, MetaNone} vs @ value_t st) T.
  Proof.
    iIntros "(%ly & %Halg & HT) Hv".
    iPoseProof (own_val_split_value _ _ _ _ (UntypedSynType _) with "Hv") as "(Hv' & Hv)".
    { split; first done. eapply syn_type_has_layout_make_untyped; done. }
    iApply ("HT" with "Hv Hv'").
  Qed.
  Definition value_subsume_goal_inst := [instance @value_subsume_goal].
  Global Existing Instance value_subsume_goal_inst | 50.
  *)

  (* TODO: this isn't ideal if v' is an evar -- then this currently will lead to evar instantiation failures, since we don't know the value yet.
     Maybe we want to have a type which encapsulates the existential quantifier in that case?
  *)
  Lemma owned_subltype_step_to_typed_value π E L step {rt} l v' st (ty : type rt) r T:
    (∀ v, v ◁ᵥ{π, MetaNone} r @ ty -∗
      owned_subltype_step π E L step l #v #v' (◁ value_t true (ty_syn_type ty MetaNone)) (◁ value_t true st) T)
    ⊢ owned_subltype_step π E L step l #r #v' (◁ ty) (◁ value_t true st) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "HT" (????) "#CTX #HE HL Hty".
    iMod (ofty_own_split_value_typed with "Hty") as "(%v & Hv & Hty)"; [done.. | ].
    iDestruct ("HT" with "Hv") as "HT".
    by iApply ("HT" with "[//] [//] [//] CTX HE HL").
  Qed.
  Lemma owned_subltype_step_to_untyped_value π E L step {rt} l v' st (ty : type rt) r T:
    (∀ v, v ◁ᵥ{π, MetaNone} r @ ty -∗
      owned_subltype_step π E L step l #v #v' (◁ value_t false (ty_syn_type ty MetaNone)) (◁ value_t false st) T)
    ⊢ owned_subltype_step π E L step l #r #v' (◁ ty) (◁ value_t false st) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "HT" (????) "#CTX #HE HL Hty".
    iMod (ofty_own_split_value_untyped with "Hty") as "(%v & Hv & Hty)"; [done.. | ].
    iDestruct ("HT" with "Hv") as "HT".
    by iApply ("HT" with "[//] [//] [//] CTX HE HL").
  Qed.

  (* TODO: check if needed or if falling down to [owned_subtype] is enough.
  (** When we require assembled ownership, try to assemble it. *)
  Lemma owned_subltype_step_merge_untyped_value {rt} π E L step (ty : type rt) `{!TySized ty} r v l st T :
    (prove_with_subtype E L step ProveDirect (v ◁ᵥ{π, MetaNone} r @ ty) True (λ L' _ R,
      li_tactic (compute_layout_goal (ty_syn_type ty MetaNone)) (λ ly,
        ⌜syn_type_has_layout st ly⌝ ∗ T L' R)))
    ⊢ owned_subltype_step π E L step l #v #r (◁ value_t false st) (◁ ty) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    rewrite /compute_layout_goal.
    iMod ("HT" $! _ True%I with "[//] [//] [//] CTX HE HL []") as "(%L' & % & %R & Hx & HL & %ly & %Hst & %Hst2 & HT)".
    { iApply maybe_logical_step_intro. done. }
    iExists _, _. iFrame.
    iModIntro. iApply (maybe_logical_step_compose with "Hx").
    iApply maybe_logical_step_intro.
    iIntros "(HR & Hv & _)".
    iPoseProof (ofty_own_merge_value_untyped with "Hv Hl") as "?"; last by iFrame.
    all: done.
  Qed.
  (* should have a lower priority than Lithium's id instance - in case the goal specifies that we want a value_t, we should not try to fiddle with that. *)
  (* also should be lower priority than the instance for going to uninit, [owned_subltype_step_ofty_uninit] *)
  Definition owned_subltype_step_merge_untyped_value_inst := [instance @owned_subltype_step_merge_untyped_value].
  Global Existing Instance owned_subltype_step_merge_untyped_value_inst | 200.

  Lemma owned_subltype_step_merge_typed_value {rt} π E L step (ty : type rt) `{!TySized ty} r v l st T :
    (prove_with_subtype E L false ProveDirect (v ◁ᵥ{π, MetaNone} r @ ty) True (λ L' _ R,
      ⌜ty_has_op_type ty (use_op_alg' (ty.(ty_syn_type) MetaNone)) MCCopy⌝ ∗
      ⌜ty_syn_type ty MetaNone = st⌝ ∗
      T L' R))
    ⊢ owned_subltype_step π E L step l #v #r (◁ value_t true st) (◁ ty) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl". iPoseProof (ltype_own_has_layout with "Hl") as "(%ly' & %Hst & %)".
    iMod ("HT" $! _ True%I with "[//] [//] [//] CTX HE HL []") as "(%L' & % & %R & >(HR & Hv & _) & HL & %Hc & %Ha & HT)".
    { iApply maybe_logical_step_intro. done. }
    iModIntro. iExists L', R. iFrame.
    iApply maybe_logical_step_intro. iFrame.
    subst st.
    iApply (ofty_own_merge_value_typed with "Hv Hl").
    done.
  Qed.
  (* should have a lower priority than Lithium's id instance - in case the goal specifies that we want a value_t, we should not try to fiddle with that. *)
  Definition owned_subltype_step_merge_typed_value_inst := [instance @owned_subltype_step_merge_typed_value].
  Global Existing Instance owned_subltype_step_merge_typed_value_inst | 201.
  *)

  Definition owned_subtype_value_id π E L step st r1 r2 typed := owned_subtype_id π E L step r1 r2 (value_t typed st).
  Definition owned_subtype_value_id_inst := [instance @owned_subtype_value_id].
  Global Existing Instance owned_subtype_value_id_inst | 10.

  Lemma owned_subtype_merge_typed_value {rt} π E L (ty : type rt) r v' st T :
    prove_with_subtype E L false ProveDirect (v' ◁ᵥ{π, MetaNone} r @ ty) True (λ L' _ R,
      introduce_with_hooks E L' R (λ L2,
      ⌜ty_has_op_type ty (use_op_alg' (ty.(ty_syn_type) MetaNone)) MCCopy⌝ ∗
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
  Global Existing Instance owned_subtype_merge_typed_value_inst | 100.

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
      eapply syn_type_size_eq_prove; done. }
    iSplitR; first by eauto.
    iIntros (v) "Hv".
    by iApply (own_val_merge_value_untyped with "Hv Hv'").
  Qed.
  (* shouldn't have super high priority because the conclusion is very general *)
  Definition owned_subtype_merge_untyped_value_inst := [instance @owned_subtype_merge_untyped_value].
  Global Existing Instance owned_subtype_merge_untyped_value_inst | 100.
End rules.

Section unify_loc.
  Context `{!typeGS Σ}.
  (** Strategy for unifying two values:
     Step 1 (equalize st):
     - if goal st is evar, instantiate with same and proceed to 2
     - if goal st is given:
       + if current is Untyped and goal is Untyped, go to step 2
       + if current is Untyped and goal is something else, make goal Untyped
       + otherwise, require equality (TODO: not complete: we could also make a prefix here)

     Invariant after step 2: either st match, or both are Untyped.

     Step 2
     - if both are untyped:
        a) if both are using the same layout, done
        b) if both have the same size, require the goal's alignment to be lower, done
        c) otherwise (size also not equal), require current to be a prefix and continue with prove_with_subtype of the rest (startign at step 1 again); require goal's alignment to be lower
     - otherwise: require the values to be the same.
   *)

  Lemma owned_subltype_step_ofty_value_unify_vs π E L step l vs1 vs2 typed st T :
    ⌜vs1 = vs2⌝ ∗ T L True%I
    ⊢ owned_subltype_step π E L step l #vs1 #vs2 (◁ value_t typed st) (◁ value_t typed st) T.
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
    owned_subltype_step π E L step l #vs1 #vs2 (◁ value_t typed1 st1) (◁ value_t typed2 st1) T
    ⊢ owned_subltype_step π E L step l #vs1 #vs2 (◁ value_t typed1 st1) (◁ value_t typed2 st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Definition owned_subltype_step_ofty_value_st_evar_inst := [instance @owned_subltype_step_ofty_value_st_evar].
  Global Existing Instance owned_subltype_step_ofty_value_st_evar_inst | 10.

  (* instantiate in case [typed2] is an evar *)
  Lemma owned_subltype_step_ofty_value_typed_evar π E L step l typed1 typed2 st1 st2 vs1 vs2 `{!IsProtected typed2} T :
    ⌜typed1 = typed2⌝ ∗
    owned_subltype_step π E L step l #vs1 #vs2 (◁ value_t typed1 st1) (◁ value_t typed1 st2) T
    ⊢ owned_subltype_step π E L step l #vs1 #vs2 (◁ value_t typed1 st1) (◁ value_t typed2 st2) T.
  Proof.
    iIntros "(-> & HT)". iApply "HT".
  Qed.
  Definition owned_subltype_step_ofty_value_typed_evar_inst := [instance @owned_subltype_step_ofty_value_typed_evar].
  Global Existing Instance owned_subltype_step_ofty_value_typed_evar_inst | 11.


  (* NOTE removed
  (* in case st1 is Untyped, make the goal untyped, too *)
  Lemma owned_subltype_step_ofty_value_st_untyped π E L step vs1 vs2 l st2 ly1 T :
    li_tactic (compute_layout_goal (UntypedSynType ly1)) (λ ly1',
    (li_tactic (compute_layout_goal st2) (λ ly2,
      owned_subltype_step π E L step l vs1 vs2 (◁ value_t (UntypedSynType ly1')) (◁ value_t (UntypedSynType ly2)) T)))
    ⊢ owned_subltype_step π E L step l vs1 vs2 (◁ value_t (UntypedSynType ly1)) (◁ value_t st2) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1' & %Hst1 & %ly2 & %Halg & HT)".
    iIntros (F ???) "#CTX #HE HL Hl".
    apply syn_type_has_layout_untyped_inv in Hst1 as (-> & ?).
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl") as "(%L' & %R2 & Hl & HL & HT)".
    iModIntro. iExists L', R2. iFrame.
    iApply (maybe_logical_step_wand with "[] Hl"). iIntros "(Hl & $)".
    iApply (ofty_mono_ly_strong with "[] [] Hl").
    - simpl. by eapply syn_type_has_layout_make_untyped.
    - done.
    - done.
    - done.
    - iIntros (v r) "Hv". rewrite /ty_own_val /=.
      iDestruct "Hv" as "(_ & %ot & %Heq & %Hmc & %Hv & _)".
      iR.
      injection Heq as <-. apply is_memcast_val_untyped_inv in Hmc as <-.
      specialize (syn_type_has_layout_op_alg _ _ Halg) as (ot & Hot & <-).
      iExists ot. iSplitR; first done. iSplitR. { by iLeft. }
      done.
    - simpl. done.
  Qed.
  Definition owned_subltype_step_ofty_value_st_untyped_inst := [instance @owned_subltype_step_ofty_value_st_untyped].
  Global Existing Instance owned_subltype_step_ofty_value_st_untyped_inst | 15.
  *)


  (** Step 2 *)

  (* if both are using the same st, unify the values *)

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

  Lemma owned_subltype_step_ofty_value_array π E L step l vs1 vs2 typed st1 st2 n1 n2  T :
    ⌜fast_eq_hint (st1 = st2)⌝ ∗ ⌜fast_lia_hint (n1 = n2)⌝ ∗
    ⌜vs1 = vs2⌝ ∗
    T L True%I
    ⊢ owned_subltype_step π E L step l vs1 vs2 (◁ value_t typed (ArraySynType st1 n1)) (◁ value_t typed (ArraySynType st2 n2)) T.
  Proof.
    iIntros "(<- & <- & <- & HT)".
    iIntros (????) "CTX HE ? ?".
    iFrame. iApply maybe_logical_step_intro.
    by iFrame.
  Qed.
  Definition owned_subltype_step_ofty_value_array_inst := [instance @owned_subltype_step_ofty_value_array].
  Global Existing Instance owned_subltype_step_ofty_value_array_inst | 15.


  (* if all of the above fail, require equality of the syntypes. *)
  (*
  Lemma owned_subltype_step_ofty_value_st_eq π E L step l vs1 vs2 typed1 typed2 st1 st2 T :
    ⌜fast_eq_hint (typed1 = typed2)⌝ ∗ ⌜st1 = st2⌝ ∗ owned_subltype_step π E L step l vs1 vs2 (◁ value_t typed2 st2) (◁ value_t typed2 st2) T
    ⊢ owned_subltype_step π E L step l vs1 vs2 (◁ value_t typed1 st1) (◁ value_t typed2 st2) T.
  Proof.
    iIntros "(-> & -> & $)".
  Qed.
  Definition owned_subltype_step_ofty_value_st_eq_inst := [instance @owned_subltype_step_ofty_value_st_eq].
  Global Existing Instance owned_subltype_step_ofty_value_st_eq_inst | 80.
  *)

  (* NOTE removed
  (* Prove a prefix of the goal, and continue finding the rest of the ownership *)
  Lemma owned_subltype_step_ofty_value_untyped_prefix π E L step l (vs1 vs2 : val) ly1 ly2 T `{!LayoutSizeLe ly1 ly2} :
    (⌜syn_type_has_layout (UntypedSynType ly2) ly2⌝ ∗
    (⌜l `has_layout_loc` ly1⌝ -∗
    ⌜l `has_layout_loc` ly2⌝ ∗
    ∃ vs2' : val, ⌜vs2 = vs1 ++ vs2'⌝ ∗
    ∃ ly1', prove_with_subtype E L step ProveDirect ((l +ₗ ly_size ly1) ◁ₗ[π, Owned] #vs2' @ ◁ value_t (UntypedSynType ly1')) True
        (λ L2 _ R2, ⌜ly_size ly1' = ly_size ly2 - ly_size ly1⌝ ∗ T L2 R2)))
    ⊢ owned_subltype_step π E L step l #vs1 #vs2 (◁ value_t (UntypedSynType ly1)) (◁ value_t (UntypedSynType ly2)) T.
  Proof.
    iIntros "(%Hst & HT)".
    match goal with H : LayoutSizeLe _ _ |- _ => rewrite /LayoutSizeLe in H end.
    iIntros (F ???) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Halg & %Hal)".
    apply syn_type_has_layout_untyped_inv in Halg as (-> & ? & ?).
    iDestruct ("HT" with "[//]") as "(%Hal2 & %vs2' & -> & %ly1' & HT)".
    iMod ("HT" $! _ True%I with "[//] [//] [//] CTX HE HL[] ") as "(%L' & % & %R2 & Hl' & HL & %Hsz & HT)".
    { iApply maybe_logical_step_intro. done. }
    iExists _, R2. iFrame.
    iApply maybe_logical_step_fupd.
    iApply (maybe_logical_step_compose with "Hl'").
    iApply maybe_logical_step_intro.
    iIntros "!> ($ & Hl' & _)".
    iPoseProof (ofty_value_untyped_app_merge with "Hl Hl'") as "$"; last done.
    - done.
    - done.
    - done.
    - done.
  Qed.
  Definition owned_subltype_step_ofty_value_untyped_prefix_inst := [instance @owned_subltype_step_ofty_value_untyped_prefix].
  Global Existing Instance owned_subltype_step_ofty_value_untyped_prefix_inst | 7.
  *)
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

  (* NOTE removed
  (* in case st1 is Untyped, make the goal untyped, too *)
  Lemma owned_subtype_value_st_untyped E L π vs1 vs2 st2 ly1 T :
    (li_tactic (compute_layout_goal (UntypedSynType ly1)) (λ ly1',
    (li_tactic (compute_layout_goal st2) (λ ly2,
      owned_subtype π E L false vs1 vs2 (value_t (UntypedSynType ly1')) (value_t (UntypedSynType ly2)) T))))
    ⊢ owned_subtype π E L false vs1 vs2 (value_t (UntypedSynType ly1)) (value_t st2) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1' & %Halg1 & %ly2 & %Halg2 & HT)".
    assert (Halg1' := Halg1).
    apply syn_type_has_layout_untyped_inv in Halg1 as (-> & ?).
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & Hsub & HL & HT)".
    iExists L2. iFrame. iModIntro.
    iDestruct "Hsub" as "(%Hsz & Hsc & Hv)".
    iSplitR "Hsc Hv".
    { iPureIntro. simpl in Hsz |- *.
      assert (Halg2' : syn_type_has_layout (UntypedSynType ly2) ly2).
      { eapply syn_type_has_layout_make_untyped; done. }
      eapply syn_type_size_eq_prove; [exact Halg1' | exact Halg2 | ].
      eapply syn_type_size_eq_use; [exact Hsz | exact Halg1' | exact Halg2']. }
    iSplitR "Hv".
    { iIntros "Hsc1". iApply "Hsc". done. }
    iIntros (v) "Hv1". iApply value_untyped_make_typed; first done.
    iApply "Hv". done.
  Qed.
  Definition owned_subtype_value_st_untyped_inst := [instance @owned_subtype_value_st_untyped].
  Global Existing Instance owned_subtype_value_st_untyped_inst | 15.
  *)


  (* TODO: one thing that definitely needs to work:
      value_t (UntypedOp ly) <: value_t st when st_has_layout st ly
   *)

  (** Step 2 *)
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
      - exact Halg1'.
      - exact Halg2'.
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

  (*
  (* if all of the above fail, require equality of the syntypes. TODO: this is too strict *)
  Lemma owned_subtype_value_st_eq E L π vs1 vs2 typed1 typed2 st1 st2 T :
    ⌜fast_eq_hint (typed1 = typed2)⌝ ∗ ⌜st1 = st2⌝ ∗ owned_subtype π E L false vs1 vs2 (value_t typed2 st2) (value_t typed2 st2) T
    ⊢ owned_subtype π E L false vs1 vs2 (value_t typed1 st1) (value_t typed2 st2) T.
  Proof.
    iIntros "(-> & -> & $)".
  Qed.
  Definition owned_subtype_value_st_eq_inst := [instance @owned_subtype_value_st_eq].
  Global Existing Instance owned_subtype_value_st_eq_inst | 80.
  *)
End unify_val.

Section rules.
  Context `{!typeGS Σ}.

  (* Read instance that leaves uninit on moves.
     TODO: Ideally, we would like to leave a value instead to not loose information.
      The lemmas below explore this, but currently do not work. *)
  Lemma type_read_ofty_move_owned E L {rt} π l (ty : type rt) r ot (T : typed_read_end_cont_t UpdStrong rt) :
    (⌜ty_has_op_type ty ot MCCopy⌝ ∗
      ∀ v, T L v _ ty r unit (◁ uninit (ty.(ty_syn_type) MetaNone)) (#()) (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned) UpdStrong ot ReadDoMove T.
  Proof.
    iIntros "(%Hot & Hs)" (F ????) "#CTX #HE HL Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly' & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    assert (ly' = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iR. iR.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv".
    iMod ("Hcl" $! v _ (uninit (ty.(ty_syn_type) MetaNone)) tt with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { iApply uninit_own_spec. iR. iExists _. iSplitR; first done. done. }
    iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.
    iModIntro.
    iSpecialize ("Hs" $! (mem_cast v ot st)).
    iFrame. done.
  Qed.
  Definition type_read_ofty_move_owned_inst := [instance @type_read_ofty_move_owned].
  Global Existing Instance type_read_ofty_move_owned_inst | 20.

  (* We also have a corresponding rule for Uniq ownership that leaves [Opened].
    This allows us to move out of mutable references, as long as another object is moved in at a later point. *)
  (* TODO also move value out here. *)
  Lemma type_read_ofty_move_uniq E L {rt} π l (ty : type rt) r ot κ γ (T : typed_read_end_cont_t UpdStrong rt)  :
    (li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
      ⌜ty_has_op_type ty ot MCCopy⌝ ∗
        ∀ v, T L2 v _ ty r unit
          (OpenedLtype (◁ uninit (ty.(ty_syn_type) MetaNone)) (◁ ty) (◁ ty) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs))
          (#())
          (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Uniq κ γ) UpdStrong ot ReadDoMove T.
  Proof.
    iIntros "HT" (F ????) "#CTX #HE HL Hb".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "HT" as (κs L2) "(%Hal & %Hot & HT)".

    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Hcl_tok & HL)"; [done.. | ].
    iPoseProof (ofty_ltype_acc_uniq with "CTX Htok Hcl_tok Hb") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iMod "Hcl_F" as "_".
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    do 2 iR.
    iApply (logical_step_mask_mono lftE); first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "[_ Hcl] %st Hl Hv".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod ("Hcl" $! v _ (uninit (ty.(ty_syn_type) MetaNone)) tt with "Hl [] [] [//]") as "Hl".
    { simpl. done. }
    { iApply uninit_own_spec. iR. iExists _. iSplitR; first done. done. }
    iPoseProof (ty_memcast_compat _ _ _ _ st with "Hv") as "Hid"; first done. simpl.
    iMod "Hcl_F" as "_".
    iModIntro.
    iSpecialize ("HT" $! (mem_cast v ot st)).
    iFrame. done.
  Qed.
  Definition type_read_ofty_move_uniq_inst := [instance @type_read_ofty_move_uniq].
  Global Existing Instance type_read_ofty_move_uniq_inst | 20.

  Lemma type_read_ofty_move_owned_value E L {rt} π l (ty : type rt) r ot (T : typed_read_end_cont_t UpdStrong rt) :
    (⌜use_op_alg (ty_syn_type ty MetaNone) = Some ot⌝ ∗
      (* TODO too strong, should also allow Untyped *)
      ⌜ty_has_op_type ty (use_op_alg' (ty_syn_type ty MetaNone)) MCCopy⌝ ∗
      ∀ v v', v ◁ᵥ{π, MetaNone} r @ ty -∗
      T L v' _ (value_t true (ty.(ty_syn_type) MetaNone)) v val
      (◁ value_t true (ty.(ty_syn_type) MetaNone)) (#v)
      (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned) UpdStrong ot ReadDoMove T.
  Proof.
    iIntros "(%Hotalg & %Hot & Hs)" (F ????) "#CTX #HE HL Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    specialize (ty_op_type_stable Hot) as Halg''.
    rewrite /use_op_alg' Hotalg in Halg''.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv".
    iPoseProof (own_val_split_value with "Hv") as "(#Hv1 & Hv)".
    { done. }
    iMod ("Hcl" $! v _ (value_t true (ty.(ty_syn_type) MetaNone)) (v) with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { done. }
    (*iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.*)
    iModIntro.

    iSpecialize ("Hs" with "Hv").
    iFrame.
    iPoseProof (ty_memcast_compat_copy _ _ _ ot _ _ st with "Hv1") as "Hv2".
    { rewrite ty_has_op_type_unfold. exists ot. split_and!; first done; last done. by apply is_value_ot_core_refl. }
    iR. done.
  Qed.
    (* TODO replace the preceding instances with this, once we have fixed:
      (a) owned_subtype to be able to move stuff into it again reliably, also below structs etc.
      (b) the model to allow syntype updates as long as the layout stays the same *)
  (*Definition type_read_ofty_move_owned_value_inst := [instance @type_read_ofty_move_owned_value].*)
  (*Global Existing Instance type_read_ofty_move_owned_value_inst | 19.*)


  (* TODO for Untyped, we currently cannot leave a value, because we cannot do syntype updates, but [value_t] relies on the syntype to compute the value update *)
  (*
  Lemma type_read_ofty_move_owned_untyped E L {rt} π  l (ty : type rt) r ly (T : typed_read_end_cont_t UpdStrong rt):
    ( ∀ v v', v ◁ᵥ{π, MetaNone} r @ ty -∗
      T L v' _ (value_t (UntypedSynType ly)) v val (◁ value_t (UntypedSynType ly)) (#v)
      (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)) -∗
      typed_read_end π E L l (◁ ty) (#r) (Owned) UpdStrong (UntypedOp ly) ReadDoMove T.
  Proof.
    iIntros "Hs" (F ????) "#CTX #HE HL".
    iIntros "Hb".
  Abort.
  *)

  (* Instead we leave uninit *)
  Lemma type_read_ofty_move_owned_value_untyped E L {rt} π l (ty : type rt) `{!TySized ty} r ly (T : typed_read_end_cont_t UpdStrong rt) :
    (⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
        ∀ v, T L v _ ty r unit (◁ uninit (ty.(ty_syn_type) MetaNone)) (#())
        (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))
    ⊢ typed_read_end π E L l (◁ ty) (#r) (Owned) UpdStrong (UntypedOp ly) ReadDoMove T.
  Proof.
    iIntros "(%Hst & Hs)" (F ????) "#CTX #HE HL Hb".
    iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly' & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iExists _, _, rt, _, _.
    iFrame "Hl Hv".
    iSplitR; first done. iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl %st Hl Hv". iMod ("Hcl" $! v _ (uninit (ty.(ty_syn_type) MetaNone)) tt with "Hl [//] [] []") as "Hl".
    { simpl. done. }
    { iApply uninit_own_spec. iR. iExists _. iSplitR; first done. done. }
    iPoseProof (ty_memcast_compat _ _ _ MCCopy with "Hv") as "Hid".
    { by eapply ty_sized_has_op_type_untyped. }
    simpl.
    iModIntro.
    iSpecialize ("Hs" $! (mem_cast v (UntypedOp ly) st)).
    iFrame. done.
  Qed.
  Definition type_read_ofty_move_owned_value_untyped_inst := [instance @type_read_ofty_move_owned_value_untyped].
  Global Existing Instance type_read_ofty_move_owned_value_untyped_inst | 20.

  (* TODO: this is now problematic. Maybe should have an untyped bit in the syntype after all?
       Alternative: use syn_type_compat everywhere to allow untyped interaction.

       Use an untyped bit:
       - then we still have a problem that often we should maybe be talking about a concrete layout instead.
          In particular when we assemble chunks.
          For array, we can work around that, since it is "chunkable", but for everything else, that does not really work.
          Q: do we reallyneed that for anything but arrays?
          + when we want to have a view on data and change the element type: e.g. in copy_nonoverlapping, would like to have an array of U8.
            We could in principle also do that for the ArraySynType, but it would be more of a hassle, and we would again end up with a different syntype
            OTOH is copy_nonoverlapping that much of a concern?
            In principle, we could also have something that first adapts
       - making things untyped would be much less of a hassle in the rules.

       Make rules compatible with UntypedSynType everywhere:
       - what is the intuitive justification for this? Why should we do it?
         + to my mind, UntypedSynType is just an undesirable artifact -- at least in safe Rust.
         + for unsafe stuff, the story may be different. We may want to treat stuff just as bytes.
            - allocation API itself should maybe treat it that way. We should just have some layout there.
              In our system, we will have a mixed concrete-symbolic layout.
              Arguably, that should not be a proper syntype, but that's how it is: our types need a syntype, and generally that requirement seems sensible.

       Alternative for this particular issue:
       - at the place, just don't leave an Untyped, but the right type. We should not loose information there!
         Then we also do not need a syntype update.

     *)

  (* TODO: consider whether we need special instances for reading/writing.
     In particular, what if we read with an ot from an UntypedOp-value? Then we should specialize the ot further in the result of the read.
     - problem currently: the generic ofty instance requires the type to have the same ot
     - but in case of value_t, we can change the ot!
   *)



  (* We also need stratification instances: should we generally move values back in during stratification?
    - One option: always cancel value_t in stratification.
        This limits expressivity a bit for specs, because when we really want to have value_t there, we get stuck.
      => do this for now, it should suffice.
     - Other option: have a (non-semantic) guidance parameter that gets provided by OpenedLtype.
       Only if that guidance parameter is not giving us identity do we fold the value_t.
     - Other option: do not let stratify do this, but rather have subtyping do this before folding.

     TODO: currently not an instance, because we sometimes do not want to do this!
     Instead, should give stratify some syntactic guidance from OpenedLtype above it.
   *)
   (*
  Lemma stratify_ltype_ofty_value_owned π E L mdu ma {M} (m : M) l st v (T : stratify_ltype_cont_t) :
    find_in_context (FindVal v) (λ '(existT rt (ty', r', π', m)),
      ⌜π' = π⌝ ∗ ⌜m = MetaNone⌝ ∗
      find_tc_inst (TySized ty') (λ _,
      ⌜ty_has_op_type ty' (use_op_alg' (ty'.(ty_syn_type) m)) MCCopy⌝ ∗
      ⌜ty'.(ty_syn_type) m = st⌝ ∗
      stratify_ltype π E L mdu ma m l (◁ ty') (#r') (Owned) T))
    ⊢ stratify_ltype π E L mdu ma m l (◁ value_t st)%I (#v) (Owned) T.
  Proof.
    iDestruct 1 as ([rt [[[ty' r'] π'] m']]) "(Hv & -> & -> & % & %Hot & %Heq & HT)" => /=.
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "#(%ly & %Hst &_)".
    iPoseProof (ofty_own_merge_value with "Hv Hl") as "Ha".
    { subst st. destruct (ty_syn_type ty'); try done.
      simp_ltypes in Hst. simpl in Hst.
      specialize (syn_type_has_layout_untyped_inv _ _ Hst) as (-> & _).
      done. }
    iMod ("HT" with "[//] [//] [//] CTX HE HL Ha") as "Ha".
    subst st. eauto.
  Qed.
  *)
  (* needs to have a higher priority than the ofty_resolve_ghost instance *)
  (*Global Instance stratify_ltype_unblock_ofty_value_owned_inst π E L mu mdu ma l st v wl :*)
    (*StratifyLtype π E L mu mdu ma StratifyUnblockOp l (◁ value_t st)%I (PlaceIn v) (Owned wl) | 10:=*)
    (*λ T, i2p (stratify_ltype_ofty_value_owned π E L mu mdu ma StratifyUnblockOp l st v wl T).*)
  (* TODO: not an instance right now since we don't always want to stratify this -- esp. not for functions passing values in their interface *)


  (* Simplification instance - when introducing a value_t, we simply destruct it *)
  (* TODO how does this overlap with ghost_drop?
     TODO can we simplify the is_memcast_val? Otherwise, it seems pretty useless. *)
  (*
  Lemma value_simplify π v T ot st p :
    (⌜is_memcast_val p ot v⌝ -∗ ⌜v `has_layout_val` ot_layout ot⌝ -∗ ⌜syn_type_has_layout st (ot_layout ot)⌝ -∗ T) -∗
    simplify_hyp (v ◁ᵥ{π} p @ value_t st)%I T.
  Proof. iIntros "HT (% & % & %)". by iApply "HT". Qed.
  Global Instance value_simplify_inst π v ot st p :
    SimplifyHypVal v π (value_t ot st) p (Some 0%N) :=
    λ T, i2p (value_simplify π v T ot st p).
   *)



End rules.

Global Typeclasses Opaque value_t.
Global Hint Unfold value_t : tyunfold.
