From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_sweep.
From hinata_mikami.extra_proofs.gc Require Import heap_lemmas sweep_contract.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* The Vec-specific resolvers in stdlib/vec/extra_specs.v are admitted.
   Sweep only carries concrete pointer lists, so use the proved generic
   ghost-resolution rules instead. This changes automation, not obligations. *)
#[local] Remove Hints
  generated_specs_vec.resolve_ghost_Vec_T_owned_inst
  generated_specs_vec.resolve_ghost_Vec_T_uniq_inst : typeclass_instances.

Local Lemma resolve_ghost_Vec_concrete
    {T_rt : RT} (T_ty : type T_rt) {A_rt : RT} (A_ty : type A_rt)
    A_attrs π E L rm lb l bk rs T :
  T L (#rs) True false ⊢
  resolve_ghost π E L rm lb l
    (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>)) bk (#rs) T.
Proof. apply resolve_ghost_ofty_default. Qed.
Local Definition resolve_ghost_Vec_concrete_inst :=
  [instance @resolve_ghost_Vec_concrete].
Local Existing Instance resolve_ghost_Vec_concrete_inst | 1.

Local Lemma prove_with_subtype_stratify_opened
    l E L pm Q A T :
  find_in_context (FindLoc l)
    (λ '(existT rt (lt, r, bk, π)),
      stratify_ltype
        π E L
        StratNoUnfold
        StratRefoldOpened
        StratifyUnblockOp
        l lt r bk
        (λ L2 R rt' lt' r',
          prove_with_subtype E L2 true pm
            (l ◁ₗ[π, bk] r' @ lt' -∗
             R -∗
             Q)
            A T))
  ⊢ prove_with_subtype E L true pm Q A T.
Proof.
  unfold find_in_context, FindLoc.
  simpl.

  iIntros "(%x & Ha)".
  destruct x as [rt (((lt & r) & bk) & π)].
  iDestruct "Ha" as "(Hl & HT)".

  rewrite /prove_with_subtype.
  iIntros (F Acc' ???) "#CTX #HE HL HA".

  rewrite /stratify_ltype.
  iMod ("HT" with "[//] [//] [//] CTX HE HL Hl")
    as "(%L2 & %R & %rt' & %lt' & %r' &
         HL & %Hst' & Hstep & HT)".

  iMod ("HT" with "[//] [//] [//] CTX HE HL HA")
    as "(%L3 & %κs2 & %R' &
         Hstep' & HL & HT)".

  simpl.
  iFrame.

  iApply logical_step_fupd.
  iApply (logical_step_compose with "Hstep").
  iApply (logical_step_wand with "Hstep'").

  iModIntro.
  iIntros "($ & Ha & $) (Hl & HR)".

  destruct pm.
  - iApply ("Ha" with "[$] [$]").

  - iModIntro.
    iIntros "Hdead".
    iMod ("Ha" with "Hdead") as "Ha".
    iModIntro.
    iApply ("Ha" with "[$] [$]").
Qed.

Ltac liRStepUntilBb2 :=
  repeat lazymatch goal with
  | |- environments.envs_entails _
      (typed_stmt _ _ _ (Goto "_bb2") _ _ _ _) =>
      fail
  | _ =>
      liRStep
  end;
  liShow.

Local Lemma keep_marked_suffix_pred_true {A} cut (xs : list A) marks :
  (0 < cut)%nat → length xs = length marks →
  marks !! (cut - 1)%nat = Some true →
  keep_marked_suffix cut xs marks = keep_marked_suffix (cut - 1) xs marks.
Proof.
  destruct cut as [|cut]; intros Hpos Hlen Hmark; first lia.
  replace (S cut - 1)%nat with cut in * by lia.
  by apply keep_marked_suffix_step_true.
Qed.

Local Lemma keep_marked_suffix_pred_false {A} cut (xs : list A) marks :
  (0 < cut)%nat → length xs = length marks →
  marks !! (cut - 1)%nat = Some false →
  delete (cut - 1)%nat (keep_marked_suffix cut xs marks) =
    keep_marked_suffix (cut - 1) xs marks.
Proof.
  destruct cut as [|cut]; intros Hpos Hlen Hmark; first lia.
  replace (S cut - 1)%nat with cut in * by lia.
  by apply keep_marked_suffix_step_false.
Qed.


Lemma Heap_sweep_proof (π : thread_id) :
  Heap_sweep_lemma π.
Proof.
  Heap_sweep_prelude.

  liRStepUntilBb2.

  set (Φ :=
  fun (v : Z)
      (l n : loc) (m : bool) =>
    (guarded true
       (l ◁ₗ[π, Owned]
          # -[#v; #n; #m]
          @ (◁ struct_t Node_sls
               +[int i32; alias_ptr_t; bool_t])) ∗
     freeable_nz l
       (ly_size (use_layout_alg' Node_sls))
       1 HeapAlloc)%I).
  iRename select
    ([∗ list] i ↦ v ∈ vals,
      ∃ (l n : loc) (m : bool), _)%I
    into "Hnodes".
    iAssert
    (aligned_nodes vals locs nexts marks Φ)%I
    with "[Hnodes]"
    as "Hnodes_aligned".
  {
    unfold aligned_nodes.
    unfold Φ.
    iExact "Hnodes".
  }

  assert (Hvals_marks :
    length vals = length marks).
  {
    lia.
  }

  assert (Hlocs_marks :
    length locs = length marks).
  {
    lia.
  }

  assert (Hnexts_marks :
    length nexts = length marks).
  {
    lia.
  }

  iPoseProof
    (sweep_nodes_inv_init
      vals locs nexts marks Φ
      Hvals_marks
      Hlocs_marks
      Hnexts_marks
      with "Hnodes_aligned")
    as "Hsweep".

  let_bind_envs.
  liRStep.
  liShow.

  rep liRStep; liShow.
  assert (Hcut :
    Z.to_nat (Z.of_nat (length locs)) = length marks).
  {
    rewrite Nat2Z.id.
    exact Hlocs_marks.
  }

  iApply prove_with_subtype_default.
  iSplitL "Hsweep".
  {
    rewrite Hcut.
    assert (Hkeep_vals :
      keep_marked_suffix (length marks) vals marks =
      take (length marks) vals).
    {
      unfold keep_marked_suffix.
      rewrite (drop_ge vals); last lia.
      simpl. apply app_nil_r.
    }
    rewrite -Hkeep_vals.
    iExact "Hsweep".
  }

  rewrite Hcut (drop_ge vals); last lia.
  rep <-! liRStep; liShow.
  - iRename select (sweep_nodes_inv _ _ _ _ _ _) into "Hinv".
    have Hpos : (0 < Z.to_nat ic)%nat by lia.
    have Hbound : (Z.to_nat ic ≤ length marks)%nat by lia.
    iDestruct (sweep_nodes_inv_step (Z.to_nat ic) vals locs nexts marks
      _ Hpos Hbound Hvals_marks Hlocs_marks Hnexts_marks with "Hinv")
      as (vc lc nc mc) "(%Hvc & %Hlc & %Hnc & %Hmc & Hnode & Hclose)".
    (* Use the same natural-number index for Vec lookup and node ownership. *)
    have Hindex : (Z.to_nat ic - 1 = Z.to_nat (ic - 1))%nat by lia.
    have Hactual : keep_marked_suffix (Z.to_nat ic) locs marks !!
        (Z.to_nat ic - 1)%nat = Some lc.
    {
      rewrite /keep_marked_suffix lookup_app_l.
      - rewrite lookup_take_lt; [exact Hlc|lia].
      - rewrite length_take. lia.
    }
    have Hptr : keep_marked_suffix (Z.to_nat ic) locs marks !!!
        (Z.to_nat ic - 1)%nat = lc.
    { apply list_lookup_total_correct. exact Hactual. }
    have Hnonnull : loc_a lc ≠ 0.
    {
      have Hnonall : Forall (λ l : loc, loc_a l ≠ 0) locs by assumption.
      exact ((proj1 (Forall_lookup (λ l : loc, loc_a l ≠ 0) locs) Hnonall)
        _ _ Hlc).
    }
    rewrite -Hindex Hptr.
    iDestruct "Hnode" as "[Hguard Hfree]".
    apply_update updateable_strip_guards.
    rep liRStep; liShow.
    + iRename select
        ((keep_marked_suffix (Z.to_nat ic) locs marks !!!
          (Z.to_nat ic - 1)%nat) ◁ₗ[_, Owned] _ @ _)%I into "Hnew".
      (* Return the reset node to the invariant with a prepaid guard. *)
      iAcquireCredits as "Hcred".
      iPoseProof ("Hclose" with "[Hnew Hfree Hcred]") as "Hnewinv".
      { iFrame "Hfree". iApply guarded_intro. iFrame. }
      try rewrite -Hindex.
      iEval (rewrite /sweep_nodes_inv /aligned_nodes /keep_marked_suffix
        big_sepL_app) in "Hnewinv".
      iDestruct "Hnewinv" as "[Hprefix Hsuffix]".
      iApply prove_with_subtype_default.
      iSplitL "Hprefix"; first by iExact "Hprefix".
      rep liRStep; liShow.
    + rep liRStep; liShow.
      (* Normalize deletion through the Vec element refinement map. *)
      have Hkeep_false :
        delete (Z.to_nat ic - 1)%nat
          (keep_marked_suffix (Z.to_nat ic) locs marks) =
        keep_marked_suffix (Z.to_nat ic - 1) locs marks.
      { apply keep_marked_suffix_pred_false; [lia|lia|exact Hmc]. }
      try rewrite -Hindex.
      try rewrite -!list_fmap_delete.
      try rewrite Hkeep_false.
      iEval (rewrite /sweep_nodes_inv /aligned_nodes /keep_marked_suffix
        big_sepL_app) in "Hclose".
      iDestruct "Hclose" as "[Hprefix Hsuffix]".
      rep liRStep; liShow.
  - (* Checked usize subtraction: the overflow path contradicts the bounds. *)
    exfalso.
    match goal with Hoverflow : ic - 1 ∉ usize |- _ => apply Hoverflow end.
    change (MinInt usize ≤ ic - 1 ≤ MaxInt usize)%Z.
    rewrite MinInt_eq /min_int /=. lia.
  - have Hzero : ic = 0 by lia. subst ic.
    iRename select (sweep_nodes_inv _ _ _ _ _ _) into "Hinv".
    iPoseProof (sweep_nodes_inv_done vals locs nexts marks _
      Hvals_marks Hlocs_marks Hnexts_marks with "Hinv") as "Hdone".
    rep liRStep; liShow.

  (* Discharge the pure arithmetic, filtering, and pointer-validity obligations. *)
  Unshelve. all: sidecond_solver.
  all: sidecond_hammer_normalize.
  all: try lia.
  all: try (rewrite keep_marked_suffix_length; done).
  all: try (rewrite /keep_marked_suffix length_app length_take_le; lia).
  all: try (apply keep_marked_length_same_mask; lia).
  all: try (apply keep_marked_NoDup; assumption).
  all: try (apply keep_marked_Forall; assumption).
  all: try (eapply marks_closed_keep_marked_next_valid;
    [lia|assumption|assumption|assumption]).
  all: try (eapply sweep_post_filter; [assumption|lia|lia|assumption]).
  all: try (apply sweep_kept_exact_filter; assumption).
  all: try (apply sweep_reachable_exact_filter; assumption).
  all: try (eapply sweep_preserves_reachability;
    [assumption|lia|lia|assumption|assumption]).
  all: try (apply sweep_fields_preserved_filter; assumption).
  all: try (apply sweep_reset_all_unmarked).
  all: try rewrite -list_fmap_delete.
  all: try (
    match goal with
    | Hm : ?ms !! (?cut - 1)%nat = Some true |- _ =>
      let Heq := fresh "Hkeep" in
      assert (Heq : keep_marked_suffix cut locs ms =
        keep_marked_suffix (cut - 1) locs ms) by
        (apply keep_marked_suffix_pred_true; [lia|lia|exact Hm]);
      rewrite Heq; done
    end).
  all: try (
    match goal with
    | Hm : ?ms !! (?cut - 1)%nat = Some false |- _ =>
      let Heq := fresh "Hkeep" in
      assert (Heq : delete (cut - 1)%nat (keep_marked_suffix cut locs ms) =
        keep_marked_suffix (cut - 1) locs ms) by
        (apply keep_marked_suffix_pred_false; [lia|lia|exact Hm]);
      rewrite Heq; done
    end).
  all: try (apply (elem_of_int_type_0_to_127 _ usize); lia).
  Unshelve. all: done.
Time Qed.
End proof.
