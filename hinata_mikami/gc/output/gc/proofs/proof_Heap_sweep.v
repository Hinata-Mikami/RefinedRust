From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_sweep.
From hinata_mikami.extra_proofs.gc Require Import heap_lemmas.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Local Lemma prove_with_subtype_stratify_opened
    l E L pm Q T :
  find_in_context (FindLoc l)
    (λ '(existT rt (lt, r, bk, π)),
      stratify_ltype
        π E L
        StratMutNone
        StratNoUnfold
        StratRefoldOpened
        StratifyUnblockOp
        l lt r bk
        (λ L2 R rt' lt' r',
          prove_with_subtype E L2 true pm
            (l ◁ₗ[π, bk] r' @ lt' -∗
             R -∗
             Q)
            T))
  ⊢ prove_with_subtype E L true pm Q T.
Proof.
  unfold find_in_context, FindLoc.
  simpl.

  iIntros "(%x & Ha)".
  destruct x as [rt (((lt & r) & bk) & π)].
  iDestruct "Ha" as "(Hl & HT)".

  rewrite /prove_with_subtype.
  iIntros (F ???) "#CTX #HE HL".

  rewrite /stratify_ltype.
  iMod ("HT" with "[//] [//] [//] CTX HE HL Hl")
    as "(%L2 & %R & %rt' & %lt' & %r' &
         HL & %Hst' & Hstep & HT)".

  iMod ("HT" with "[//] [//] [//] CTX HE HL")
    as "(%L3 & %κs2 & %R' &
         Hstep' & HL & HT)".

  simpl.
  iFrame.

  iApply logical_step_fupd.
  iApply (logical_step_compose with "Hstep").
  iApply (logical_step_wand with "Hstep'").

  iModIntro.
  iIntros "(Ha & $) (Hl & HR)".

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
      (typed_stmt _ _ _ (Goto "_bb2") _ _ _) =>
      fail
  | _ =>
      liRStep
  end;
  liShow.


Lemma Heap_sweep_proof (π : thread_id) :
  Heap_sweep_lemma π.
Proof.
  Heap_sweep_prelude.

  liRStepUntilBb2.

  set (Φ :=
  fun (k : nat) (v : Z)
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
    iEval (rewrite /sweep_nodes_inv /aligned_nodes) in "Hsweep".
    rewrite Hcut.

    assert (Hkeep_vals :
      keep_marked_suffix (length marks) vals marks =
      take (length marks) vals).
    {
      unfold keep_marked_suffix.

      rewrite drop_ge.
      2: lia.

      rewrite drop_ge.
      2: lia.

      simpl.

      
    }
  }


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
