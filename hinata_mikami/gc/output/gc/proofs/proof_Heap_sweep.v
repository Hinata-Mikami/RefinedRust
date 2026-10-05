From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_sweep.

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



Lemma Heap_sweep_proof (π : thread_id) :
  Heap_sweep_lemma π.
Proof.
  Heap_sweep_prelude.

  rep <-! liRStep; liShow.

  -
    iRename select
      ([∗ list] i ↦ v ∈ vals,
        ∃ (l n : loc) (m : bool), _)%I
      into "Hnodes".

    set (idx := Z.to_nat (length locs - 1)).

    assert (Hidx_locs : (idx < length locs)%nat).
    {
      unfold idx.
      lia.
    }

    assert (Hidx_vals : (idx < length vals)%nat).
    {
      rewrite <- H9.
      exact Hidx_locs.
    }

    destruct
      (lookup_lt_is_Some_2 vals idx Hidx_vals)
      as [vi Hvi].

    iDestruct
      (big_sepL_lookup_acc_impl
        idx vi Hvi
        with "Hnodes")
      as "(HiNode & Hclose)".

    iDestruct "HiNode" as
      (node_l next_i mark_i)
      "(%Hloc_i & %Hnext_i & %Hmark_i &
        Hguard & Hfree)".

    assert (Hloc_total :
      locs !! idx = Some (locs !!! idx)).
    {
      apply list_lookup_lookup_total_lt.
      exact Hidx_locs.
    }

    assert (node_l = locs !!! idx) as Heq_node.
    {
      rewrite Hloc_i in Hloc_total.
      injection Hloc_total as Heq_node.
      exact Heq_node.
    }

    subst node_l.

    apply_update updateable_strip_guards.

    rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
