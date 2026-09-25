From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_sweep.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Heap_sweep_proof (π : thread_id) :
  Heap_sweep_lemma π.
Proof.
  Heap_sweep_prelude.

  rep <-! liRStep; liShow.

  {
    iRename select
      ([∗ list] i ↦ v ∈ vals,
        ∃ (l n : loc) (m : bool), _)%I
      into "Hnodes".

    set (idx := Z.to_nat (ic - 1)).

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

    - iRename select
      ((locs !!! idx) ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".

      set (P := fun (k : nat) (y : Z) =>
        (∃ (l0 n : loc) (m : bool),
          ⌜locs !! k = Some l0⌝ ∗
          ⌜nexts !! k = Some n⌝ ∗
          ⌜marks !! k = Some m⌝ ∗
          guarded true
            (l0 ◁ₗ[π, Owned]
              # -[# y; # n; # m]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l0
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc)%I).

      iSpecialize ("Hclose" $! P).

      iSpecialize ("Hclose" with "[]").
      {
        iModIntro.
        iIntros (k y) "%Hlookup %Hneq HP".
        unfold P.
        iExact "HP".
      }

      iAcquireCredits as "Hcred".

      iRevert "Hnode Hfree Hclose".

      rep liRStep; liShow.

      iRename select
        (P idx vi -∗ [∗ list] k ↦ y ∈ vals, P k y)%I
        into "Hclose".

      iRename select
        ((locs !!! idx) ◁ₗ[_, Owned] _ @ _)%I
        into "Hnode".

      iRename select
        (freeable_nz (locs !!! idx) _ 1 HeapAlloc)%I
        into "Hfree".

      iApply
      (prove_with_subtype_big_sepL_acc
        _ _ _ _ vals P idx vi _
        with "Hclose").

      unfold P.
      rep liRStep; liShow.

      iApply prove_with_subtype_default.


(* 
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

    - iRename select
      ((locs !!! idx) ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".

      iAcquireCredits as "Hcred".

      iRevert "Hnode Hfree Hclose".

      rep <-! liRStep; liShow.

      rep liRStep; liShow.

      iRename select
        ((locs !!! idx) ◁ₗ[_, Owned] _ @ _)%I
        into "Hnode".

      iRename select
        (freeable_nz (locs !!! idx) _ 1 HeapAlloc)%I
        into "Hfree".

      iRename select
        (∀ Ψ : nat → Z → iPropI Σ, _)%I
        into "Hclose".

      set (P := fun (k : nat) (y : Z) =>
      (∃ (l0 n : loc) (m : bool),
        ⌜locs !! k = Some l0⌝ ∗
        ⌜nexts !! k = Some n⌝ ∗
        ⌜marks !! k = Some m⌝ ∗
        guarded true
          (l0 ◁ₗ[π, Owned]
            # -[# y; # n; # m]
            @ (◁ (Node_ty <INST!>))) ∗
        freeable_nz l0
          (ly_size (use_layout_alg' Node_sls))
          1 HeapAlloc)%I).

      iSpecialize ("Hclose" $! P).

      iSpecialize ("Hclose" with "[]").
      {
        iModIntro.
        iIntros (k y) "%Hlookup %Hneq HP".
        unfold P.
        iExact "HP".
      }

      iApply
      (prove_with_subtype_big_sepL_acc
        _ _ _ _ vals P idx vi _
        with "Hclose").

      unfold P.

      rep liRStep; liShow. *)

    
  }
  {

  }


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
