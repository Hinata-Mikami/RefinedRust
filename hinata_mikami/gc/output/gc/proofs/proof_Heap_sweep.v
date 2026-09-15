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
  (* Goal 1 *)
  {
    iRename select
    ([∗ list] k ↦ x ∈ (id <$> h),
      ∃ (l0 n : loc) (m : bool), _)%I
    into "Hnodes".

    assert (Hmap_vals : (id <$> h) = h).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_locs : (id <$> h0) = h0).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_nexts : (id <$> h1) = h1).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_marks : (id <$> h2) = h2).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    iEval (
      rewrite Hmap_vals
              Hmap_locs
              Hmap_nexts
              Hmap_marks
    ) in "Hnodes".


    assert (H0_vals : (0 < length h)%nat) by lia.

    destruct
      (lookup_lt_is_Some_2 h 0%nat H0_vals)
      as [vi Hvi].

    iDestruct
      (big_sepL_lookup_acc_impl
        0%nat vi Hvi
        with "Hnodes")
      as "(HiNode & Hclose)".

    iDestruct "HiNode" as
      (node_l next0 mark0)
      "(%Hloc0 & %Hnext0 & %Hmark0 &
        Hguard & Hfree)".

    assert (Hloc_total :
      h0 !! 0%nat = Some (h0 !!! 0%nat)).
    {
      apply list_lookup_lookup_total_lt.
      lia.
    }

    assert (node_l = h0 !!! 0%nat) as Heq_node.
    {
      rewrite Hloc0 in Hloc_total.
      injection Hloc_total as Heq_node.
      exact Heq_node.
    }

    subst node_l.

    apply_update updateable_strip_guards.

    rep <-! liRStep; liShow.

    - iRename select
      ((h0 !!! Z.to_nat 0) ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".

      iAcquireCredits as "Hcred".

      iRevert "Hnode Hfree Hclose".

      rep <-! liRStep; liShow.

      rep liRStep; liShow.

      iRename select
      ((h0 !!! Z.to_nat 0) ◁ₗ[π, Owned] _ @ _)%I
      into "Hnode".

      iRename select
        (freeable_nz (h0 !!! 0%nat)
          (ly_size (use_layout_alg' Node_sls))
          1 HeapAlloc)%I
        into "Hfree".

      iRename select
        (∀ Ψ : nat → Z → iPropI Σ, _)%I
        into "Hclose".

      set (P := fun (k : nat) (y : Z) =>
      (∃ (l0 n : loc) (m : bool),
        ⌜h0 !! k = Some l0⌝ ∗
        ⌜h1 !! k = Some n⌝ ∗
        ⌜h2 !! k = Some m⌝ ∗
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

      iRevert "Hnode Hfree Hclose".
      iIntros "Hnode Hfree Hclose".

      rep liRStep; liShow.

      iApply
        (prove_with_subtype_big_sepL_acc
          _ _ _ _ h P 0%nat vi _
          with "Hclose").

      unfold P.

      rep liRStep; liShow.
      

    

  }
  (* Goal 2 *)
  {

  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
