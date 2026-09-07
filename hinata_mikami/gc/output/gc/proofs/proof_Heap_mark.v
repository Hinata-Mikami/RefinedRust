From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_mark.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Heap_mark_proof (π : thread_id) :
  Heap_mark_lemma π.
Proof.
  Heap_mark_prelude.

  rep <-! liRStep; liShow.

  rep liRStep; liShow.

  liInst Hevar_x1 h.
  liInst Hevar_x0 h1.
  liInst Hevar_x3 h2.

  rep liRStep; liShow.

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

  iApply prove_with_subtype_default.

  iSplitL "Hnodes".
  {
    iExact "Hnodes".
  }

  rep liRStep; liShow.

  liInst Hevar_x5 0%nat.

  rep liRStep; liShow.

  
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
