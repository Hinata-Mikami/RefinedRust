From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_mark.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* Avoid the admitted Vec ghost resolvers in the upstream specifications.
   These functions carry concrete element refinements and need no resolution. *)
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
  {
    eapply mark_from_rel_final_closed_unmarked; eassumption.
  }
  {
    eapply (mark_from_rel_exact_root h0 h1 h2 x'); eassumption.
  }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
