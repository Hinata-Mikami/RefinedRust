From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_collect.

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

Lemma Heap_collect_proof (π : thread_id) :
  Heap_collect_lemma π.
Proof.
  Heap_collect_prelude.

  1: rep <-! <3000 liRStep.
  liShow.

  (* Open the Heap returned by mark before transferring its structure
     and node resources to the permissive sweep receiver. *)
  iRename select (l'0 ◁ₗ[_, _] _ @ _)%I into "Hheap".
  apply_update updateable_add_fupd.
  iMod (ex_plain_t_destruct_owned with "Hheap")
    as (r) "(Hinv & Hheap)"; first done.
  iDestruct "Hinv" as
    "(%Hr & %Hlen_locs & %Hlen_nexts & %Hlen_marks & %Hnext_valid &
      Hnodes & %Hnodup_locs & %Hnot_null & _)".
  subst r.
  iModIntro.

  1: rep <-! <3000 liRStep.
  liInst Hevar_x1 h.
  liInst Hevar_x0 h1.
  liInst Hevar_x3 x'.
  1: rep <-! <3000 liRStep.
  liShow.

  (* Rebuild the Heap invariant from sweep's actual post-call ownership.
     This connects the filtered lists to the mutable Heap, including
     the reset mark bits and all retained node/freeable resources. *)
  iRename select (l'0 ◁ₗ[_, _] _ @ _)%I into "Hheap".
  iRename select
    ([∗ list] i ↦ v ∈ (keep_marked h x'),
      ∃ (l n : loc) (m : bool), _)%I into "Hnodes".
  iAssert
    (l'0 ◁ₗ[π, Owned]
      #(keep_marked h x', keep_marked h0 x', keep_marked h1 x',
        replicate (length (keep_marked h0 x')) false)
      @ ◁ (Heap_inv_t -[] -[]))%I
    with "[Hheap Hnodes]" as "Hheap".
  {
    iApply ltype_own_ex_plain_t_intro.
    iExists (-[#(<#> (keep_marked h0 x'))]).
    iFrame "Hheap Hnodes".
    repeat iSplit; try done.
    iPureIntro. unfold name_hint. rewrite length_replicate. assumption.
  }

  1: rep <-! <3000 liRStep.
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  {
    rename select
      (marking_exact _ _ _ → sweep_reachable_exact _ _ _) into Hsweep_exact.
    symmetry.
    apply Hsweep_exact. unfold marking_exact. assumption.
  }
  {
    rename select
      (_ !! 0%nat = Some true → sweep_reachability_preserved _ _ _ _)
      into Hsweep_preserves.
    apply Hsweep_preserves.
    eapply mark_from_rel_marks_start; eassumption.
  }
  { apply sweep_reset_all_unmarked. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
