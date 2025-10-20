From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_RawVec_T_grow.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma RawVec_T_grow_proof (π : thread_id) :
  RawVec_T_grow_lemma π.
Proof.
  RawVec_T_grow_prelude.

  rep <-! liRStep.
  (* Manual step to extract the array value before the call to realloc *)
  apply_update (updateable_extract_value l).
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unfold size_of_array_in_bytes in *. simplify_layout_assum. nia. }
  {
    revert select (ly_size (mk_array_layout _ _) ≤ _).
    move: Hnot_sz.
    match goal with H : 2 * MaxInt ISize < MaxInt USize |- _ => move: H end.
    rewrite ly_size_mk_array_layout.
    clear. solve_goal with nia.
  }
  {
    revert select (ly_size (mk_array_layout _ _) ≤ _).
    move: Hnot_sz.
    match goal with H : 2 * MaxInt ISize < MaxInt USize |- _ => move: H end.
    rewrite ly_size_mk_array_layout.
    solve_goal with nia.
  }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
