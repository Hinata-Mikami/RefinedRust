From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_alignment_Alignment_as_usize.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma alignment_Alignment_as_usize_proof (π : thread_id) :
  alignment_Alignment_as_usize_lemma π.
Proof.
  alignment_Alignment_as_usize_prelude.

  assert (ty_has_op_type (enum_t (alignment_AlignmentEnum_enum -[] -[])) (use_op_alg' alignment_AlignmentEnum_els)).
  { solve_ty_has_op_type. }

  (* opaque because we are working with big terms here *)
  Opaque alignment_AlignmentEnum_els.

  rep liRStep.
  Transparent alignment_AlignmentEnum_els.
  liRStep.
  Opaque alignment_AlignmentEnum_els.
  (* otherwise, [solve_goal] will take a long time to fail when the rewrite with [wrap_to_it_id] tries to apply *)
  rewrite int_elem_of_u64_usize.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve.
  destruct self.
  all: vm_compute; reflexivity.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
