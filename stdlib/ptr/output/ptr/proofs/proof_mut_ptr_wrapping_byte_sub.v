From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_mut_ptr_wrapping_byte_sub.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma mut_ptr_wrapping_byte_sub_proof (π : thread_id) :
  mut_ptr_wrapping_byte_sub_lemma π.
Proof.
  mut_ptr_wrapping_byte_sub_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite /WrappingOffsetLocSt/wrapping_offset_loc. 
    simplify_layout_goal. all: sidecond_hammer. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
