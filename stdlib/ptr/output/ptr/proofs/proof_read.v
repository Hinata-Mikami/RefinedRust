From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From stdlib.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_read.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma read_proof (π : thread_id) :
  read_lemma π.
Proof.
  read_prelude.

  destruct k.
  { liRStepUntil (typed_read_end).
    (* locally override the instance used for moves *)
    (*iApply type_read_ofty_move_owned_value.*)
    (*liFromSyntax.*)
    repeat liRStep; liShow.
  }
  { repeat liRStep; liShow. }
  { repeat liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
