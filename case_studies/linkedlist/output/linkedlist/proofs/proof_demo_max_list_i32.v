From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_demo_max_list_i32.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* Auto-generated proof skeleton *)
Lemma demo_max_list_i32_proof (π : thread_id) :
  demo_max_list_i32_lemma π.
Proof.
  (* Function-specific proof prelude *)
  demo_max_list_i32_prelude.

  (* Run RefinedRust's type checker *)
  rep <-! liRStep; liShow.

  (* Run RefinedRust's sidecondition solvers *)
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* Manually inserted proof *)
  (* Changes to the proof script are persistent *)
  all: unsafe_unfold_common_radium_defs; simpl; lia.

  (* Cleanup *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
