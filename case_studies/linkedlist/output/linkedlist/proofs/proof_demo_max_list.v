From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_demo_max_list.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* Auto-generated proof skeleton *)
Lemma demo_max_list_proof (π : thread_id) :
  demo_max_list_lemma π.
Proof.
  (* Function-specific proof prelude *)
  demo_max_list_prelude.

  (* Run RefinedRust's type checker *)
  rep <-! liRStep; liShow.

  (* Run RefinedRust's sidecondition solvers *)
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* Manually inserted proof *)
  (* Changes to the proof script are persistent *)
  { case_bool_decide as Heq; revert Heq; normalize_and_simpl_goal.
    { rewrite max_list_cmp_app/= max_by_r_1; solve_goal. }
    { rewrite max_list_cmp_app/= max_by_l_1; solve_goal. } }

  (* Cleanup *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
