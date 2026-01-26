From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.hillel.generated Require Import generated_code_hillel generated_specs_hillel generated_template_insert_unique.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma insert_unique_proof (π : thread_id) :
  insert_unique_lemma π.
Proof.
  insert_unique_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(unique) *)
  all: try set_solver.
  rewrite app_Permutation_comm. econstructor; done.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
