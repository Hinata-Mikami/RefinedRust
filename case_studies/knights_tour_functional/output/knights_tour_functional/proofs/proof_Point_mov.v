From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour_functional.generated Require Import generated_code_knights_tour_functional generated_specs_knights_tour_functional generated_template_Point_mov.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Point_mov_proof (π : thread_id) :
  Point_mov_lemma π.
Proof.
  Point_mov_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  (* !start proof(knights_tour_functional.mov) *)
  rename select ((Z.abs _ = 2 ∧ Z.abs _ = 1) ∨ _) into Hk.
  cbn in Hk. lia.
  (* !end proof *)
  all: print_remaining_sidecond.
Qed.
End proof.
