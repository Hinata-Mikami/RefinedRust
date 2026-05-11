From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_moves.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma moves_proof (π : thread_id) :
  moves_lemma π.
Proof.
  moves_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. 
  (* !start proof(knights_tour.moves) *)
  all: try (intros ??; rewrite !elem_of_cons elem_of_nil; intros Helem;
    repeat (destruct Helem as  [Heq | Helem]; [injection Heq; lia | ]); done).
  (* !end proof *)
  all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
