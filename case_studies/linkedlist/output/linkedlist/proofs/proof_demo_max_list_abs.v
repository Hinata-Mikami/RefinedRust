From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_demo_max_list_abs.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma demo_max_list_abs_proof (π : thread_id) :
  demo_max_list_abs_lemma π.
Proof.
  demo_max_list_abs_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite list_fmap_compose. sidecond_hammer. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
