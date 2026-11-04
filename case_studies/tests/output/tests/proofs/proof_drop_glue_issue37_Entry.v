From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_drop_glue_issue37_Entry.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_issue37_Entry_proof (π : thread_id) :
  drop_glue_issue37_Entry_lemma π.
Proof.
  drop_glue_issue37_Entry_prelude.

  rep liRStep; liShow.
  destruct x. rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
