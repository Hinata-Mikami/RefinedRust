From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.adequacy.generated Require Import generated_code_adequacy generated_specs_adequacy generated_template_main2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma main2_proof (π : thread_id) :
  main2_lemma π.
Proof.
  main2_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: unsafe_unfold_common_radium_defs; simpl in *; lia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
