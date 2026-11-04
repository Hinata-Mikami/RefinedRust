From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops.generated Require Import generated_code_arithops generated_specs_arithops generated_template_i128asSubAssignREFi128_sub_assign.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma i128asSubAssignREFi128_sub_assign_proof (π : thread_id) :
  i128asSubAssignREFi128_sub_assign_lemma π.
Proof.
  i128asSubAssignREFi128_sub_assign_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
