From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec generated_template_client_fold_i32.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma client_fold_i32_proof (π : thread_id) :
  client_fold_i32_lemma π.
Proof.
  client_fold_i32_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep. liShow.
    iRename select (∀ _ _, FnOnce_Pre _ _ _ _ _)%I into "Hpre".
    iRename select (∀ _ _ _, FnOnce_Post _ _ _ _ _ _ -∗ _)%I into "Hpost".
    iSpecialize ("Hpre" $! _ _).
    liRStepUntil typed_stmt.
    1: rep liRStep.
    1: { iPoseProof ("Hpost" with "[$]") as "(% & _)". rep liRStep. } }
  { rep <-! liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  rewrite fold_left_app//.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
