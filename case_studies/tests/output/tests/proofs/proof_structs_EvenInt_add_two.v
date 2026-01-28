From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_structs_EvenInt_add_two.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma structs_EvenInt_add_two_proof (π : thread_id) :
  structs_EvenInt_add_two_lemma π.
Proof.
  generalize RR_CONFIG_DONT_FOLD_PLACES; intros ?.
  structs_EvenInt_add_two_prelude.

  rep <-! liRStep; liShow.
  liRStepUntil interpret_typing_hint.
  iApply interpret_typing_hint_ignore.
  rep <-! liRStep; liShow.
  liRStepUntil interpret_typing_hint.
  iApply interpret_typing_hint_ignore.
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { by apply Zeven_Sn, Zodd_Sn. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
