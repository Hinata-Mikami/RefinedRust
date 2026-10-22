From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_test_collect_result_ok.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_collect_result_ok_proof (π : thread_id) :
  test_collect_result_ok_lemma π.
Proof.
  test_collect_result_ok_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  unfold_all_protected_evars.
  rewrite list_fmap_compose fst_zip; last by rewrite length_seqZ length_replicate.
  rewrite result_sequence_ok.
  repeat split; try reflexivity.
  rep liRStep; liShow.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
