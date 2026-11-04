From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_test_collect_result_err.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_collect_result_err_proof (π : thread_id) :
  test_collect_result_err_lemma π.
Proof.
  test_collect_result_err_prelude.

  repeat (
    tryif iMatchHyp (fun _ P =>
      lazymatch P with IteratorCollectEnd _ _ _ _ _ _ => idtac end)
    then fail
    else liRStep);
  liRStepUntil typed_place.
  destruct x'4.
  - assert (0 < x'0) as Hpos.
    { destruct (decide (x'0 = 0)) as [->|]; last lia. done. }
    rewrite list_fmap_compose fst_zip; last by rewrite length_seqZ length_replicate.
    rewrite seqZ_cons; last done.
    rep liRStep.
  - iRename select (IteratorCollectEnd _ _ _ _ _ _) into "Hend".
    iEval (rewrite /IteratorCollectEnd; simpl) in "Hend".
    iDestruct "Hend" as "((%Hnext & _) & _)".
    destruct Hnext as (_ & (_ & ->) & _).
    rename select (if_Err _ _) into Hcollect_err.
    rewrite list_fmap_compose fst_zip in Hcollect_err; last by rewrite length_seqZ length_replicate.
    rewrite seqZ_cons in Hcollect_err; last lia. simpl in Hcollect_err. naive_solver.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
