From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_step_by_StepByMIastraits_iterator_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_step_by_StepByMIastraits_iterator_Iterator_next_proof (π : thread_id) :
  adapters_step_by_StepByMIastraits_iterator_Iterator_next_lemma π.
Proof.
  adapters_step_by_StepByMIastraits_iterator_Iterator_next_prelude.

  rep <-! liRStep; liShow.
  { (* first element: call next directly *)
    iRename select (traits_iterator_Iterator_Inv _ _ _ _) into "Hinv".
    iEval (rewrite /traits_iterator_Iterator_Inv/=) in "Hinv".
    rep <- 1 liRStep; liShow.
    { liRStep; liShow.
      rewrite H11.
      iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow. } }
  { (* subsequent elements: skip step_minus_one elements *)
    iRename select (traits_iterator_Iterator_Inv _ _ _ _) into "Hinv".
    iEval (rewrite /traits_iterator_Iterator_Inv/=) in "Hinv".
    rep <- 20 liRStep; liShow.
    { liInst Hevar_it x'0. liInst Hevar_n (step_by_n x0). liInst Hevar_first false.
      rewrite H11.
      rep liRStep; liShow.
      { liInst Hevar_seq x'1. liInst Hevar_s2_inner x'.
        rep liRStep; liShow.
        iRename select (traits_iterator_Iterator_Inv traits_iterator_Iterator_MI_spec_attrs π x x'0) into "Hinv".
        iAssert (traits_iterator_Iterator_Inv
          (adapters_step_by_StepByMIastraits_iterator_Iterator_spec_attrs
            MI_rt traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_spec_attrs)
          π x (mk_step_by_x x'0 (step_by_n x0) false))%I with "[Hinv]" as "Hinv".
        { simpl. iFrame. }
        rep liRStep; liShow. }
      { rep liRStep; liShow.
        liInst Hevar_seq x'1. liInst Hevar_s2_inner x'.
        rep <- 1 liRStep; liShow.
        iEval (rewrite /traits_iterator_Iterator_Inv/=).
        rep liRStep; liShow. } }
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
