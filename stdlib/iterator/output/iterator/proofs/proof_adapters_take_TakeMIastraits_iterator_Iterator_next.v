From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_take_TakeMIastraits_iterator_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_take_TakeMIastraits_iterator_Iterator_next_proof (π : thread_id) :
  adapters_take_TakeMIastraits_iterator_Iterator_next_lemma π.
Proof.
  adapters_take_TakeMIastraits_iterator_Iterator_next_prelude.

  rep <-! liRStep; liShow.
  { (* unfold invariant *)
    iRename select (traits_iterator_Iterator_Inv _ _ _ _) into "Hinv".
    iEval (rewrite /traits_iterator_Iterator_Inv/=) in "Hinv".
    rep <-! liRStep; liShow.
    rep <- 8 liRStep; liShow.
    { iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow. }
    { iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow. } }
  { rep <-! liRStep; liShow. }
  { iRename select (traits_iterator_Iterator_Inv
      (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs
        MI_rt traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_spec_attrs
        DropGlue_MI_spec_attrs DropGlue_MIastraits_iterator_Iterator_Item_spec_attrs)
      π x x0) into "Hinv".
    iAssert (traits_iterator_Iterator_Inv
      (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs
        MI_rt traits_iterator_Iterator_MI_Item_rt traits_iterator_Iterator_MI_spec_attrs
        DropGlue_MI_spec_attrs DropGlue_MIastraits_iterator_Iterator_Item_spec_attrs)
      π x (mk_take_x (take_it x0) (take_n x0)))%I with "[Hinv]" as "Hinv".
    { simpl. iFrame. }
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
