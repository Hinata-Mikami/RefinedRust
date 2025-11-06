From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_map.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_map_proof (π : thread_id) :
  traits_iterator_Iterator_map_lemma π.
Proof.
  traits_iterator_Iterator_map_prelude.

  repeat liRStep; liShow.
  unfold MapInv.
  repeat liRStep; liShow.
  liInst Hevar Inv.
  iApply prove_with_subtype_default.
  iFrame.
  rep liRStep. liShow.
  iApply prove_with_subtype_default.
  iSplitR. { unfold li_sealed. done. }
  iApply prove_with_subtype_default.
  iSplitR. { unfold li_sealed. done. }
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
