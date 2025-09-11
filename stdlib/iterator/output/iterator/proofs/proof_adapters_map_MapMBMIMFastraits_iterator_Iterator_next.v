From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_map_MapMBMIMFastraits_iterator_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_map_MapMBMIMFastraits_iterator_Iterator_next_proof (π : thread_id) :
  adapters_map_MapMBMIMFastraits_iterator_Iterator_next_lemma π.
Proof.
  adapters_map_MapMBMIMFastraits_iterator_Iterator_next_prelude.

  rep liRStep. liShow.

  simpl.
  iRename select (li_sealed (□ (∀ _ _ _, traits_iterator_Iterator_Next _ _ _ None _ -∗ _))) into "Hnone".
  iRename select (li_sealed (□ (∀ _ _ _ _,  _))) into "Hsome".
  iRename select (_ (map_it _) (map_clos _)) into "Hinv".
  iRename select (traits_iterator_Iterator_Next _ _ _ _ _) into "Hnext".
  iPoseProof (li_sealed_use_pers with "Hsome") as "#Hsome'".
  iPoseProof (li_sealed_use_pers with "Hnone") as "#Hnone'".
  iPoseProof (boringly_intro with "Hnext") as "#Hnext_x".

  destruct x'0.
  { (* obtain an element *)
    iPoseProof ("Hsome'" with "Hnext Hinv") as "(Hpre & Hinv_clos)".
    iPoseProof (boringly_intro with "Hpre") as "#Hpre_x".
    rep <-! liRStep. liShow.
    iRename select (FnMut_PostMut _ _ _ _ _ _) into "Hpost".
    iPoseProof (boringly_intro with "Hpost") as "#Hpost_x".
    iPoseProof ("Hinv_clos" with "Hpost") as "Hinv".
    rep liRStep.
    liInst Hevar (mut_ref_ghost_drop _ _).
    liInst Hevar2 x4.
    rep liRStep. liShow.
    iApply prove_with_subtype_default.
    liInst Hevar r.
    rep liRStep. }
  { (* no element *)
    iPoseProof ("Hnone'" with "Hnext Hinv") as "Hinv".
    simpl.
    rep <-! liRStep. liShow. 
    rep 100 liRStep. liShow.
    rep liRStep.
    liInst Hevar1 x4.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. 1-10: sidecond_solver.
  2: { unshelve sidecond_solver.
        (* TODO: this is a bug in the contract...: For an instantiation, we also need to be able to assume that its elctx is okay. I.e., similar to how we add typaram_wf *)


  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
