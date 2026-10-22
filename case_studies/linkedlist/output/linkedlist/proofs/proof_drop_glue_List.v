From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_drop_glue_List.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_List_proof (π : thread_id) :
  drop_glue_List_lemma π.
Proof.
  drop_glue_List_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  iRename select ([∗ list] y ∈ x, ty_ghost_drop T_ty π ($# y))%I into "Hdrop".
  iApply prove_with_subtype_default.
  iSplitL "Hdrop".
  { iApply big_sepL_fmap. iExact "Hdrop". }
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
