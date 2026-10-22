From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_iter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_iter_proof (π : thread_id) :
  List_T_iter_lemma π.
Proof.
  List_T_iter_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  (* A fresh forward iterator starts before the physical head. *)
  liInst Hevar_locs locs.
   liInst Hevar_prev_ptr NULL_loc.
   split; first (destruct (decide (loc_a hd_ptr = 0)), (decide (loc_a tl_ptr = 0));
     simpl in *; destruct self; simpl in *; naive_solver).
   iRename select ([∗ list] _ ↦ _ ∈ _, _)%I into "Hxs".
   iEval (rewrite big_sepL_fmap /linkedlist_node_shared) in "Hxs".
   rewrite list_fmap_id.
   rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
