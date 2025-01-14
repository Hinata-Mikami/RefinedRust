From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_unchecked_mut.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma Vec_T_get_unchecked_mut_proof (π : thread_id) :
  Vec_T_get_unchecked_mut_lemma π.
Proof.
  Vec_T_get_unchecked_mut_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try (rewrite project_vec_els_insert_lt /=; [|lia]; normalize_and_simpl_goal).
  all: assert (length xs ≤ length x2); first (specialize (project_vec_els_length (length xs) x2); rewrite -Hxs; solve_goal).
  all: normalize_and_simpl_goal; try solve_goal with lia.

  { solve_goal with nia. }
  { solve_goal with nia. }
  { apply list_lookup_insert_Some'. 
    split; normalize_and_simpl_goal.
    { simpl in *. lia. }
    { rewrite Hxs. solve_goal with lia. }
  }
  { by rewrite Hxs. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
