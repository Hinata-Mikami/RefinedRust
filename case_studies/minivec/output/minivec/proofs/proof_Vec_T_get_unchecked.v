From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_unchecked.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma Vec_T_get_unchecked_proof (π : thread_id) :
  Vec_T_get_unchecked_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft4" ["ulft_1"].
  Vec_T_get_unchecked_prelude.

  rep <-! liRStep; liShow.

  apply_update (updateable_typed_array_access x0 i (st_of T_ty)).
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { revert select (ly_size (mk_array_layout _ _) ≤ _).
    move: Hi Hcap.
    rewrite ly_size_mk_array_layout.
    clear. nia. }
  { move: Hi Hcap. clear. nia. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
