From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_RawVec_T_new.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma RawVec_T_new_proof (π : thread_id) :
  RawVec_T_new_lemma π.
Proof.
  RawVec_T_new_prelude.

  (* Otherwise, in the ZST case, we try to compute a very big list *)
  Arguments replicate : simpl never.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve.
  all: open_cache; try lia.
  all: sidecond_hammer.
  rewrite MaxInt_eq. solve_goal. (* NOTE : manual *)
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
