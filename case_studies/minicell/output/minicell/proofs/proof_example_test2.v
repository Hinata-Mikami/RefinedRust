From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minicell.generated Require Import generated_code_minicell generated_specs_minicell generated_template_example_test2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma example_test2_proof (π : thread_id) :
  example_test2_lemma π.
Proof.
  example_test2_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unsafe_unfold_common_caesium_defs; simpl. lia. }
  { revert select (Zeven _). revert select (_ `rem` 2 ≠ 0%Z).
    rewrite Zeven_ex_iff Z.rem_divide; last done.
    setoid_rewrite Z.mul_comm; done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
