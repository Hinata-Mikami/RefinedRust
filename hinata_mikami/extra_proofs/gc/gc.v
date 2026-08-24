From caesium Require Import lang notation.
From refinedrust Require Import typing shims.



Lemma simplify_goal_big_sepL_app {A}
    (xs1 xs2 : list A)
    (Φ : nat → A → iProp Σ) T :
  ([∗ list] i ↦ x ∈ xs1, Φ i x) ∗
  ([∗ list] i ↦ x ∈ xs2,
      Φ (length xs1 + i)%nat x) ∗ T
  ⊢
  simplify_goal
    ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  rewrite /simplify_goal.
  rewrite big_sepL_app.
  iIntros "($ & $ & $)".
Qed.

Definition simplify_goal_big_sepL_app_inst :=
  [instance @simplify_goal_big_sepL_app with 10%N].

Global Existing Instance simplify_goal_big_sepL_app_inst.