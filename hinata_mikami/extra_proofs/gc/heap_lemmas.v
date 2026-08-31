From caesium Require Import lang notation.
From refinedrust Require Import typing.

Section heap_lemmas.

Context `{RRGS : !refinedrustGS Σ}.

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

Lemma prove_with_subtype_big_sepL_acc {A}
    E L step pm
    (xs : list A)
    (Φ : nat → A → iProp Σ)
    (i : nat) (x : A) T :
  (Φ i x -∗
     [∗ list] k ↦ y ∈ xs, Φ k y) -∗
  prove_with_subtype E L step pm
    (Φ i x) T -∗
  prove_with_subtype E L step pm
    ([∗ list] k ↦ y ∈ xs, Φ k y) T.
Proof.
  iIntros "Hclose Hsub".

  rewrite /prove_with_subtype.
  iEval (rewrite /prove_with_subtype) in "Hsub".

  iIntros (F ???) "#CTX #HE HL".

  iMod ("Hsub" with "[//] [//] [//] CTX HE HL")
    as "(%L' & %κs & %R & Hstep & HL & HT)".

  iModIntro.
  iExists L', κs, R.
  iFrame "HL HT".

  iApply (maybe_logical_step_wand with "[Hclose] Hstep").

  destruct pm.
  - iIntros "(Hi & HR)".
    iFrame "HR".
    iApply "Hclose".
    iExact "Hi".

  - iIntros "(Hi & HR)".
    iFrame "HR".

    iIntros "Hdead".
    iMod ("Hi" with "Hdead") as "Hi".
    iModIntro.

    iApply "Hclose".
    iExact "Hi".
Qed.


End heap_lemmas.