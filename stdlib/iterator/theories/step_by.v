From refinedrust Require Import typing shims.

Record StepByX (I : RT) : Type := mk_step_by_x {
  step_by_it : RT_xt I;
  step_by_n : nat;
  step_by_first : bool;
}.
Global Arguments step_by_it {_}.
Global Arguments step_by_n {_}.
Global Arguments step_by_first {_}.
Global Arguments mk_step_by_x {_}.
Canonical Structure StepByXRT (I : RT) := directRT (StepByX I).

Global Instance StepByX_inh I :
  Inhabited (RT_xt I) → Inhabited (StepByX I).
Proof.
  intros Ha. exact (populate (mk_step_by_x inhabitant 0 true)).
Qed.

Global Instance StepByX_simpl_exist I :
  SimplExist (StepByX I) (λ H, ∃ (it : RT_xt I) (n : nat) (first : bool), H (mk_step_by_x it n first)).
Proof.
  intros ? (it & n & first & Ha).
  eexists _. done.
Qed.

Global Instance StepByX_simpl_forall I :
  SimplForall (StepByX I) 3 (λ H, ∀ (it : RT_xt I) (n : nat) (first : bool), H (mk_step_by_x it n first)).
Proof.
  intros ? Ha [it n first]. apply Ha.
Qed.

Global Instance simpl_both_step_byX {I} (s1 s2 : StepByX I) :
  SimplBothRel (=) s1 s2
    (s1.(step_by_it) = s2.(step_by_it) ∧
     s1.(step_by_n) = s2.(step_by_n) ∧
     s1.(step_by_first) = s2.(step_by_first)).
Proof.
  unfold SimplBothRel.
  destruct s1, s2; naive_solver.
Qed.
