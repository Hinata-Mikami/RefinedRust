From refinedrust Require Import typing shims.

Record TakeX (I : RT) : Type := mk_take_x {
  take_it : RT_xt I;
  take_n : nat;
}.
Global Arguments take_it {_}.
Global Arguments take_n {_}.
Global Arguments mk_take_x {_}.
Canonical Structure TakeXRT (I : RT) := directRT (TakeX I).

Global Instance TakeX_inh I :
  Inhabited (RT_xt I) → Inhabited (TakeX I).
Proof.
  intros Ha. exact (populate (mk_take_x inhabitant 0)).
Qed.

Global Instance TakeX_simpl_exist I :
  SimplExist (TakeX I) (λ H, ∃ (it : RT_xt I) (n : nat), H (mk_take_x it n)).
Proof.
  intros ? (it & n & Ha).
  eexists _. done.
Qed.

Global Instance TakeX_simpl_forall I :
  SimplForall (TakeX I) 2 (λ H, ∀ (it : RT_xt I) (n : nat), H (mk_take_x it n)).
Proof.
  intros ? Ha [it n]. apply Ha.
Qed.

Global Instance simpl_both_takeX {I} (s1 s2 : TakeX I) :
  SimplBothRel (=) s1 s2
    (s1.(take_it) = s2.(take_it) ∧ s1.(take_n) = s2.(take_n)).
Proof.
  unfold SimplBothRel.
  destruct s1, s2; naive_solver.
Qed.
