From refinedrust Require Import typing shims.

Record SkipX (I : RT) : Type := mk_skip_x {
  skip_it : RT_xt I;
  skip_n : nat;
}.
Global Arguments skip_it {_}.
Global Arguments skip_n {_}.
Global Arguments mk_skip_x {_}.
Canonical Structure SkipXRT (I : RT) := directRT (SkipX I).

Global Instance SkipX_inh I :
  Inhabited (RT_xt I) → Inhabited (SkipX I).
Proof.
  intros Ha. exact (populate (mk_skip_x inhabitant 0)).
Qed.

Global Instance SkipX_simpl_exist I :
  SimplExist (SkipX I) (λ H, ∃ (it : RT_xt I) (n : nat), H (mk_skip_x it n)).
Proof.
  intros ? (it & n & Ha).
  eexists _. done.
Qed.

Global Instance SkipX_simpl_forall I :
  SimplForall (SkipX I) 2 (λ H, ∀ (it : RT_xt I) (n : nat), H (mk_skip_x it n)).
Proof.
  intros ? Ha [it n]. apply Ha.
Qed.

Global Instance simpl_both_skipX {I} (s1 s2 : SkipX I) :
  SimplBothRel (=) s1 s2
    (s1.(skip_it) = s2.(skip_it) ∧ s1.(skip_n) = s2.(skip_n)).
Proof.
  unfold SimplBothRel.
  destruct s1, s2; naive_solver.
Qed.
