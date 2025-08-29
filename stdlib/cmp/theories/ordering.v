From refinedrust Require Import typing.

Inductive ordering : Set :=
| Less
| Equal
| Greater
.
Canonical Structure orderingRT := directRT ordering.

Global Instance ordering_eqdec : EqDecision ordering.
Proof. solve_decision. Defined.

Module Z.
  Definition cmp (a b : Z) : ordering :=
    if bool_decide (a < b) then Less
    else if bool_decide (a = b) then Equal
    else Greater.

  Lemma cmp_less_iff a b :
    cmp a b = Less ↔ a < b.
  Proof.
    unfold cmp. repeat case_bool_decide; naive_solver.
  Qed.
  Lemma cmp_equal_iff a b :
    cmp a b = Equal ↔ a = b.
  Proof.
    unfold cmp. repeat case_bool_decide.
    all: split; intros; try congruence; try lia.
  Qed.
  Lemma cmp_greater_iff a b :
    cmp a b = Greater ↔ a > b.
  Proof.
    unfold cmp. repeat case_bool_decide.
    all: split; intros; try congruence; try lia.
  Qed.
End Z.

Global Instance cmp_less_simpl a b :
  SimplBothRel (=) (Z.cmp a b) Less (a < b).
Proof.
  unfold SimplBothRel. by rewrite Z.cmp_less_iff.
Qed.
Global Instance cmp_equal_simpl a b :
  SimplBothRel (=) (Z.cmp a b) Equal (a = b).
Proof.
  unfold SimplBothRel. by rewrite Z.cmp_equal_iff.
Qed.
Global Instance cmp_greater_simpl a b :
  SimplBothRel (=) (Z.cmp a b) Greater (a > b).
Proof.
  unfold SimplBothRel. by rewrite Z.cmp_greater_iff.
Qed.
