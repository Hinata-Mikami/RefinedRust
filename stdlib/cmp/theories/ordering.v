From refinedrust Require Import typing.

Inductive ordering : Set :=
| Less
| Equal
| Greater
.
Canonical Structure orderingRT := directRT ordering.

Global Instance ordering_eqdec : EqDecision ordering.
Proof. solve_decision. Defined.

Definition ord_lt {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  cmp a b = Less.
Definition ord_eq {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  cmp a b = Equal.
Definition ord_gt {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  cmp a b = Greater.

Notation "a '<o{' cmp '}' b" := (ord_lt cmp a b) (at level 42).
Notation "a '>o{' cmp '}' b" := (ord_gt cmp a b) (at level 42).
Notation "a '=o{' cmp '}' b" := (ord_eq cmp a b) (at level 42).

Global Hint Unfold ord_lt ord_gt ord_eq: lithium_rewrite.

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
  Lemma cmp_not_less_iff a b :
    cmp a b ≠ Less ↔ a >= b.
  Proof.
    unfold cmp. repeat case_bool_decide; naive_solver.
  Qed.
  Lemma cmp_equal_iff a b :
    cmp a b = Equal ↔ a = b.
  Proof.
    unfold cmp. repeat case_bool_decide.
    all: split; intros; try congruence; try lia.
  Qed.
  Lemma cmp_not_equal_iff a b :
    cmp a b ≠ Equal ↔ a ≠ b.
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
  Lemma cmp_not_greater_iff a b :
    cmp a b ≠ Greater ↔ a ≤ b.
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
Global Instance cmp_not_greater_simpl a b :
  SimplBoth (Z.cmp a b ≠ Greater) (a ≤ b).
Proof.
  unfold SimplBoth. by rewrite Z.cmp_not_greater_iff.
Qed.
Global Instance cmp_not_less_simpl a b :
  SimplBoth (Z.cmp a b ≠ Less) (a >= b).
Proof.
  unfold SimplBoth. by rewrite Z.cmp_not_less_iff.
Qed.

Definition max_by {A} (cmp : A → A → ordering) (a b : A) : A :=
  match cmp a b with
  | Greater => a
  | _ => b
  end.
Definition min_by {A} (cmp : A → A → ordering) (a b : A) : A :=
  match cmp a b with
  | Less => a
  | _ => b
  end.

Definition max_list_cmp {A} (cmp : A → A → ordering) (def : A) : list A → A :=
  fix go l :=
  match l with
  | [] => def
  | x :: l =>
      let m := go l in
      max_by cmp x m
  end.

Class CorrectEq {A : Type} (eq : A → A → bool) := {
  correct_eq_refl :: Reflexive (λ a b, Is_true (eq a b));
  correct_eq_sym :: Symmetric (λ a b, Is_true (eq a b));
  correct_eq_trans :: Transitive (λ a b, Is_true (eq a b));
}.

Class CorrectOrd {A : Type} (eq : A → A → bool) (cmp : A → A → ordering) := {
  correct_ord_correct_eq :: CorrectEq eq;
  correct_ord_eq_compat : ∀ x y, eq x y ↔ x =o{cmp} y;
  correct_ord_lt_trans :: Transitive (ord_lt cmp);
  correct_ord_gt_trans :: Transitive (ord_gt cmp);
  correct_ord_antisym : ∀ x y, ord_lt cmp x y ↔ ord_gt cmp y x;
  (* for convenience *)
  correct_ord_eq_leibniz : ∀ x y, eq x y ↔ x = y;
}.

Section correct_ord.
  Context {A : Type} {eq cmp} `{!CorrectOrd (A := A) eq cmp}.

  Local Set Default Proof Using "Type*".

  #[export] Instance correct_ord_eq_trans : Transitive (ord_eq cmp).
  Proof.
    intros a b c.
    rewrite -!correct_ord_eq_compat.
    apply correct_eq_trans.
  Qed.
  #[export] Instance correct_ord_eq_sym : Symmetric (ord_eq cmp).
  Proof.
    intros a b.
    rewrite -!correct_ord_eq_compat.
    apply correct_eq_sym.
  Qed.
  #[export] Instance correct_ord_eq_refl : Reflexive (ord_eq cmp).
  Proof.
    intros a.
    rewrite -!correct_ord_eq_compat.
    apply correct_eq_refl.
  Qed.

  Lemma correct_ord_eq_compat' x y : eq x y ↔ cmp x y = Equal.
  Proof.
    specialize (correct_ord_eq_compat x y).
    unfold ord_eq. done.
  Qed.
  Lemma correct_ord_cmp_refl a :
    cmp a a = Equal.
  Proof.
    by rewrite -correct_ord_eq_compat'.
  Qed.

  Lemma correct_ord_cmp_leibniz a b :
    cmp a b = Equal ↔ a = b.
  Proof.
    rewrite -correct_ord_eq_compat'.
    apply correct_ord_eq_leibniz.
  Qed.

  Lemma not_ord_lt_iff a b :
    (¬ a <o{cmp} b) ↔ (a =o{cmp} b ∨ a >o{cmp} b).
  Proof.
    unfold ord_lt, ord_gt, ord_eq.
    destruct (cmp a b); naive_solver.
  Qed.
  Lemma not_ord_gt_iff a b :
    (¬ a >o{cmp} b) ↔ (a =o{cmp} b ∨ a <o{cmp} b).
  Proof.
    unfold ord_lt, ord_gt, ord_eq.
    destruct (cmp a b); naive_solver.
  Qed.

  Lemma max_by_refl a : max_by cmp a a = a.
  Proof.
    unfold max_by. by rewrite correct_ord_cmp_refl.
  Qed.

  Lemma max_by_max_by a b :
    max_by cmp a (max_by cmp a b) = max_by cmp a b.
  Proof.
    unfold max_by.
    destruct (cmp a b) eqn:Hab; try rewrite Hab; try done.
    by rewrite correct_ord_cmp_refl.
  Qed.
  Lemma max_by_com a b :
    (max_by cmp a b) = (max_by cmp b a).
  Proof.
    unfold max_by.
    destruct (cmp a b) eqn:Hab.
    all: try apply correct_ord_antisym in Hab; try rewrite Hab; try done.
    apply correct_ord_eq_sym in Hab. rewrite Hab.
    apply correct_ord_eq_leibniz.
    by apply correct_ord_eq_compat.
  Qed.
  Lemma max_by_assoc a b c :
    max_by cmp a (max_by cmp b c) = max_by cmp (max_by cmp a b) c.
  Proof.
    unfold max_by.
    destruct (cmp a b) eqn:Hab.
    all: destruct (cmp b c) eqn:Hbc.
    all: destruct (cmp a c) eqn:Hac.
    all: try rewrite Hab.
    all: try done.
    all: repeat match goal with
      | H : cmp _ _ = Equal |- _ =>
          apply correct_ord_cmp_leibniz in H; subst
      | H : cmp ?a ?b = Less, H2 : cmp ?b ?c = Less |- _ =>
          specialize (correct_ord_lt_trans _ _ _ H H2);
          unfold ord_lt; intros ?;
          clear H H2
      | H : cmp ?a ?b = Greater, H2 : cmp ?b ?c = Greater |- _ =>
          specialize (correct_ord_gt_trans _ _ _ H H2);
          unfold ord_gt; intros ?;
          clear H H2
      end; try congruence.
  Qed.

  Lemma max_by_r a b :
    ¬ (a >o{cmp} b) → max_by cmp a b = b.
  Proof.
    intros Hcmp. unfold max_by.
    destruct (cmp a b) eqn:Heq; done.
  Qed.
  Lemma max_by_l a b :
    ¬ (a <o{cmp} b) → max_by cmp a b = a.
  Proof.
    intros Hcmp. unfold max_by.
    destruct (cmp a b) eqn:Heq; try done.
    apply correct_ord_cmp_leibniz in Heq. done.
  Qed.
End correct_ord.

(** ** Properties of the [max_list_cmp] function *)
Section max_list.
  Context {A : Type}  {eq cmp} `{!CorrectOrd (A := A) eq cmp}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Local Set Default Proof Using "Type*".

  (* What properties do we need?
     - equality is reflexive, transitive, symmetric
     - partial order is compatible with equality
     - order is compatible with partial order, and so with equality
     - order is transitive
  *)

  Lemma max_list_cmp_def def l :
    max_list_cmp cmp def l =
      max_by cmp def (max_list_cmp cmp def l).
  Proof.
    induction l as [ | x l IH]; simpl.
    - by rewrite max_by_refl.
    - rewrite IH.
      rewrite (max_by_assoc x def _).
      rewrite (max_by_com x def).
      rewrite -(max_by_assoc def x _).
      rewrite (max_by_assoc def def _).
      rewrite max_by_refl.
      done.
  Qed.
  Lemma max_list_cmp_app def l k :
    max_list_cmp cmp def (l ++ k) =
    max_by cmp (max_list_cmp cmp def l) (max_list_cmp cmp def k).
  Proof.
    induction l as [ | ?? IH] in k |-*; simpl.
    - by rewrite {1}max_list_cmp_def.
    - rewrite IH. by rewrite max_by_assoc.
  Qed.
End max_list.

(* TODO autorewrite cannot handle the TC assumption... *)
(*Global Hint Rewrite -> @max_list_cmp_app : lithium_rewrite.*)
