From stdpp Require Import base.
From Stdlib Require Import Bool Nat BinInt.
From Stdlib Require Import Zify ZifyClasses.
From Stdlib Require Import Lia.
From Stdlib Require Import ZifyComparison ZifyBool ZifyNat.
From Stdlib Require Import Arith.

#[global]
Program Instance BinOp_Natcompare : BinOp Nat.compare :=
  { TBOp := ZcompareZ }.
Next Obligation.
  unfold ZcompareZ, Z_of_comparison.
  intros. rewrite Znat.Nat2Z.inj_compare.
  reflexivity.
Qed.
Add Zify BinOp BinOp_Natcompare.

Definition NatcompareZ (x y : nat) :=
  Z_of_comparison (Nat.compare x y).

#[global] Program Instance NatcompareSpec : BinOpSpec NatcompareZ :=
  {| BPred := λ x y r, (x = y → r = 0%Z) ∧
                       (x > y → r = 1%Z) ∧
                       (x < y → r = (-1)%Z) |}.
Next Obligation.
  unfold NatcompareZ, Z_of_comparison.
  intros.
  destruct (x ?= y) eqn:C; simpl.
  - rewrite Nat.compare_eq_iff in C.
    lia.
  - rewrite Nat.compare_lt_iff in C.
    lia.
  - rewrite Nat.compare_gt_iff in C.
    lia.
Qed.
Add Zify BinOpSpec NatcompareSpec.
