From stdpp Require Import base.
From refinedrust Require Import type ltypes.
From refinedrust Require Import options.

Class XMap (A B : Type) := xmap : (A → B).

Global Instance xmap_prod {A1 A2 B1 B2} (X1 : XMap A1 A2) (X2 : XMap B1 B2) :
  XMap (A1 * B1) (A2 * B2) :=
  λ '(a, b), (xmap a, xmap b).
Global Instance fmap_xmap {A1 A2} {M : Type → Type} (X : XMap A1 A2) (F : FMap M) :
  XMap (M A1) (M A2) :=
  F _ _ X.
Global Instance xmap_id {A : Type} : XMap A A := id.

Global Instance xmap_place_rfn {A B : RT} (X : XMap A B) :
  XMap A (place_rfn B) := PlaceIn ∘ X.

Global Instance xt_inj_xmap `{!typeGS Σ} {rt : RT}  : XMap (RT_xt rt) rt :=
  RT_xrt rt.

Global Instance result_xmap {A1 A2 B1 B2} (X1 : XMap A1 A2) (X2 : XMap B1 B2) :
  XMap (result A1 B1) (result A2 B2) :=
  λ x,
  match x with
  | inl x => inl (X1 x)
  | inr x => inr (X2 x)
  end.

Global Hint Unfold xmap : lithium_rewrite.
Global Hint Unfold xmap_id : lithium_rewrite.
Global Hint Unfold xmap_place_rfn : lithium_rewrite.

Lemma fmap_xmap_unfold {A1 A2} {M} (f : FMap M) (x : XMap A1 A2) a :
  fmap_xmap x f a = fmap x a.
Proof. done. Qed.
Global Hint Rewrite @fmap_xmap_unfold : lithium_rewrite.

Global Hint Unfold xt_inj_xmap : lithium_rewrite.

Global Instance simpl_both_xmap_inl {A1 A2 B1 B2} (f : A1 → A2) (g : B1 → B2) (x : result A1 B1) (y : A2): 
  SimplBothRel (=) (result_xmap f g x) (inl y) (∃ x', x = inl x' ∧ y = f x').
Proof. unfold SimplBothRel. destruct x; naive_solver. Qed.
Global Instance simpl_both_xmap_inr {A1 A2 B1 B2} (f : A1 → A2) (g : B1 → B2) (x : result A1 B1) (y : B2): 
  SimplBothRel (=) (result_xmap f g x) (inr y) (∃ x', x = inr x' ∧ y = g x').
Proof. unfold SimplBothRel. destruct x; naive_solver. Qed.
