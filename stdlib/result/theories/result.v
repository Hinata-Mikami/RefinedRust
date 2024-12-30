From refinedrust Require Import typing.

(*Notation "'<#>' x" := (fmap (M := list) PlaceIn x) (at level 30).*)
(*Notation "'<#>@{' A '}' x" := (fmap (M := A) PlaceIn x) (at level 30).*)
Notation "'<#>@{' 'result' '}' x" := (sum_map PlaceIn PlaceIn x) (at level 30).

Definition is_Ok {A B} (x : result A B) :=
  ∃ y : A, x = Ok y.
Global Instance is_Ok_dec {A B} (x : result A B) : Decision (is_Ok x).
Proof.
  destruct x.
  - left. eexists _. done.
  - right. intros [y Hx]. naive_solver.
Defined.

Definition is_Err {A B} (x : result A B) :=
  ∃ y : B, x = Err y.
Global Instance is_Err_dec {A B} (x : result A B) : Decision (is_Err x).
Proof.
  destruct x.
  - right. intros [y Hx]. naive_solver.
  - left. eexists _. done.
Defined.

Definition map_inl {A A' B} (f : A → A') : A + B -> A' + B :=
  sum_map f id.
Definition map_inr {A B B'} (f : B → B') : A + B -> A + B' :=
  sum_map id f.
