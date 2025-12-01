From refinedrust Require Import typing.

(*Notation "'<#>' x" := (fmap (M := list) PlaceIn x) (at level 30).*)
(*Notation "'<#>@{' A '}' x" := (fmap (M := A) PlaceIn x) (at level 30).*)
Notation "'<#>@{' 'result' '}' x" := (sum_map PlaceIn PlaceIn x) (at level 30).

Definition map_inl {A A' B} (f : A → A') : A + B -> A' + B :=
  sum_map f id.
Definition map_inr {A B B'} (f : B → B') : A + B -> A + B' :=
  sum_map id f.
