From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized Require Export generated_code_sized.

Record Sized_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Sized_spec_attrs {
}.
#[global] Arguments Sized_spec_attrs : clear implicits.

#[global] Arguments Sized_spec_attrs {_ _}.

#[global] Arguments mk_Sized_spec_attrs  {_} {_} {_}.


Definition Sized_semantic_interp `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Self_ty: (type (Self_rt))) : Prop :=
  TySized Self_ty.
Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Existing Class Sized_semantic_interp. 
Global Instance Sized_semantic_TySized `{!refinedrustGS Σ} {rt} (ty : type rt) : 
  Sized_semantic_interp rt ty →
  TySized ty.
Proof. done. Qed.
End extra_specs.
Record Sized_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Sized_spec {
}.
#[global] Arguments Sized_spec : clear implicits.

#[global] Arguments Sized_spec {_ _}.


Section Sized.
Context `{RRGS : !refinedrustGS Σ}.
Definition Sized_spec_incl `{Self_rt : !RT} (spec1: ((Sized_spec (Self_rt)))) (spec2: ((Sized_spec (Self_rt)))) : Prop :=
  True.
Instance Sized_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Sized_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition Sized_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((Sized_spec_attrs ((Self_rt))))) : (spec_with _ _ (Sized_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Sized_spec _ _ ((Self_rt))).

End Sized.

Section Sized_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Sized_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.




End specs.
