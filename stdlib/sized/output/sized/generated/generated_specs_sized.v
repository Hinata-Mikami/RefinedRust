From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized Require Export generated_code_sized.

Record Sized_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Sized_spec_attrs {
}.
#[global] Arguments Sized_spec_attrs : clear implicits.

#[global] Arguments Sized_spec_attrs {_ _}.

#[global] Arguments mk_Sized_spec_attrs  {_} {_} {_}.


Record Drop_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Drop_spec_attrs {
}.
#[global] Arguments Drop_spec_attrs : clear implicits.

#[global] Arguments Drop_spec_attrs {_ _}.

#[global] Arguments mk_Drop_spec_attrs  {_} {_} {_}.


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


Record Drop_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Drop_spec {
  Drop_drop_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments Drop_spec : clear implicits.

#[global] Arguments Drop_spec {_ _}.


Section Sized.
Context `{RRGS : !refinedrustGS Σ}.
Definition Sized_spec_incl `{Self_rt : !RT} (spec1: ((Sized_spec (Self_rt)))) (spec2: ((Sized_spec (Self_rt)))) : Prop :=
  True.
Instance Sized_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Sized_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Sized_spec `{Self_rt : !RT} : (ScopeBindable ((Sized_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Sized_spec (Self_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((Sized_spec (Self_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_Sized_spec.

Definition Sized_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((Sized_spec_attrs ((Self_rt))))) : (spec_with _ _ (Sized_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Sized_spec _ _ ((Self_rt))).

End Sized.

Section Drop.
Context `{RRGS : !refinedrustGS Σ}.
Definition Drop_spec_incl `{Self_rt : !RT} (spec1: ((Drop_spec (Self_rt)))) (spec2: ((Drop_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(Drop_drop_spec)) (spec2.(Drop_drop_spec)))).
Instance Drop_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Drop_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Drop_spec `{Self_rt : !RT} : (ScopeBindable ((Drop_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Drop_spec (Self_rt)))) :=
      {|
        Drop_drop_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Drop_drop_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Drop_spec (Self_rt)))) :=
      {|
        Drop_drop_spec  :=
          (scope_add_elctx (E) (s.(Drop_drop_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Drop_spec.

Definition Drop_drop_base_spec (Self_rt: RT) (Self_st: syn_type) (Drop_Self_spec_attrs: (Drop_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, (⌜(False)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, True).

Definition Drop_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((Drop_spec_attrs ((Self_rt))))) : (spec_with _ _ (Drop_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      Drop_drop_spec  :=
        (Drop_drop_base_spec ((Self_rt)) (Self_st)) _ATTRS 
           <TY> Self_ty : (spec_with 1 [] fn_spec);
    |}
.

End Drop.

Section Sized_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Sized_trait_req_incls.

Section Drop_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Drop_drop (Self_rt: RT) (Self_st: syn_type) (Drop_Self_spec_attrs: (Drop_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Drop_Self_spec: (spec_with 0 [] (Drop_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Drop_spec_incl Drop_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Drop_base_spec (Self_rt) Self_st Drop_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty])))).
End Drop_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.




End specs.
