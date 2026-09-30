From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.clone.clone Require Export generated_code_clone.

Record Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Clone_spec_attrs {
}.
#[global] Arguments Clone_spec_attrs : clear implicits.

#[global] Arguments Clone_spec_attrs {_ _}.

#[global] Arguments mk_Clone_spec_attrs  {_} {_} {_}.


Record Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Clone_Self_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )} : Type := mk_Copy_spec_attrs {
}.
#[global] Arguments Copy_spec_attrs : clear implicits.

#[global] Arguments Copy_spec_attrs {_ _}.

#[global] Arguments mk_Copy_spec_attrs  {_} {_} {_} {_}.


Definition Copy_semantic_interp `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Self_ty: (type (Self_rt))) : Prop :=
  Copyable Self_ty.
Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs ((place_rfnRT (T_rt))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition constTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs (loc))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition mutTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs (loc))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition boolasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (bool))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition charasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition constTasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs (loc) ((constTasClone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition mutTasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs (loc) ((mutTasClone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition boolasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (bool) (boolasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition charasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (charasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i128asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i16asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i32asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i64asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i8asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (isizeasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u128asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u16asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u32asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u64asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u8asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (usizeasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_marker_PhantomDataTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_marker_PhantomDataTasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt))))) ((std_marker_PhantomDataTasClone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Existing Class Copy_semantic_interp. 
Global Instance Copy_semantic_Copyable `{!refinedrustGS Σ} {rt} (ty : type rt) : 
  Copy_semantic_interp rt ty →
  Copyable ty.
Proof. done. Qed.
End extra_specs.
Record Clone_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Clone_spec {
  Clone_clone_spec  : (spec_with 1 [] fn_spec);
  Clone_clone_from_spec  : (spec_with 2 [] fn_spec);
}.
#[global] Arguments Clone_spec : clear implicits.

#[global] Arguments Clone_spec {_ _}.


Record Copy_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Copy_spec {
}.
#[global] Arguments Copy_spec : clear implicits.

#[global] Arguments Copy_spec {_ _}.


Section Clone.
Context `{RRGS : !refinedrustGS Σ}.
Definition Clone_spec_incl `{Self_rt : !RT} (spec1: ((Clone_spec (Self_rt)))) (spec2: ((Clone_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(Clone_clone_spec)) (spec2.(Clone_clone_spec)))) ∧ ((function_subtype (spec1.(Clone_clone_from_spec)) (spec2.(Clone_clone_from_spec)))).
Instance Clone_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Clone_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Clone_spec `{Self_rt : !RT} : (ScopeBindable ((Clone_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Clone_spec (Self_rt)))) :=
      {|
        Clone_clone_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Clone_clone_spec)));
        Clone_clone_from_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Clone_clone_from_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Clone_spec (Self_rt)))) :=
      {|
        Clone_clone_spec  :=
          (scope_add_elctx (E) (s.(Clone_clone_spec)));
        Clone_clone_from_spec  :=
          (scope_add_elctx (E) (s.(Clone_clone_from_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Clone_spec.

Definition Clone_clone_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ Self_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Clone_clone_from_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, source) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), source :@: (shr_ref ulft_2 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (($#@{ (Self_rt) } source)))) |
      (* unwind cond... *) DropGlue_Self_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition Clone_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Clone_spec_attrs ((Self_rt))))) : (spec_with _ _ (Clone_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      Clone_clone_spec  :=
        (Clone_clone_base_spec ((Self_rt)) (Self_st)) DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 1 [] fn_spec);
      Clone_clone_from_spec  :=
        (Clone_clone_from_base_spec ((Self_rt)) (Self_st)) DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 2 [] fn_spec);
    |}
.
Arguments Clone_base_spec : simpl never.


End Clone.

Section Copy.
Context `{RRGS : !refinedrustGS Σ}.
Definition Copy_spec_incl `{Self_rt : !RT} (spec1: ((Copy_spec (Self_rt)))) (spec2: ((Copy_spec (Self_rt)))) : Prop :=
  True.
Instance Copy_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Copy_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Copy_spec `{Self_rt : !RT} : (ScopeBindable ((Copy_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Copy_spec (Self_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((Copy_spec (Self_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_Copy_spec.

Definition Copy_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Copy_spec_attrs ((Self_rt)) (Clone_Self_spec_attrs)))) : (spec_with _ _ (Copy_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Copy_spec _ _ ((Self_rt))).
Arguments Copy_base_spec : simpl never.


End Copy.

Section Clone_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Clone_clone (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_realization: (trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Clone_Self_lfts_inst : prod_vec lft Clone_Self_realization.(trait_ctx_lfts)) (Clone_Self_tys_inst : plist type Clone_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Clone_spec_incl (Clone_Self_realization.(trait_ctx_spec) Clone_Self_lfts_inst Clone_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs Clone_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Clone_Self_realization.(trait_ctx_wf) Clone_Self_lfts_inst Clone_Self_tys_inst π))%I).
  Definition trait_incl_of_Clone_clone_from (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_realization: (trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (Clone_Self_lfts_inst : prod_vec lft Clone_Self_realization.(trait_ctx_lfts)) (Clone_Self_tys_inst : plist type Clone_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Clone_spec_incl (Clone_Self_realization.(trait_ctx_spec) Clone_Self_lfts_inst Clone_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs Clone_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ Clone_Self_realization.(trait_ctx_wf) Clone_Self_lfts_inst Clone_Self_tys_inst π))%I).
End Clone_trait_req_incls.

Section Copy_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Copy_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_REFTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_REFTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Clone_base_spec ((place_rfnRT (T_rt))) (RefSynType) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt))))) ((REFTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(shr_ref ulft_0 T_ty)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_constTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_constTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (loc) (PtrSynType) ((drop_glue_trivial_spec_attrs (loc))) ((constTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[alias_ptr_t]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_mutTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_mutTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (loc) (PtrSynType) ((drop_glue_trivial_spec_attrs (loc))) ((mutTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[alias_ptr_t]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_boolasClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_boolasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (bool) (BoolSynType) ((drop_glue_trivial_spec_attrs (bool))) (boolasClone_spec_attrs))
    -[] -[bool_t]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_charasClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_charasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) (CharSynType) ((drop_glue_trivial_spec_attrs (Z))) (charasClone_spec_attrs))
    -[] -[char_t]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i128asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType I128)) ((drop_glue_trivial_spec_attrs (Z))) (i128asClone_spec_attrs))
    -[] -[(int I128)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i16asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType I16)) ((drop_glue_trivial_spec_attrs (Z))) (i16asClone_spec_attrs))
    -[] -[(int I16)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i32asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType I32)) ((drop_glue_trivial_spec_attrs (Z))) (i32asClone_spec_attrs))
    -[] -[(int I32)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i64asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType I64)) ((drop_glue_trivial_spec_attrs (Z))) (i64asClone_spec_attrs))
    -[] -[(int I64)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_i8asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType I8)) ((drop_glue_trivial_spec_attrs (Z))) (i8asClone_spec_attrs))
    -[] -[(int I8)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_isizeasClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isizeasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType ISize)) ((drop_glue_trivial_spec_attrs (Z))) (isizeasClone_spec_attrs))
    -[] -[(int ISize)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u128asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType U128)) ((drop_glue_trivial_spec_attrs (Z))) (u128asClone_spec_attrs))
    -[] -[(int U128)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u16asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType U16)) ((drop_glue_trivial_spec_attrs (Z))) (u16asClone_spec_attrs))
    -[] -[(int U16)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u32asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType U32)) ((drop_glue_trivial_spec_attrs (Z))) (u32asClone_spec_attrs))
    -[] -[(int U32)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u64asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType U64)) ((drop_glue_trivial_spec_attrs (Z))) (u64asClone_spec_attrs))
    -[] -[(int U64)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_u8asClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType U8)) ((drop_glue_trivial_spec_attrs (Z))) (u8asClone_spec_attrs))
    -[] -[(int U8)]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_usizeasClone_clone  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usizeasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (Z) ((IntSynType USize)) ((drop_glue_trivial_spec_attrs (Z))) (usizeasClone_spec_attrs))
    -[] -[(int USize)]).(Clone_clone_spec)   a b))) <MERGE!>.


Definition trait_incl_of_std_marker_PhantomDataTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_std_marker_PhantomDataTasClone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec ((((core_marker_PhantomData_rt) ((T_rt))))) (((core_marker_PhantomData_sls (T_st)) : syn_type)) ((drop_glue_trivial_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt))))))) ((std_marker_PhantomDataTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty])]).(Clone_clone_spec)   a b))) <MERGE!>.



End specs.
Section REFTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFTasClone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec ((place_rfnRT (T_rt))))) :=
    spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_REFTasClone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec ((place_rfnRT (T_rt))) (RefSynType)) (drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt)))) (REFTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> (shr_ref ulft_0 T_ty) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments REFTasClone_spec : simpl never.

  Program Definition REFTasClone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (place_rfnRT (T_rt)))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[T_ty]) _ _, (REFTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[ulft_0] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (REFTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[ulft_0] -[T_ty]) (spec! ( *[ulft_0]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec (place_rfnRT (T_rt)) RefSynType (drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt)))) (REFTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(shr_ref ulft_0 T_ty)])))).
End REFTasClone_spec.

Section constTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition constTasClone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_constTasClone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (loc) (PtrSynType)) (drop_glue_trivial_spec_attrs (loc)) (constTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> alias_ptr_t : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments constTasClone_spec : simpl never.

  Program Definition constTasClone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) loc)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (constTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition constTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (constTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec loc PtrSynType (drop_glue_trivial_spec_attrs (loc)) (constTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[alias_ptr_t])))).
End constTasClone_spec.

Section constTasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition constTasCopy_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (loc)).
  Arguments constTasCopy_spec : simpl never.

  Program Definition constTasCopy_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) loc)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (constTasCopy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition constTasCopy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (constTasCopy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Copy_base_spec loc PtrSynType (constTasClone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs (loc)) (constTasCopy_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[alias_ptr_t])))).
  Lemma constTasCopy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp loc alias_ptr_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End constTasCopy_spec.

Section mutTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition mutTasClone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_mutTasClone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (loc) (PtrSynType)) (drop_glue_trivial_spec_attrs (loc)) (mutTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> alias_ptr_t : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments mutTasClone_spec : simpl never.

  Program Definition mutTasClone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) loc)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (mutTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition mutTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (mutTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec loc PtrSynType (drop_glue_trivial_spec_attrs (loc)) (mutTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[alias_ptr_t])))).
End mutTasClone_spec.

Section mutTasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition mutTasCopy_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (loc)).
  Arguments mutTasCopy_spec : simpl never.

  Program Definition mutTasCopy_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) loc)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (mutTasCopy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition mutTasCopy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (mutTasCopy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Copy_base_spec loc PtrSynType (mutTasClone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs (loc)) (mutTasCopy_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[alias_ptr_t])))).
  Lemma mutTasCopy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp loc alias_ptr_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End mutTasCopy_spec.

Section boolasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition boolasClone_spec  : (spec_with _ _ (Clone_spec (bool))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_boolasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (bool) (BoolSynType)) (drop_glue_trivial_spec_attrs (bool)) boolasClone_spec_attrs 
             <TY> bool_t : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments boolasClone_spec : simpl never.

  Program Definition boolasClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) bool)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, boolasClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition boolasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), boolasClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec bool BoolSynType (drop_glue_trivial_spec_attrs (bool)) boolasClone_spec_attrs-[] -[bool_t])))).
End boolasClone_spec.

Section boolasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition boolasCopy_spec  : (spec_with _ _ (Copy_spec (bool))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (bool)).
  Arguments boolasCopy_spec : simpl never.

  Program Definition boolasCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) bool)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, boolasCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition boolasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), boolasCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec bool BoolSynType boolasClone_spec_attrs (drop_glue_trivial_spec_attrs (bool)) boolasCopy_spec_attrs-[] -[bool_t])))).
  Lemma boolasCopy_semantic_interp  : (Copy_semantic_interp bool bool_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End boolasCopy_spec.

Section charasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition charasClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_charasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) (CharSynType)) (drop_glue_trivial_spec_attrs (Z)) charasClone_spec_attrs 
             <TY> char_t : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments charasClone_spec : simpl never.

  Program Definition charasClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, charasClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition charasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), charasClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z CharSynType (drop_glue_trivial_spec_attrs (Z)) charasClone_spec_attrs-[] -[char_t])))).
End charasClone_spec.

Section charasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition charasCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments charasCopy_spec : simpl never.

  Program Definition charasCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, charasCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition charasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), charasCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z CharSynType charasClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) charasCopy_spec_attrs-[] -[char_t])))).
  Lemma charasCopy_semantic_interp  : (Copy_semantic_interp Z char_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End charasCopy_spec.

Section i128asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i128asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I128))) (drop_glue_trivial_spec_attrs (Z)) i128asClone_spec_attrs 
             <TY> (int I128) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i128asClone_spec : simpl never.

  Program Definition i128asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i128asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i128asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType I128) (drop_glue_trivial_spec_attrs (Z)) i128asClone_spec_attrs-[] -[(int I128)])))).
End i128asClone_spec.

Section i128asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments i128asCopy_spec : simpl never.

  Program Definition i128asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i128asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i128asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType I128) i128asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i128asCopy_spec_attrs-[] -[(int I128)])))).
  Lemma i128asCopy_semantic_interp  : (Copy_semantic_interp Z (int I128)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i128asCopy_spec.

Section i16asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i16asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I16))) (drop_glue_trivial_spec_attrs (Z)) i16asClone_spec_attrs 
             <TY> (int I16) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i16asClone_spec : simpl never.

  Program Definition i16asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i16asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i16asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType I16) (drop_glue_trivial_spec_attrs (Z)) i16asClone_spec_attrs-[] -[(int I16)])))).
End i16asClone_spec.

Section i16asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments i16asCopy_spec : simpl never.

  Program Definition i16asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i16asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i16asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType I16) i16asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i16asCopy_spec_attrs-[] -[(int I16)])))).
  Lemma i16asCopy_semantic_interp  : (Copy_semantic_interp Z (int I16)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i16asCopy_spec.

Section i32asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i32asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I32))) (drop_glue_trivial_spec_attrs (Z)) i32asClone_spec_attrs 
             <TY> (int I32) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i32asClone_spec : simpl never.

  Program Definition i32asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i32asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i32asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType I32) (drop_glue_trivial_spec_attrs (Z)) i32asClone_spec_attrs-[] -[(int I32)])))).
End i32asClone_spec.

Section i32asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments i32asCopy_spec : simpl never.

  Program Definition i32asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i32asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i32asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType I32) i32asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i32asCopy_spec_attrs-[] -[(int I32)])))).
  Lemma i32asCopy_semantic_interp  : (Copy_semantic_interp Z (int I32)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i32asCopy_spec.

Section i64asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i64asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I64))) (drop_glue_trivial_spec_attrs (Z)) i64asClone_spec_attrs 
             <TY> (int I64) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i64asClone_spec : simpl never.

  Program Definition i64asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i64asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i64asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType I64) (drop_glue_trivial_spec_attrs (Z)) i64asClone_spec_attrs-[] -[(int I64)])))).
End i64asClone_spec.

Section i64asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments i64asCopy_spec : simpl never.

  Program Definition i64asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i64asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i64asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType I64) i64asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i64asCopy_spec_attrs-[] -[(int I64)])))).
  Lemma i64asCopy_semantic_interp  : (Copy_semantic_interp Z (int I64)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i64asCopy_spec.

Section i8asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i8asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I8))) (drop_glue_trivial_spec_attrs (Z)) i8asClone_spec_attrs 
             <TY> (int I8) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments i8asClone_spec : simpl never.

  Program Definition i8asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i8asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i8asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType I8) (drop_glue_trivial_spec_attrs (Z)) i8asClone_spec_attrs-[] -[(int I8)])))).
End i8asClone_spec.

Section i8asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments i8asCopy_spec : simpl never.

  Program Definition i8asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, i8asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition i8asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType I8) i8asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) i8asCopy_spec_attrs-[] -[(int I8)])))).
  Lemma i8asCopy_semantic_interp  : (Copy_semantic_interp Z (int I8)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i8asCopy_spec.

Section isizeasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_isizeasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType ISize))) (drop_glue_trivial_spec_attrs (Z)) isizeasClone_spec_attrs 
             <TY> (int ISize) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments isizeasClone_spec : simpl never.

  Program Definition isizeasClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, isizeasClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition isizeasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType ISize) (drop_glue_trivial_spec_attrs (Z)) isizeasClone_spec_attrs-[] -[(int ISize)])))).
End isizeasClone_spec.

Section isizeasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments isizeasCopy_spec : simpl never.

  Program Definition isizeasCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, isizeasCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition isizeasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType ISize) isizeasClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) isizeasCopy_spec_attrs-[] -[(int ISize)])))).
  Lemma isizeasCopy_semantic_interp  : (Copy_semantic_interp Z (int ISize)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End isizeasCopy_spec.

Section u128asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u128asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U128))) (drop_glue_trivial_spec_attrs (Z)) u128asClone_spec_attrs 
             <TY> (int U128) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u128asClone_spec : simpl never.

  Program Definition u128asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u128asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u128asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType U128) (drop_glue_trivial_spec_attrs (Z)) u128asClone_spec_attrs-[] -[(int U128)])))).
End u128asClone_spec.

Section u128asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments u128asCopy_spec : simpl never.

  Program Definition u128asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u128asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u128asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType U128) u128asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u128asCopy_spec_attrs-[] -[(int U128)])))).
  Lemma u128asCopy_semantic_interp  : (Copy_semantic_interp Z (int U128)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u128asCopy_spec.

Section u16asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u16asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U16))) (drop_glue_trivial_spec_attrs (Z)) u16asClone_spec_attrs 
             <TY> (int U16) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u16asClone_spec : simpl never.

  Program Definition u16asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u16asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u16asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType U16) (drop_glue_trivial_spec_attrs (Z)) u16asClone_spec_attrs-[] -[(int U16)])))).
End u16asClone_spec.

Section u16asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments u16asCopy_spec : simpl never.

  Program Definition u16asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u16asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u16asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType U16) u16asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u16asCopy_spec_attrs-[] -[(int U16)])))).
  Lemma u16asCopy_semantic_interp  : (Copy_semantic_interp Z (int U16)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u16asCopy_spec.

Section u32asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u32asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U32))) (drop_glue_trivial_spec_attrs (Z)) u32asClone_spec_attrs 
             <TY> (int U32) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u32asClone_spec : simpl never.

  Program Definition u32asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u32asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u32asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType U32) (drop_glue_trivial_spec_attrs (Z)) u32asClone_spec_attrs-[] -[(int U32)])))).
End u32asClone_spec.

Section u32asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments u32asCopy_spec : simpl never.

  Program Definition u32asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u32asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u32asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType U32) u32asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u32asCopy_spec_attrs-[] -[(int U32)])))).
  Lemma u32asCopy_semantic_interp  : (Copy_semantic_interp Z (int U32)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u32asCopy_spec.

Section u64asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u64asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U64))) (drop_glue_trivial_spec_attrs (Z)) u64asClone_spec_attrs 
             <TY> (int U64) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u64asClone_spec : simpl never.

  Program Definition u64asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u64asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u64asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType U64) (drop_glue_trivial_spec_attrs (Z)) u64asClone_spec_attrs-[] -[(int U64)])))).
End u64asClone_spec.

Section u64asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments u64asCopy_spec : simpl never.

  Program Definition u64asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u64asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u64asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType U64) u64asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u64asCopy_spec_attrs-[] -[(int U64)])))).
  Lemma u64asCopy_semantic_interp  : (Copy_semantic_interp Z (int U64)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u64asCopy_spec.

Section u8asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u8asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U8))) (drop_glue_trivial_spec_attrs (Z)) u8asClone_spec_attrs 
             <TY> (int U8) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments u8asClone_spec : simpl never.

  Program Definition u8asClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u8asClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u8asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) u8asClone_spec_attrs-[] -[(int U8)])))).
End u8asClone_spec.

Section u8asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments u8asCopy_spec : simpl never.

  Program Definition u8asCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, u8asCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition u8asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType U8) u8asClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) u8asCopy_spec_attrs-[] -[(int U8)])))).
  Lemma u8asCopy_semantic_interp  : (Copy_semantic_interp Z (int U8)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u8asCopy_spec.

Section usizeasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_usizeasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType USize))) (drop_glue_trivial_spec_attrs (Z)) usizeasClone_spec_attrs 
             <TY> (int USize) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments usizeasClone_spec : simpl never.

  Program Definition usizeasClone_realization  : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, usizeasClone_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition usizeasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasClone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec Z (IntSynType USize) (drop_glue_trivial_spec_attrs (Z)) usizeasClone_spec_attrs-[] -[(int USize)])))).
End usizeasClone_spec.

Section usizeasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Arguments usizeasCopy_spec : simpl never.

  Program Definition usizeasCopy_realization  : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) Z)) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, usizeasCopy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition usizeasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasCopy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec Z (IntSynType USize) usizeasClone_spec_attrs (drop_glue_trivial_spec_attrs (Z)) usizeasCopy_spec_attrs-[] -[(int USize)])))).
  Lemma usizeasCopy_semantic_interp  : (Copy_semantic_interp Z (int USize)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End usizeasCopy_spec.

Section std_marker_PhantomDataTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_marker_PhantomDataTasClone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec ((((core_marker_PhantomData_rt) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_std_marker_PhantomDataTasClone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec ((((core_marker_PhantomData_rt) ((T_rt))))) (((core_marker_PhantomData_sls (T_st)) : syn_type))) (drop_glue_trivial_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt)))))) (std_marker_PhantomDataTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> (core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments std_marker_PhantomDataTasClone_spec : simpl never.

  Program Definition std_marker_PhantomDataTasClone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (((core_marker_PhantomData_rt) ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (std_marker_PhantomDataTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition std_marker_PhantomDataTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_marker_PhantomDataTasClone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec (((core_marker_PhantomData_rt) ((T_rt)))) ((core_marker_PhantomData_sls (T_st)) : syn_type) (drop_glue_trivial_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt)))))) (std_marker_PhantomDataTasClone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty])])))).
End std_marker_PhantomDataTasClone_spec.

Section std_marker_PhantomDataTasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_marker_PhantomDataTasCopy_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec ((((core_marker_PhantomData_rt) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ ((((core_marker_PhantomData_rt) ((T_rt)))))).
  Arguments std_marker_PhantomDataTasCopy_spec : simpl never.

  Program Definition std_marker_PhantomDataTasCopy_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) (((core_marker_PhantomData_rt) ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (std_marker_PhantomDataTasCopy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition std_marker_PhantomDataTasCopy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_marker_PhantomDataTasCopy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Copy_base_spec (((core_marker_PhantomData_rt) ((T_rt)))) ((core_marker_PhantomData_sls (T_st)) : syn_type) (std_marker_PhantomDataTasClone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt)))))) (std_marker_PhantomDataTasCopy_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty])])))).
  Lemma std_marker_PhantomDataTasCopy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp (((core_marker_PhantomData_rt) ((T_rt)))) (core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End std_marker_PhantomDataTasCopy_spec.

