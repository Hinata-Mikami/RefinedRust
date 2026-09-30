From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.index.index Require Export generated_code_index.

Definition Index_IndexProj_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Idx_rt: RT) (Output_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (Idx_rt)) → (RT_xt (Output_rt)) → Prop).
Record Index_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Idx_rt : !RT} `{Output_rt : !RT} : Type := mk_Index_spec_attrs {
  Index_IndexProj  : (Index_IndexProj_sig (Self_rt) (Idx_rt) (Output_rt));
}.
#[global] Arguments Index_spec_attrs : clear implicits.

#[global] Arguments Index_spec_attrs {_ _}.

#[global] Arguments mk_Index_spec_attrs  {_} {_} {_} {_} {_}.


Definition IndexMut_IndexMutInj_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Idx_rt: RT) (Index_Self_Idx_Output_rt: RT) (Index_Self_Idx_spec_attrs: (Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) )) :=
  ((RT_xt (Self_rt)) → (RT_xt (Idx_rt)) → gname → (Self_rt)).
Record IndexMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Idx_rt : !RT} `{Index_Self_Idx_Output_rt : !RT} `{Index_Self_Idx_spec_attrs : !(Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) )} : Type := mk_IndexMut_spec_attrs {
  IndexMut_IndexMutInj  : (IndexMut_IndexMutInj_sig (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) (Index_Self_Idx_spec_attrs));
}.
#[global] Arguments IndexMut_spec_attrs : clear implicits.

#[global] Arguments IndexMut_spec_attrs {_ _}.

#[global] Arguments mk_IndexMut_spec_attrs  {_} {_} {_} {_} {_} {_}.


Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Record Index_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Idx_rt : !RT} `{Output_rt : !RT} : Type := mk_Index_spec {
  Index_index_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments Index_spec : clear implicits.

#[global] Arguments Index_spec {_ _}.


Record IndexMut_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Idx_rt : !RT} `{Index_Self_Idx_Output_rt : !RT} : Type := mk_IndexMut_spec {
  IndexMut_index_mut_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments IndexMut_spec : clear implicits.

#[global] Arguments IndexMut_spec {_ _}.


Section Index.
Context `{RRGS : !refinedrustGS Σ}.
Definition Index_spec_incl `{Self_rt : !RT} `{Idx_rt : !RT} `{Output_rt : !RT} (spec1: ((Index_spec (Self_rt) (Idx_rt) (Output_rt)))) (spec2: ((Index_spec (Self_rt) (Idx_rt) (Output_rt)))) : Prop :=
  ((function_subtype (spec1.(Index_index_spec)) (spec2.(Index_index_spec)))).
Instance Index_spec_incl_preorder `{Self_rt : !RT} `{Idx_rt : !RT} `{Output_rt : !RT} : (PreOrder (Index_spec_incl (Self_rt := Self_rt) (Idx_rt := Idx_rt) (Output_rt := Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Index_spec `{Self_rt : !RT} `{Idx_rt : !RT} `{Output_rt : !RT} : (ScopeBindable ((Index_spec (Self_rt) (Idx_rt) (Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Index_spec (Self_rt) (Idx_rt) (Output_rt)))) :=
      {|
        Index_index_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Index_index_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Index_spec (Self_rt) (Idx_rt) (Output_rt)))) :=
      {|
        Index_index_spec  :=
          (scope_add_elctx (E) (s.(Index_index_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Index_spec.

Definition Index_index_base_spec (Self_rt: RT) (Idx_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Idx_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_SelfasIndexIdx_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (Index_Self_Idx_spec_attrs: (Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Output_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Idx_ty; Output_ty]) : ([(Self_rt, Self_st); (Idx_rt, Idx_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, index) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), index :@: Idx_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (shr_ref ulft_1 Output_ty);
      (* postcondition *) (λ π : thread_id, (⌜(Index_Self_Idx_spec_attrs.(Index_IndexProj) self index ret)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition Index_base_spec (Self_rt: RT) (Idx_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Idx_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_SelfasIndexIdx_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (_ATTRS: ((Index_spec_attrs ((Self_rt)) ((Idx_rt)) ((Output_rt))))) : (spec_with _ _ (Index_spec ((Self_rt)) ((Idx_rt)) ((Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Idx_ty; Output_ty]) : ([Self_rt; Idx_rt; Output_rt] : list RT), {|
      Index_index_spec  :=
        (Index_index_base_spec ((Self_rt)) ((Idx_rt)) ((Output_rt)) (Self_st) (Idx_st) (Output_st)) DropGlue_Self_spec_attrs DropGlue_Idx_spec_attrs DropGlue_SelfasIndexIdx_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Idx_ty <TY> Output_ty : (spec_with 1 [] fn_spec);
    |}
.
Arguments Index_base_spec : simpl never.


End Index.

Section IndexMut.
Context `{RRGS : !refinedrustGS Σ}.
Definition IndexMut_spec_incl `{Self_rt : !RT} `{Idx_rt : !RT} `{Index_Self_Idx_Output_rt : !RT} (spec1: ((IndexMut_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt)))) (spec2: ((IndexMut_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt)))) : Prop :=
  ((function_subtype (spec1.(IndexMut_index_mut_spec)) (spec2.(IndexMut_index_mut_spec)))).
Instance IndexMut_spec_incl_preorder `{Self_rt : !RT} `{Idx_rt : !RT} `{Index_Self_Idx_Output_rt : !RT} : (PreOrder (IndexMut_spec_incl (Self_rt := Self_rt) (Idx_rt := Idx_rt) (Index_Self_Idx_Output_rt := Index_Self_Idx_Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_IndexMut_spec `{Self_rt : !RT} `{Idx_rt : !RT} `{Index_Self_Idx_Output_rt : !RT} : (ScopeBindable ((IndexMut_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((IndexMut_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt)))) :=
      {|
        IndexMut_index_mut_spec  :=
          (scope_add_typarams (rts) (tys) (s.(IndexMut_index_mut_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((IndexMut_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt)))) :=
      {|
        IndexMut_index_mut_spec  :=
          (scope_add_elctx (E) (s.(IndexMut_index_mut_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_IndexMut_spec.

Definition IndexMut_index_mut_base_spec (Self_rt: RT) (Idx_rt: RT) (Index_Self_Idx_Output_rt: RT) (Self_st: syn_type) (Idx_st: syn_type) (Index_Self_Idx_Output_st: syn_type) (Index_Self_Idx_spec_attrs: (Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_SelfasIndexIdx_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Index_Self_Idx_Output_rt) )) (IndexMut_Self_Idx_spec_attrs: (IndexMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) Index_Self_Idx_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Idx_ty; Index_Self_Idx_Output_ty]) : ([(Self_rt, Self_st); (Idx_rt, Idx_st); (Index_Self_Idx_Output_rt, Index_Self_Idx_Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, index) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), index :@: Idx_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γi, ret) : ((_ * _)), (ret, γi) @ (mut_ref ulft_1 Index_Self_Idx_Output_ty);
      (* postcondition *) (λ π : thread_id, (⌜(Index_Self_Idx_spec_attrs.(Index_IndexProj) self.cur index ret)%Z⌝)
      ∗ (gvar_pobs self.ghost (#(IndexMut_Self_Idx_spec_attrs.(IndexMut_IndexMutInj) self.cur index γi)))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition IndexMut_base_spec (Self_rt: RT) (Idx_rt: RT) (Index_Self_Idx_Output_rt: RT) (Self_st: syn_type) (Idx_st: syn_type) (Index_Self_Idx_Output_st: syn_type) (Index_Self_Idx_spec_attrs: (Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_SelfasIndexIdx_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Index_Self_Idx_Output_rt) )) (_ATTRS: ((IndexMut_spec_attrs ((Self_rt)) ((Idx_rt)) ((Index_Self_Idx_Output_rt)) (Index_Self_Idx_spec_attrs)))) : (spec_with _ _ (IndexMut_spec ((Self_rt)) ((Idx_rt)) ((Index_Self_Idx_Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Idx_ty; Index_Self_Idx_Output_ty]) : ([Self_rt; Idx_rt; Index_Self_Idx_Output_rt] : list RT), {|
      IndexMut_index_mut_spec  :=
        (IndexMut_index_mut_base_spec ((Self_rt)) ((Idx_rt)) ((Index_Self_Idx_Output_rt)) (Self_st) (Idx_st) (Index_Self_Idx_Output_st)) Index_Self_Idx_spec_attrs DropGlue_Self_spec_attrs DropGlue_Idx_spec_attrs DropGlue_SelfasIndexIdx_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Idx_ty <TY> Index_Self_Idx_Output_ty : (spec_with 1 [] fn_spec);
    |}
.
Arguments IndexMut_base_spec : simpl never.


End IndexMut.

Section Index_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Index_index (Self_rt: RT) (Idx_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Idx_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_Idx_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Idx_rt))))) (DropGlue_SelfasIndexIdx_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (DropGlue_SelfasIndexIdx_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt))))) (Index_Self_Idx_spec_attrs: (Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Output_rt) )) (Index_Self_Idx_realization: (trait_spec_realization (spec_with 0 [] (Index_spec (RRGS:=RRGS) (Self_rt) (Idx_rt) (Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Idx_ty; Output_ty]) : ([Self_rt; Idx_rt; Output_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Idx_lfts_inst : prod_vec lft DropGlue_Idx_realization.(trait_ctx_lfts)) (DropGlue_Idx_tys_inst : plist type DropGlue_Idx_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Idx_realization.(trait_ctx_spec) DropGlue_Idx_lfts_inst DropGlue_Idx_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Idx_rt) Idx_st DropGlue_Idx_spec_attrs-[] -[Idx_ty]))⌝ ∗ DropGlue_Idx_realization.(trait_ctx_wf) DropGlue_Idx_lfts_inst DropGlue_Idx_tys_inst π)
      ∗ (∃ (DropGlue_SelfasIndexIdx_Output_lfts_inst : prod_vec lft DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_lfts)) (DropGlue_SelfasIndexIdx_Output_tys_inst : plist type DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_spec) DropGlue_SelfasIndexIdx_Output_lfts_inst DropGlue_SelfasIndexIdx_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st DropGlue_SelfasIndexIdx_Output_spec_attrs-[] -[Output_ty]))⌝ ∗ DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_wf) DropGlue_SelfasIndexIdx_Output_lfts_inst DropGlue_SelfasIndexIdx_Output_tys_inst π)
      ∗ (∃ (Index_Self_Idx_lfts_inst : prod_vec lft Index_Self_Idx_realization.(trait_ctx_lfts)) (Index_Self_Idx_tys_inst : plist type Index_Self_Idx_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Index_spec_incl (Index_Self_Idx_realization.(trait_ctx_spec) Index_Self_Idx_lfts_inst Index_Self_Idx_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Index_base_spec (Self_rt) (Idx_rt) (Output_rt) Self_st Idx_st Output_st DropGlue_Self_spec_attrs DropGlue_Idx_spec_attrs DropGlue_SelfasIndexIdx_Output_spec_attrs Index_Self_Idx_spec_attrs-[] -[Self_ty; Idx_ty; Output_ty]))⌝ ∗ Index_Self_Idx_realization.(trait_ctx_wf) Index_Self_Idx_lfts_inst Index_Self_Idx_tys_inst π))%I).
End Index_trait_req_incls.

Section IndexMut_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_IndexMut_index_mut (Self_rt: RT) (Idx_rt: RT) (Index_Self_Idx_Output_rt: RT) (Self_st: syn_type) (Idx_st: syn_type) (Index_Self_Idx_Output_st: syn_type) (Index_Self_Idx_spec_attrs: (Index_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) )) (Index_Self_Idx_realization: (trait_spec_realization (spec_with 0 [] (Index_spec (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_Idx_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Idx_rt))))) (DropGlue_SelfasIndexIdx_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Index_Self_Idx_Output_rt) )) (DropGlue_SelfasIndexIdx_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Index_Self_Idx_Output_rt))))) (IndexMut_Self_Idx_spec_attrs: (IndexMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) Index_Self_Idx_spec_attrs)) (IndexMut_Self_Idx_realization: (trait_spec_realization (spec_with 0 [] (IndexMut_spec (RRGS:=RRGS) (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Idx_ty; Index_Self_Idx_Output_ty]) : ([Self_rt; Idx_rt; Index_Self_Idx_Output_rt] : list RT), (λ π, ((∃ (Index_Self_Idx_lfts_inst : prod_vec lft Index_Self_Idx_realization.(trait_ctx_lfts)) (Index_Self_Idx_tys_inst : plist type Index_Self_Idx_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Index_spec_incl (Index_Self_Idx_realization.(trait_ctx_spec) Index_Self_Idx_lfts_inst Index_Self_Idx_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Index_base_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) Self_st Idx_st Index_Self_Idx_Output_st DropGlue_Self_spec_attrs DropGlue_Idx_spec_attrs DropGlue_SelfasIndexIdx_Output_spec_attrs Index_Self_Idx_spec_attrs-[] -[Self_ty; Idx_ty; Index_Self_Idx_Output_ty]))⌝ ∗ Index_Self_Idx_realization.(trait_ctx_wf) Index_Self_Idx_lfts_inst Index_Self_Idx_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Idx_lfts_inst : prod_vec lft DropGlue_Idx_realization.(trait_ctx_lfts)) (DropGlue_Idx_tys_inst : plist type DropGlue_Idx_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Idx_realization.(trait_ctx_spec) DropGlue_Idx_lfts_inst DropGlue_Idx_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Idx_rt) Idx_st DropGlue_Idx_spec_attrs-[] -[Idx_ty]))⌝ ∗ DropGlue_Idx_realization.(trait_ctx_wf) DropGlue_Idx_lfts_inst DropGlue_Idx_tys_inst π)
      ∗ (∃ (DropGlue_SelfasIndexIdx_Output_lfts_inst : prod_vec lft DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_lfts)) (DropGlue_SelfasIndexIdx_Output_tys_inst : plist type DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_spec) DropGlue_SelfasIndexIdx_Output_lfts_inst DropGlue_SelfasIndexIdx_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Index_Self_Idx_Output_rt) Index_Self_Idx_Output_st DropGlue_SelfasIndexIdx_Output_spec_attrs-[] -[Index_Self_Idx_Output_ty]))⌝ ∗ DropGlue_SelfasIndexIdx_Output_realization.(trait_ctx_wf) DropGlue_SelfasIndexIdx_Output_lfts_inst DropGlue_SelfasIndexIdx_Output_tys_inst π)
      ∗ (∃ (IndexMut_Self_Idx_lfts_inst : prod_vec lft IndexMut_Self_Idx_realization.(trait_ctx_lfts)) (IndexMut_Self_Idx_tys_inst : plist type IndexMut_Self_Idx_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl IndexMut_spec_incl (IndexMut_Self_Idx_realization.(trait_ctx_spec) IndexMut_Self_Idx_lfts_inst IndexMut_Self_Idx_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), IndexMut_base_spec (Self_rt) (Idx_rt) (Index_Self_Idx_Output_rt) Self_st Idx_st Index_Self_Idx_Output_st Index_Self_Idx_spec_attrs DropGlue_Self_spec_attrs DropGlue_Idx_spec_attrs DropGlue_SelfasIndexIdx_Output_spec_attrs IndexMut_Self_Idx_spec_attrs-[] -[Self_ty; Idx_ty; Index_Self_Idx_Output_ty]))⌝ ∗ IndexMut_Self_Idx_realization.(trait_ctx_wf) IndexMut_Self_Idx_lfts_inst IndexMut_Self_Idx_tys_inst π))%I).
End IndexMut_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.




End specs.
