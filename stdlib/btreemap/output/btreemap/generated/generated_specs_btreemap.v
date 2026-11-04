From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.btreemap.btreemap Require Export generated_code_btreemap.

Section BTreeMap_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {K_rt : RT} {V_rt : RT} {A_rt : RT}.
  (* Additional parameters *)
  Context `{_CTX0 : !(EqDecision (RT_xt (K_rt)))} `{_CTX1 : !(Countable (RT_xt (K_rt)))}.
  Definition BTreeMap_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(K_rt); (V_rt); (A_rt)] ((type (plist place_rfnRT [(K_rt) : RT; (V_rt) : RT; (A_rt) : RT])))).
  Proof using _CTX0 _CTX1.
    exact (spec! ( *[]) : 0 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), (struct_t (BTreeMap_sls ((ty_syn_type K_ty MetaNone)) ((ty_syn_type V_ty MetaNone)) ((ty_syn_type A_ty MetaNone))) +[(K_ty); (V_ty); (A_ty)])).
  Defined.

  Definition BTreeMap_rt  : RT.
  Proof using K_rt V_rt A_rt _CTX0 _CTX1.
    let __a := (normalized_rt_of_spec_ty (BTreeMap_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent BTreeMap_rt.
  #[global] Typeclasses Transparent BTreeMap_ty.
End BTreeMap_ty.
#[global] Arguments BTreeMap_rt : clear implicits.

#[global] Arguments BTreeMap_rt _ _ _  {_ _ }.

#[global] Arguments BTreeMap_ty : clear implicits.

#[global] Arguments BTreeMap_ty {_ _} _ _ _   {_} {_}.

Section BTreeMap_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {K_rt : RT} {V_rt : RT} {A_rt : RT}.
  (* Additional parameters *)
  Context `{_CTX0 : !(EqDecision (RT_xt (K_rt)))} `{_CTX1 : !(Countable (RT_xt (K_rt)))}.
  Program Definition BTreeMap_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(K_rt); (V_rt); (A_rt)] ((ex_inv_def ((BTreeMap_rt (K_rt) (V_rt) (A_rt)))%type ((directRT (gmap (RT_xt (K_rt)) ((RT_xt (V_rt))))))%type))) :=
    spec! ( *[]) : 0 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (BTreeMap_rt (K_rt) (V_rt) (A_rt))) (_ty_rfn : RT_rt ((directRT (gmap (RT_xt (K_rt)) ((RT_xt (V_rt)))))%type : RT)),
                  let 'M := _ty_rfn in ∃ (k: name_hint_ty "k" (((RT_xt (K_rt))))%Z) (v: name_hint_ty "v" (((RT_xt (V_rt))))%Z) (a: name_hint_ty "a" (((RT_xt (A_rt))))%Z), ⌜inner_rfn = -[#($# k); #($# v); #($# a)]⌝ ∗ True)%I
          (false)
          _
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    intros ? ?; ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    intros ? ?; ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    intros ? ?; ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    intros ? ?; ex_t_solve_persistent.
  Qed.

  Final Obligation.
    intros ? ?; ex_plain_t_solve_shr_mono.
  Qed.

  Definition BTreeMap_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(K_rt); (V_rt); (A_rt)] ((type (((directRT (gmap (RT_xt (K_rt)) ((RT_xt (V_rt))))))%type)))) :=
    spec! ( *[]) : 0 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), ex_plain_t _ _ (BTreeMap_inv_t_inv_spec Allocator_A_spec_attrs Clone_A_spec_attrs -[] -[K_ty; V_ty; A_ty]) (((BTreeMap_ty (K_rt) (V_rt) (A_rt)) (Allocator_A_spec_attrs) (Clone_A_spec_attrs)) -[] -[K_ty; V_ty; A_ty]).
  #[global] Arguments BTreeMap_inv_t_inv_spec : simpl never.

  #[global] Arguments BTreeMap_inv_t : simpl never.

  #[global] Typeclasses Transparent BTreeMap_inv_t.
  Definition BTreeMap_inv_t_rt  : RT.
  Proof using K_rt V_rt A_rt _CTX0 _CTX1.
    let __a := (normalized_rt_of_spec_ty (BTreeMap_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent BTreeMap_inv_t_rt.
End BTreeMap_inv_t.
#[global] Arguments BTreeMap_inv_t_rt : clear implicits.

#[global] Arguments BTreeMap_inv_t_rt _ _ _  {_ _ }.

#[global] Arguments BTreeMap_inv_t : clear implicits.

#[global] Arguments BTreeMap_inv_t {_ _} _ _ _   {_} {_}.

#[global] Arguments BTreeMap_inv_t_inv_spec : clear implicits.

#[global] Arguments BTreeMap_inv_t_inv_spec {_ _} _ _ _   {_} {_}.


Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.


Definition trait_incl_of_BTreeMap_KVA_insert (K_rt: RT) (V_rt: RT) (A_rt: RT) (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) `{!(EqDecision (RT_xt (K_rt)))} `{!(Countable (RT_xt (K_rt)))} (DropGlue_K_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (K_rt) )) (DropGlue_K_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (K_rt))))) (DropGlue_V_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (V_rt) )) (DropGlue_V_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (V_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_realization: (trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (A_rt))))) (PartialEq_K_K_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) )) (PartialEq_K_K_realization: (trait_spec_realization (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (K_rt) (K_rt))))) (Eq_K_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs)) (Eq_K_realization: (trait_spec_realization (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (K_rt))))) (PartialOrd_K_K_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) PartialEq_K_K_spec_attrs)) (PartialOrd_K_K_realization: (trait_spec_realization (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (K_rt) (K_rt))))) (Ord_K_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs Eq_K_spec_attrs PartialOrd_K_K_spec_attrs)) (Ord_K_realization: (trait_spec_realization (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (K_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), (λ π, ((∃ (DropGlue_K_lfts_inst : prod_vec lft DropGlue_K_realization.(trait_ctx_lfts)) (DropGlue_K_tys_inst : plist type DropGlue_K_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_K_realization.(trait_ctx_spec) DropGlue_K_lfts_inst DropGlue_K_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (K_rt) K_st DropGlue_K_spec_attrs-[] -[K_ty]))⌝ ∗ DropGlue_K_realization.(trait_ctx_wf) DropGlue_K_lfts_inst DropGlue_K_tys_inst π)
    ∗ (∃ (DropGlue_V_lfts_inst : prod_vec lft DropGlue_V_realization.(trait_ctx_lfts)) (DropGlue_V_tys_inst : plist type DropGlue_V_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_V_realization.(trait_ctx_spec) DropGlue_V_lfts_inst DropGlue_V_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (V_rt) V_st DropGlue_V_spec_attrs-[] -[V_ty]))⌝ ∗ DropGlue_V_realization.(trait_ctx_wf) DropGlue_V_lfts_inst DropGlue_V_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
    ∗ (∃ (Clone_A_lfts_inst : prod_vec lft Clone_A_realization.(trait_ctx_lfts)) (Clone_A_tys_inst : plist type Clone_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Clone_spec_incl (Clone_A_realization.(trait_ctx_spec) Clone_A_lfts_inst Clone_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (A_rt) A_st DropGlue_A_spec_attrs Clone_A_spec_attrs-[] -[A_ty]))⌝ ∗ Clone_A_realization.(trait_ctx_wf) Clone_A_lfts_inst Clone_A_tys_inst π)
    ∗ (∃ (PartialEq_K_K_lfts_inst : prod_vec lft PartialEq_K_K_realization.(trait_ctx_lfts)) (PartialEq_K_K_tys_inst : plist type PartialEq_K_K_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialEq_spec_incl (PartialEq_K_K_realization.(trait_ctx_spec) PartialEq_K_K_lfts_inst PartialEq_K_K_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (K_rt) (K_rt) K_st K_st DropGlue_K_spec_attrs DropGlue_K_spec_attrs PartialEq_K_K_spec_attrs-[] -[K_ty; K_ty]))⌝ ∗ PartialEq_K_K_realization.(trait_ctx_wf) PartialEq_K_K_lfts_inst PartialEq_K_K_tys_inst π)
    ∗ (∃ (Eq_K_lfts_inst : prod_vec lft Eq_K_realization.(trait_ctx_lfts)) (Eq_K_tys_inst : plist type Eq_K_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Eq_spec_incl (Eq_K_realization.(trait_ctx_spec) Eq_K_lfts_inst Eq_K_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (K_rt) K_st PartialEq_K_K_spec_attrs DropGlue_K_spec_attrs Eq_K_spec_attrs-[] -[K_ty]))⌝ ∗ Eq_K_realization.(trait_ctx_wf) Eq_K_lfts_inst Eq_K_tys_inst π)
    ∗ (∃ (PartialOrd_K_K_lfts_inst : prod_vec lft PartialOrd_K_K_realization.(trait_ctx_lfts)) (PartialOrd_K_K_tys_inst : plist type PartialOrd_K_K_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl PartialOrd_spec_incl (PartialOrd_K_K_realization.(trait_ctx_spec) PartialOrd_K_K_lfts_inst PartialOrd_K_K_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (K_rt) (K_rt) K_st K_st PartialEq_K_K_spec_attrs DropGlue_K_spec_attrs DropGlue_K_spec_attrs PartialOrd_K_K_spec_attrs-[] -[K_ty; K_ty]))⌝ ∗ PartialOrd_K_K_realization.(trait_ctx_wf) PartialOrd_K_K_lfts_inst PartialOrd_K_K_tys_inst π)
    ∗ (∃ (Ord_K_lfts_inst : prod_vec lft Ord_K_realization.(trait_ctx_lfts)) (Ord_K_tys_inst : plist type Ord_K_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Ord_spec_incl (Ord_K_realization.(trait_ctx_spec) Ord_K_lfts_inst Ord_K_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (K_rt) K_st PartialEq_K_K_spec_attrs Eq_K_spec_attrs PartialOrd_K_K_spec_attrs DropGlue_K_spec_attrs Ord_K_spec_attrs-[] -[K_ty]))⌝ ∗ Ord_K_realization.(trait_ctx_wf) Ord_K_lfts_inst Ord_K_tys_inst π))%I).

Definition type_of_BTreeMap_KVA_insert (K_rt: RT) (V_rt: RT) (A_rt: RT) (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) `{!(EqDecision (RT_xt (K_rt)))} `{!(Countable (RT_xt (K_rt)))} (DropGlue_K_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (K_rt) )) (DropGlue_V_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (V_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (PartialEq_K_K_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) )) (Eq_K_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs)) (PartialOrd_K_K_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) PartialEq_K_K_spec_attrs)) (Ord_K_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs Eq_K_spec_attrs PartialOrd_K_K_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[K_ty; V_ty; A_ty]) : ([(K_rt, K_st); (V_rt, V_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (m, k, v, γ) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) (m, γ) :@: (mut_ref ulft_1 (BTreeMap_inv_t ((K_rt)) ((V_rt)) ((A_rt)) Allocator_A_spec_attrs Clone_A_spec_attrs -[] -[K_ty; V_ty; A_ty])), k :@: K_ty, v :@: V_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, m !! k @ (Option_ty ((V_rt)) -[] -[V_ty]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs γ ((<[k := v]> m)))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
