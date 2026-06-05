From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.btreemap.btreemap Require Export generated_code_btreemap.

Section BTreeMap_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (K_rt : RT) (V_rt : RT) (A_rt : RT).

   (* Additional parameters *)
  Context `{_CTX0 : !(EqDecision (RT_xt (K_rt)))}`{_CTX1 : !(Countable (RT_xt (K_rt)))}.

Definition BTreeMap_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(K_rt); (V_rt); (A_rt)] ((type (plist place_rfnRT [(K_rt) : RT; (V_rt) : RT; (A_rt) : RT])))).
Proof using _CTX0 _CTX1.
  exact (spec! ( *[]) : 0 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), ((struct_t (BTreeMap_sls ((K_ty.(ty_syn_type) (MetaNone))) ((V_ty.(ty_syn_type) (MetaNone))) ((A_ty.(ty_syn_type) (MetaNone)))) +[(K_ty); (V_ty); (A_ty)]))).
Defined.

Definition BTreeMap_rt  : RT.
Proof using K_rt V_rt A_rt _CTX0 _CTX1.
  let __a := (normalized_rt_of_spec_ty (BTreeMap_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent BTreeMap_ty.
#[global] Typeclasses Transparent BTreeMap_rt.
End BTreeMap_ty.
Global Arguments BTreeMap_rt : clear implicits.
Global Arguments BTreeMap_rt _ _ _  {_ _ }.
Section BTreeMap_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (K_rt : RT) (V_rt : RT) (A_rt : RT).
   (* Additional parameters *)
  Context `{_CTX0 : !(EqDecision (RT_xt (K_rt)))}`{_CTX1 : !(Countable (RT_xt (K_rt)))}.

  Program Definition BTreeMap_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [K_rt; V_rt; A_rt] (ex_inv_def ((BTreeMap_rt (K_rt) (V_rt) (A_rt)))%type ((directRT (gmap (RT_xt (K_rt)) ((RT_xt (V_rt))))))%type) := spec! ( *[]) : 0 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((directRT (gmap (RT_xt (K_rt)) ((RT_xt (V_rt)))))%type : RT)),
            let 'M := _ty_rfn in ∃ (k: name_hint_ty "k" (_)%Z) (v: name_hint_ty "v" (_)%Z) (a: name_hint_ty "a" (_)%Z), ⌜inner_rfn = -[#(k); #(v); #(a)]⌝ ∗ True)%I
    (true)
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. intros ? ?; ex_plain_t_solve_shr_mono. Qed.

  Definition BTreeMap_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [K_rt; V_rt; A_rt] (type ((directRT (gmap (RT_xt (K_rt)) ((RT_xt (V_rt))))))%type) :=
    spec! ( *[]) : 0 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), ex_plain_t _ _ (BTreeMap_inv_t_inv_spec Allocator_A_spec_attrs Clone_A_spec_attrs -[] -[K_ty; V_ty; A_ty]) (((BTreeMap_ty (K_rt) (V_rt) (A_rt)) (Allocator_A_spec_attrs) (Clone_A_spec_attrs)) -[] -[K_ty; V_ty; A_ty]).
Global Arguments BTreeMap_inv_t_inv_spec : simpl never.
Global Arguments BTreeMap_inv_t : simpl never.
  Global Typeclasses Transparent BTreeMap_inv_t.
  Definition BTreeMap_inv_t_rt : RT.
  Proof using K_rt V_rt A_rt _CTX0 _CTX1. let __a := normalized_rt_of_spec_ty BTreeMap_inv_t in exact __a. Defined.
  Global Typeclasses Transparent BTreeMap_inv_t_rt.
End BTreeMap_inv_t.
Global Arguments BTreeMap_inv_t_rt : clear implicits.
Global Arguments BTreeMap_inv_t_rt _ _ _  {_ _ }.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.


Definition trait_incl_of_BTreeMap_KVA_insert (K_rt: RT) (V_rt: RT) (A_rt: RT) (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) `{!(EqDecision (RT_xt (K_rt)))} `{!(Countable (RT_xt (K_rt)))} (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (A_rt)))) (PartialEq_K_K_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) )) (PartialEq_K_K_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (K_rt) (K_rt)))) (Eq_K_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs)) (Eq_K_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (K_rt)))) (PartialOrd_K_K_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) PartialEq_K_K_spec_attrs)) (PartialOrd_K_K_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (K_rt) (K_rt)))) (Ord_K_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs Eq_K_spec_attrs PartialOrd_K_K_spec_attrs)) (Ord_K_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (K_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[K_ty; V_ty; A_ty]) : ([K_rt; V_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty]))) ∧ (trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (A_rt) A_st Clone_A_spec_attrs-[] -[A_ty]))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_K_K_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (K_rt) (K_rt) K_st K_st PartialEq_K_K_spec_attrs-[] -[K_ty; K_ty]))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_K_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (K_rt) K_st PartialEq_K_K_spec_attrs Eq_K_spec_attrs-[] -[K_ty]))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_K_K_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (K_rt) (K_rt) K_st K_st PartialEq_K_K_spec_attrs PartialOrd_K_K_spec_attrs-[] -[K_ty; K_ty]))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_K_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (K_rt) K_st PartialEq_K_K_spec_attrs Eq_K_spec_attrs PartialOrd_K_K_spec_attrs Ord_K_spec_attrs-[] -[K_ty])))).

Definition type_of_BTreeMap_KVA_insert (K_rt: RT) (V_rt: RT) (A_rt: RT) (K_st: syn_type) (V_st: syn_type) (A_st: syn_type) `{!(EqDecision (RT_xt (K_rt)))} `{!(Countable (RT_xt (K_rt)))} (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (PartialEq_K_K_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) )) (Eq_K_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs)) (PartialOrd_K_K_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (K_rt) (K_rt) PartialEq_K_K_spec_attrs)) (Ord_K_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (K_rt) PartialEq_K_K_spec_attrs Eq_K_spec_attrs PartialOrd_K_K_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[K_ty; V_ty; A_ty]) : ([(K_rt, K_st); (V_rt, V_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (m, k, v, γ) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) (m, γ) :@: (mut_ref ulft_1 (BTreeMap_inv_t ((K_rt)) ((V_rt)) ((A_rt)) Allocator_A_spec_attrs Clone_A_spec_attrs -[] -[K_ty; V_ty; A_ty])), k :@: K_ty, v :@: V_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, m !! k @ (Option_ty ((V_rt)) -[] -[V_ty]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs γ ((<[k := v]> m)))).



End specs.
