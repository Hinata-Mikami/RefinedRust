From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced Require Export generated_code_ptr_advanced.

Section nonnull_NonNull_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition nonnull_NonNull_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [loc : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (nonnull_NonNull_sls ((ty_syn_type T_ty MetaNone))) +[(alias_ptr_t)])).
  Defined.

  Definition nonnull_NonNull_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (nonnull_NonNull_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent nonnull_NonNull_rt.
  #[global] Typeclasses Transparent nonnull_NonNull_ty.
End nonnull_NonNull_ty.
#[global] Arguments nonnull_NonNull_rt : clear implicits.

#[global] Arguments nonnull_NonNull_ty : clear implicits.

#[global] Arguments nonnull_NonNull_ty {_ _} _  .

Section nonnull_NonNull_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition nonnull_NonNull_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def ((nonnull_NonNull_rt (T_rt)))%type ((loc))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (nonnull_NonNull_rt (T_rt))) (_ty_rfn : RT_rt ((loc)%type : RT)),
                  let 'l := _ty_rfn in ⌜inner_rfn = -[#(l)]⌝ ∗ ⌜(l.(loc_a) ≠ 0)%Z⌝ ∗ True)%I
          (true)
          _
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Final Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition nonnull_NonNull_inv_t  : (spec_with 0 [(T_rt)] ((type (((loc))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (nonnull_NonNull_inv_t_inv_spec  -[] -[T_ty]) ((nonnull_NonNull_ty (T_rt)) -[] -[T_ty]).
  #[global] Arguments nonnull_NonNull_inv_t_inv_spec : simpl never.

  #[global] Arguments nonnull_NonNull_inv_t : simpl never.

  #[global] Typeclasses Transparent nonnull_NonNull_inv_t.
  Definition nonnull_NonNull_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (nonnull_NonNull_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent nonnull_NonNull_inv_t_rt.
End nonnull_NonNull_inv_t.
#[global] Arguments nonnull_NonNull_inv_t_rt : clear implicits.

#[global] Arguments nonnull_NonNull_inv_t : clear implicits.

#[global] Arguments nonnull_NonNull_inv_t {_ _} _  .

#[global] Arguments nonnull_NonNull_inv_t_inv_spec : clear implicits.

#[global] Arguments nonnull_NonNull_inv_t_inv_spec {_ _} _  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition nonnull_NonNullTasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section unique_Unique_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition unique_Unique_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [((nonnull_NonNull_inv_t_rt ((T_rt)))) : RT; (((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (unique_Unique_sls ((ty_syn_type T_ty MetaNone))) +[((nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty])); ((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))])).
  Defined.

  Definition unique_Unique_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (unique_Unique_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent unique_Unique_rt.
  #[global] Typeclasses Transparent unique_Unique_ty.
End unique_Unique_ty.
#[global] Arguments unique_Unique_rt : clear implicits.

#[global] Arguments unique_Unique_ty : clear implicits.

#[global] Arguments unique_Unique_ty {_ _} _  .

Section unique_Unique_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition unique_Unique_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def ((unique_Unique_rt (T_rt)))%type ((loc))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (unique_Unique_rt (T_rt))) (_ty_rfn : RT_rt ((loc)%type : RT)),
                  let 'l := _ty_rfn in ⌜inner_rfn = -[#(l); #(tt)]⌝ ∗ True)%I
          (true)
          _
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Final Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition unique_Unique_inv_t  : (spec_with 0 [(T_rt)] ((type (((loc))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (unique_Unique_inv_t_inv_spec  -[] -[T_ty]) ((unique_Unique_ty (T_rt)) -[] -[T_ty]).
  #[global] Arguments unique_Unique_inv_t_inv_spec : simpl never.

  #[global] Arguments unique_Unique_inv_t : simpl never.

  #[global] Typeclasses Transparent unique_Unique_inv_t.
  Definition unique_Unique_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (unique_Unique_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent unique_Unique_inv_t_rt.
End unique_Unique_inv_t.
#[global] Arguments unique_Unique_inv_t_rt : clear implicits.

#[global] Arguments unique_Unique_inv_t : clear implicits.

#[global] Arguments unique_Unique_inv_t {_ _} _  .

#[global] Arguments unique_Unique_inv_t_inv_spec : clear implicits.

#[global] Arguments unique_Unique_inv_t_inv_spec {_ _} _  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition nonnull_NonNullTasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt))))) ((nonnull_NonNullTasstd_clone_Clone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unique_UniqueTasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs (((unique_Unique_inv_t_rt ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition unique_UniqueTasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs (((unique_Unique_inv_t_rt ((T_rt))))) ((unique_UniqueTasstd_clone_Clone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance NonNull_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper.
      + solve_proper.
    - cbn. apply _.
  Qed.
  Global Instance NonNull_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.

  Global Program Instance NonNull_inv_t_dep_lft_mor rts (T_rt : RT) (T : mut_types rts → type T_rt) :
    DepLftMorphism ∅ (λ x : mut_types rts, nonnull_NonNull_inv_t T_rt *[] *[(T x)]) :=
      mk_dep_lft_morph_const _ static [] _ _.
  Next Obligation.
    intros. simpl.
    iIntros (?).
    repeat rewrite !ty_lfts_unfold/=.
    iApply lft_equiv_refl.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    done.
  Qed.

  Global Instance Unique_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper.
      + solve_proper.
    - cbn; apply _.
  Qed.
  Global Instance Unique_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.

  Global Program Instance Unique_inv_t_dep_lft_mor rts (rt : RT) (T : mut_types rts → type rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, unique_Unique_inv_t rt *[] *[(T x)]) :=
    λ Ht,
      dep_lft_morph_make_id _ _ _ Ht _ _.
  Next Obligation.
    intros. rewrite /lifecycle_lfts/=.
    repeat rewrite !ty_lfts_unfold/=.
    rewrite !right_id//.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    rewrite !right_id//.
  Qed.
End contractive.
Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_nonnull_NonNullTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNullTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))) ((nonnull_NonNull_st (T_st))) ((drop_glue_trivial_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt))))))) ((nonnull_NonNullTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_unique_UniqueTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_unique_UniqueTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (((unique_Unique_inv_t_rt ((T_rt))))) ((unique_Unique_st (T_st))) ((drop_glue_trivial_spec_attrs (((unique_Unique_inv_t_rt ((T_rt))))))) ((unique_UniqueTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(unique_Unique_inv_t ((T_rt))  -[] -[T_ty])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_nonnull_NonNull_T_as_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_as_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x, self) : ((((RT_xt (T_rt))) * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_2)]);
      (* args......... *) self :@: (mut_ref ulft_2 (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, (self.cur ◁ₗ[π, Owned] # ($# x) @ ◁ T_ty)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γ) : ((_)), (x, γ) @ (mut_ref ulft_a T_ty);
      (* postcondition *) (λ π : thread_id, (self.cur ◁ₗ[π, Owned] PlaceGhost γ @ BlockedLtype T_ty ulft_a)
      ∗ (gvar_pobs self.ghost (self.cur))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_as_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_as_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_as_ref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_as_ref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x, self) : ((((RT_xt (T_rt))) * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_a); (ϝ, ulft_2)]);
      (* args......... *) self :@: (shr_ref ulft_2 (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, Owned] # ($# x) @ ◁ T_ty)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ (shr_ref ulft_a T_ty);
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, Owned] # ($# x) @ ShrBlockedLtype T_ty ulft_a)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) (DropGlue_U_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_U_lfts_inst : prod_vec lft DropGlue_U_realization.(trait_ctx_lfts)) (DropGlue_U_tys_inst : plist type DropGlue_U_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_U_realization.(trait_ctx_spec) DropGlue_U_lfts_inst DropGlue_U_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (U_rt) U_st DropGlue_U_spec_attrs-[] -[U_ty]))⌝ ∗ DropGlue_U_realization.(trait_ctx_wf) DropGlue_U_lfts_inst DropGlue_U_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; U_ty]) : ([(T_rt, T_st); (U_rt, U_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (nonnull_NonNull_inv_t ((U_rt))  -[] -[U_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_is_aligned (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_is_aligned (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (self `aligned_to` (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)))) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_is_aligned_to (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_is_aligned_to (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]), align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (self `aligned_to` Z.to_nat align) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if decide (ptr.(loc_a) = 0) then None else Some ptr @ (Option_ty (((nonnull_NonNull_inv_t_rt ((T_rt))))) -[] -[(nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty])]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_new_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_new_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜(ptr.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ptr @ (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, self) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_ops ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, self) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_ops ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_write (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_write (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, val) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]), val :@: T_ty;
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, Owned] #($# val) @ (◁ T_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_nonnull_NonNull_T_write_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_nonnull_NonNull_T_write_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, val) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]), val :@: T_ty;
      (* precondition. *) (λ π : thread_id, (self ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (self ◁ₗ[π, Owned] #($# val) @ (◁ T_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_unique_Unique_T_as_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_unique_Unique_T_as_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (unique_Unique_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_unique_Unique_T_dangling (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_unique_Unique_T_dangling (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ (unique_Unique_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit UnitSynType))
      ∗ (freeable_nz l 0 1 HeapAlloc)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_unique_Unique_T_new_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_unique_Unique_T_new_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜(ptr.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ptr @ (unique_Unique_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).




End specs.
Section nonnull_NonNullTasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition nonnull_NonNullTasstd_clone_Clone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_nonnull_NonNullTasstd_clone_Clone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))) ((nonnull_NonNull_st (T_st)))) (drop_glue_trivial_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt)))))) (nonnull_NonNullTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments nonnull_NonNullTasstd_clone_Clone_spec : simpl never.

  Program Definition nonnull_NonNullTasstd_clone_Clone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) ((nonnull_NonNull_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (nonnull_NonNullTasstd_clone_Clone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition nonnull_NonNullTasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (nonnull_NonNullTasstd_clone_Clone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec ((nonnull_NonNull_inv_t_rt ((T_rt)))) (nonnull_NonNull_st (T_st)) (drop_glue_trivial_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt)))))) (nonnull_NonNullTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty])])))).
End nonnull_NonNullTasstd_clone_Clone_spec.

Section nonnull_NonNullTasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition nonnull_NonNullTasstd_marker_Copy_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec (((nonnull_NonNull_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (((nonnull_NonNull_inv_t_rt ((T_rt)))))).
  Arguments nonnull_NonNullTasstd_marker_Copy_spec : simpl never.

  Program Definition nonnull_NonNullTasstd_marker_Copy_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) ((nonnull_NonNull_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (nonnull_NonNullTasstd_marker_Copy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition nonnull_NonNullTasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (nonnull_NonNullTasstd_marker_Copy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Copy_base_spec ((nonnull_NonNull_inv_t_rt ((T_rt)))) (nonnull_NonNull_st (T_st)) (nonnull_NonNullTasstd_clone_Clone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs (((nonnull_NonNull_inv_t_rt ((T_rt)))))) (nonnull_NonNullTasstd_marker_Copy_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty])])))).
  Lemma nonnull_NonNullTasstd_marker_Copy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp ((nonnull_NonNull_inv_t_rt ((T_rt)))) (nonnull_NonNull_inv_t ((T_rt))  -[] -[T_ty])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End nonnull_NonNullTasstd_marker_Copy_spec.

Section unique_UniqueTasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unique_UniqueTasstd_clone_Clone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec (((unique_Unique_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_unique_UniqueTasstd_clone_Clone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((unique_Unique_inv_t_rt ((T_rt))))) ((unique_Unique_st (T_st)))) (drop_glue_trivial_spec_attrs (((unique_Unique_inv_t_rt ((T_rt)))))) (unique_UniqueTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> (unique_Unique_inv_t ((T_rt))  -[] -[T_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments unique_UniqueTasstd_clone_Clone_spec : simpl never.

  Program Definition unique_UniqueTasstd_clone_Clone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) ((unique_Unique_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (unique_UniqueTasstd_clone_Clone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition unique_UniqueTasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (unique_UniqueTasstd_clone_Clone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec ((unique_Unique_inv_t_rt ((T_rt)))) (unique_Unique_st (T_st)) (drop_glue_trivial_spec_attrs (((unique_Unique_inv_t_rt ((T_rt)))))) (unique_UniqueTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(unique_Unique_inv_t ((T_rt))  -[] -[T_ty])])))).
End unique_UniqueTasstd_clone_Clone_spec.

Section unique_UniqueTasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition unique_UniqueTasstd_marker_Copy_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec (((unique_Unique_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (((unique_Unique_inv_t_rt ((T_rt)))))).
  Arguments unique_UniqueTasstd_marker_Copy_spec : simpl never.

  Program Definition unique_UniqueTasstd_marker_Copy_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) ((unique_Unique_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (unique_UniqueTasstd_marker_Copy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition unique_UniqueTasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (unique_UniqueTasstd_marker_Copy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Copy_base_spec ((unique_Unique_inv_t_rt ((T_rt)))) (unique_Unique_st (T_st)) (unique_UniqueTasstd_clone_Clone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs (((unique_Unique_inv_t_rt ((T_rt)))))) (unique_UniqueTasstd_marker_Copy_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(unique_Unique_inv_t ((T_rt))  -[] -[T_ty])])))).
  Lemma unique_UniqueTasstd_marker_Copy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp ((unique_Unique_inv_t_rt ((T_rt)))) (unique_Unique_inv_t ((T_rt))  -[] -[T_ty])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End unique_UniqueTasstd_marker_Copy_spec.

