From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.option.option Require Export generated_code_option.

Section Option_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Section components.
    Definition Option_None_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (Option_None_sls ((ty_syn_type T_ty MetaNone))) +[])).
    Defined.

    Definition Option_None_rt  : RT.
    Proof using T_rt .
      let __a := (normalized_rt_of_spec_ty (Option_None_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Option_None_rt.
    #[global] Typeclasses Transparent Option_None_ty.
    Definition Option_Some_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [(T_rt) : RT])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (Option_Some_sls ((ty_syn_type T_ty MetaNone))) +[(T_ty)])).
    Defined.

    Definition Option_Some_rt  : RT.
    Proof using T_rt .
      let __a := (normalized_rt_of_spec_ty (Option_Some_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Option_Some_rt.
    #[global] Typeclasses Transparent Option_Some_ty.
    Definition Option_enum_rt  :=
      λ rfn : (option (place_rfn (T_rt))), match rfn with | None => Option_None_rt| (Some (x)) => Option_Some_rt end.
    Definition Option_enum_ty  : (spec_with 0 [(T_rt)] (∀ (x: _), (type (Option_enum_rt (x))))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), λ rfn, match rfn as x return type (Option_enum_rt x) with | None => Option_None_ty -[] -[T_ty]| (Some (x)) => Option_Some_ty -[] -[T_ty] end.
    Program Definition Option_enum  : (spec_with 0 [(T_rt)] ((enum ((option (place_rfn (T_rt))))))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_enum
        _
        ((Option_els ((ty_syn_type T_ty MetaNone))))
        (λ rfn, Some (match rfn with | None => "None" | (Some (x)) => "Some" end))
        (Option_enum_rt)
        (Option_enum_ty -[] -[T_ty])
        (λ rfn, match rfn with | None => *[]| (Some (x)) => *[x] end)
        ([("None", mk_enum_tag_sem _ (Option_None_ty -[] -[T_ty]) (λ '( *[]), None)); ("Some", mk_enum_tag_sem _ (Option_Some_ty -[] -[T_ty]) (λ '( *[x]), (Some (x))))])
        _
        _
        _.
    Next Obligation.
      solve_inhabited.
    Defined.

    Next Obligation.
      done.
    Qed.

    Next Obligation.
      solve_mk_enum_tag_consistent.
    Defined.

    Final Obligation.
      solve_mk_enum_tag_inj_roundtrip.
    Defined.

    #[global] Arguments Option_enum : simpl never.

    Definition Option_ty_pre  : (spec_with 0 [(T_rt)] ((type _))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), enum_t (Option_enum -[] -[T_ty]).
    Definition Option_rt_pre  : RT.
    Proof using T_rt .
      let __a := (normalized_rt_of_spec_ty (Option_ty_pre)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Option_rt_pre.
  End components.
  Arguments enum_ty : simpl never.

  Definition Option_ty  : (spec_with 0 [(T_rt)] ((type _))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), enum_t (Option_enum -[] -[T_ty]).
  Definition Option_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (Option_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Option_rt.
End Option_ty.
#[global] Typeclasses Transparent Option_ty.
#[global] Typeclasses Transparent Option_rt.
#[global] Arguments Option_enum : simpl never.

#[global] Arguments Option_rt : clear implicits.

#[global] Arguments Option_ty : clear implicits.

#[global] Arguments Option_ty {_ _} _  .

Global Hint Unfold Option_ty : solve_protected_eq_db.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition OptionTasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs (((Option_rt ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition OptionTasstd_fmt_Debug_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (Debug_T_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Debug_spec_attrs (((Option_rt ((T_rt))))))) :=
  mk_Debug_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition OptionTasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Copy_T_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs (((Option_rt ((T_rt))))) ((OptionTasstd_clone_Clone_spec_attrs ((T_rt)) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition drop_glue_Option_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((DropGlue_spec_attrs (((Option_rt ((T_rt))))))) :=
  {|
    DropGlue_DropGlueUnwind  :=
      (DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind)) : ((DropGlue_DropGlueUnwind_sig (((Option_rt ((T_rt)))))));
  |}
.


End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.

(* NOTE: variance proofs are currently not automatically generated by the frontend *)
Lemma Option_ty_mut_subtype E L {T_rt} (T_ty1 : type T_rt) (T_ty2 : type T_rt) T :
  mut_subtype E L T_ty1 T_ty2 T
  ⊢ mut_subtype E L (Option_ty T_rt <TY> T_ty1 <INST!>) (Option_ty T_rt <TY> T_ty2 <INST!>) T.
Proof.
  rewrite /mut_subtype. iIntros "(%Hsub & $)". iPureIntro.
  apply enum_full_subtype. iIntros (qL) "HL #HE".
  iPoseProof (full_subtype_acc_noend with "HE HL") as "(%Hst & #Hincl)"; first exact Hsub.
  iApply (full_enum_incl_intro E L (Option_enum -[] -[T_ty1])
    (Option_enum -[] -[T_ty2]) (λ _, eq_refl) with "HL HE").
  - simpl. by rewrite Hst.
  - done.
  - done.
  - intros [r|]; simpl; rewrite /Option_Some_ty /Option_None_ty /= Hst;
      apply struct_t_full_subtype; rewrite /hzipl2 /=.
    + constructor; [exact Hsub | constructor].
    + constructor.
Qed.
Definition Option_ty_mut_subtype_inst := [instance @Option_ty_mut_subtype].
Global Existing Instance Option_ty_mut_subtype_inst.

Import EqNotations.
(* NOTE this is a pretty strong lemma, in that we allow strong updates of the type parameter.
   This is needed for the time being, as we might not pick the right lifetimes for T when initializing with None. *)
Lemma Option_ty_weak_subtype_None E L {T_rt1 T_rt2} (T_ty1 : type T_rt1) (T_ty2 : type T_rt2) r2 T :
  (⌜r2 = None⌝ ∗ ⌜st_of T_ty1 MetaNone = st_of T_ty2 MetaNone⌝ ∗ T) ⊢
  weak_subtype E L (None) r2 (Option_ty T_rt1 <TY> T_ty1 <INST!>) (Option_ty T_rt2 <TY> T_ty2 <INST!>) T.
Proof.
  iIntros "(-> & %Hst & HT)".
  iApply weak_subtype_enum_inj.
  rep liRStep. liShow. done.
  Unshelve. rewrite Hst. done.
Qed.
Definition Option_ty_weak_subtype_None_inst := [instance Option_ty_weak_subtype_None].
#[export] Existing Instance Option_ty_weak_subtype_None_inst.
Lemma Option_ty_owned_subtype_None π E L {T_rt1 T_rt2} (T_ty1 : type T_rt1) (T_ty2 : type T_rt2) r2 T :
  (⌜r2 = None⌝ ∗ ⌜st_of T_ty1 MetaNone = st_of T_ty2 MetaNone⌝ ∗ T L) ⊢
  owned_subtype π E L false (None) r2 (Option_ty T_rt1 <TY> T_ty1 <INST!>) (Option_ty T_rt2 <TY> T_ty2 <INST!>) T.
Proof.
  iIntros "(-> & %Hst & HT)".
  iApply owned_subtype_strong_subtype.
  repeat liRStep. liShow. done.
Qed.
Definition Option_ty_owned_subtype_None_inst := [instance @Option_ty_owned_subtype_None].
Global Existing Instance Option_ty_owned_subtype_None_inst.

Global Instance option_contr {rt1 T_rt} (T : type rt1 → type T_rt) :
  TypeContractive T →
  TypeContractive (λ ty, Option_ty T_rt *[] *[T ty]).
Proof.
  intros ?.
  apply enum_t_contr.
  unshelve econstructor.
  - enum_contractive_solve_eq.
  - intros. simpl. by erewrite type_ctr_syn_type.
  - enum_contractive_solve_eq.
  - enum_contractive_solve_eq.
  - intros. simpl.
    eapply (type_contractive_dist _ _ (λ ty, enum_ty (Option_enum -[] -[T ty]) r)); last done.
    destruct r; simpl.
    + apply struct_t_contr; last apply _.
      intros. by erewrite type_ctr_syn_type.
    + apply _.
  - intros. simpl.
    eapply (type_contractive_dist2 _ _ (λ ty, enum_ty (Option_enum -[] -[T ty]) r)); last done.
    destruct r; simpl.
    + apply struct_t_contr; last apply _.
      intros. by erewrite type_ctr_syn_type.
    + apply _.
  - solve_enum_t_contr_op_type.
Qed.
Global Instance option_ne {rt1 T_rt} (T : type rt1 → type T_rt) :
  TypeNonExpansive T →
  TypeNonExpansive (λ ty, Option_ty T_rt *[] *[T ty]).
Proof.
  intros ?.
  apply enum_t_ne.
  unshelve econstructor.
  - enum_contractive_solve_eq.
  - intros. simpl. by erewrite type_ne_syn_type.
  - enum_contractive_solve_eq.
  - enum_contractive_solve_eq.
  - intros. simpl.
    eapply (type_dist_use_ne _ _ _ (λ ty, enum_ty (Option_enum -[] -[T ty]) r)); last done.
    destruct r; simpl.
    + apply struct_t_ne; last apply _.
      intros. by erewrite type_ne_syn_type.
    + apply _.
  - intros. simpl.
    eapply (type_dist2_use_ne _ _ _ (λ ty, enum_ty (Option_enum -[] -[T ty]) r)); last done.
    destruct r; simpl.
    + apply struct_t_ne; last apply _.
      intros. by erewrite type_ne_syn_type.
    + apply _.
  - solve_enum_t_ne_op_type.
Qed.

End extra_specs.
Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_OptionTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_T_realization: (trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (Clone_T_lfts_inst : prod_vec lft Clone_T_realization.(trait_ctx_lfts)) (Clone_T_tys_inst : plist type Clone_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Clone_spec_incl (Clone_T_realization.(trait_ctx_spec) Clone_T_lfts_inst Clone_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (T_rt) T_st DropGlue_T_spec_attrs Clone_T_spec_attrs-[] -[T_ty]))⌝ ∗ Clone_T_realization.(trait_ctx_wf) Clone_T_lfts_inst Clone_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_OptionTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (((Option_rt ((T_rt))))) ((Option_st (T_st))) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((OptionTasstd_clone_Clone_spec_attrs (T_rt) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_Option_T_as_ref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_as_ref (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (Option_ty ((T_rt)) -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (Option_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_1 T_ty)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_filter (T_rt: RT) (P_rt: RT) (T_st: syn_type) (P_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (FnOnce_P_REFT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnOnce_P_REFT_realization: (trait_spec_realization (spec_with 1 [] (FnOnce_spec (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool)))) (DropGlue_P_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (P_rt) )) (DropGlue_P_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (P_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; P_ty]) : ([T_rt; P_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (FnOnce_P_REFT_lfts_inst : prod_vec lft FnOnce_P_REFT_realization.(trait_ctx_lfts)) (FnOnce_P_REFT_tys_inst : plist type FnOnce_P_REFT_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_P_REFT_realization.(trait_ctx_spec) FnOnce_P_REFT_lfts_inst FnOnce_P_REFT_tys_inst) (spec! ( *[_lft_for_0]) : 1 | ( *[]) : ([] : list RT), FnOnce_base_spec (P_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool P_st ((tuple1_sls (RefSynType)) : syn_type) BoolSynType DropGlue_P_spec_attrs (drop_glue_tuple1_spec_attrs ((place_rfnRT (T_rt))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (T_rt)))))) (drop_glue_trivial_spec_attrs (bool)) FnOnce_P_REFT_spec_attrs-[] -[P_ty; (tuple1_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref _lft_for_0 T_ty)]); bool_t]))⌝ ∗ FnOnce_P_REFT_realization.(trait_ctx_wf) FnOnce_P_REFT_lfts_inst FnOnce_P_REFT_tys_inst π)
    ∗ (∃ (DropGlue_P_lfts_inst : prod_vec lft DropGlue_P_realization.(trait_ctx_lfts)) (DropGlue_P_tys_inst : plist type DropGlue_P_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_P_realization.(trait_ctx_spec) DropGlue_P_lfts_inst DropGlue_P_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (P_rt) P_st DropGlue_P_spec_attrs-[] -[P_ty]))⌝ ∗ DropGlue_P_realization.(trait_ctx_wf) DropGlue_P_lfts_inst DropGlue_P_tys_inst π))%I).

Definition type_of_Option_T_filter (T_rt: RT) (P_rt: RT) (T_st: syn_type) (P_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (FnOnce_P_REFT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (DropGlue_P_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (P_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; P_ty]) : ([(T_rt, T_st); (P_rt, P_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (op, self, predicate) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty ((T_rt)) -[] -[T_ty]), predicate :@: P_ty;
      (* precondition. *) (λ π : thread_id, (if_iSome self (λ self, ∃ p, ⌜op = Some p⌝ ∗ FnOnce_P_REFT_spec_attrs.(FnOnce_Pre) π p predicate *[self]))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (Option_ty ((T_rt)) -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (if_iSome ret (λ ret, ⌜self = Some ret⌝ ∗ ∃ p, ⌜op = Some p⌝ ∗ FnOnce_P_REFT_spec_attrs.(FnOnce_Post) π p predicate *[ret] true))
      ∗ (if_iNone ret (if_iNone self (ty_ghost_drop P_ty π ($# predicate)) ∗
                                  if_iSome self (λ x, ∃ p, ⌜op = Some p⌝ ∗ FnOnce_P_REFT_spec_attrs.(FnOnce_Post) π p predicate *[x] false)))) |
      (* unwind cond... *) if_None self DropGlue_P_spec_attrs.(DropGlue_DropGlueUnwind) ∧ if_Some self (λ x, DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) ∨ ∃ p, op = Some p ∧ FnOnce_P_REFT_spec_attrs.(FnOnce_UnwindCondition) predicate p *[x]) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_OptionT_flatten (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_OptionT_flatten (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty (((Option_rt ((T_rt))))) -[] -[(Option_ty ((T_rt)) -[] -[T_ty])]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self ≫= id @ (Option_ty ((T_rt)) -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_is_none (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_is_none (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (Option_ty ((T_rt)) -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (¬ is_Some self) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_is_some (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_is_some (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (Option_ty ((T_rt)) -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_Some self) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_map (T_rt: RT) (U_rt: RT) (F_rt: RT) (T_st: syn_type) (U_st: syn_type) (F_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (FnOnce_F_T_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) )) (FnOnce_F_T_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt))))) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) (DropGlue_U_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty; F_ty]) : ([T_rt; U_rt; F_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (FnOnce_F_T_lfts_inst : prod_vec lft FnOnce_F_T_realization.(trait_ctx_lfts)) (FnOnce_F_T_tys_inst : plist type FnOnce_F_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_T_realization.(trait_ctx_spec) FnOnce_F_T_lfts_inst FnOnce_F_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) F_st ((tuple1_sls (T_st)) : syn_type) U_st DropGlue_F_spec_attrs (drop_glue_tuple1_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) DropGlue_U_spec_attrs FnOnce_F_T_spec_attrs-[] -[F_ty; (tuple1_ty ((T_rt)) -[] -[T_ty]); U_ty]))⌝ ∗ FnOnce_F_T_realization.(trait_ctx_wf) FnOnce_F_T_lfts_inst FnOnce_F_T_tys_inst π)
    ∗ (∃ (DropGlue_U_lfts_inst : prod_vec lft DropGlue_U_realization.(trait_ctx_lfts)) (DropGlue_U_tys_inst : plist type DropGlue_U_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_U_realization.(trait_ctx_spec) DropGlue_U_lfts_inst DropGlue_U_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (U_rt) U_st DropGlue_U_spec_attrs-[] -[U_ty]))⌝ ∗ DropGlue_U_realization.(trait_ctx_wf) DropGlue_U_lfts_inst DropGlue_U_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I).

Definition type_of_Option_T_map (T_rt: RT) (U_rt: RT) (F_rt: RT) (T_st: syn_type) (U_st: syn_type) (F_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (FnOnce_F_T_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) )) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; U_ty; F_ty]) : ([(T_rt, T_st); (U_rt, U_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (op, self, f) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty ((T_rt)) -[] -[T_ty]), f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (if_iNone self (⌜op = None⌝))
        ∗ (if_iSome self (λ self, ∃ p, ⌜op = Some p⌝ ∗ FnOnce_F_T_spec_attrs.(FnOnce_Pre) π p f *[self]))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (Option_ty ((U_rt)) -[] -[U_ty]);
      (* postcondition *) (λ π : thread_id, (if_iNone self (⌜ret = None⌝ ∗ ty_ghost_drop F_ty π ($# f)))
      ∗ (if_iSome self (λ self, ∃ p x, ⌜op = Some p⌝ ∗ ⌜ret = Some x⌝ ∗ FnOnce_F_T_spec_attrs.(FnOnce_Post) π p f *[self] x))) |
      (* unwind cond... *) if_None self DropGlue_F_spec_attrs.(DropGlue_DropGlueUnwind) ∧ if_Some self (λ x, ∃ p, op = Some p ∧ FnOnce_F_T_spec_attrs.(FnOnce_UnwindCondition) f p *[x]) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_ok_or (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_E_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (E_rt) )) (DropGlue_E_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_E_lfts_inst : prod_vec lft DropGlue_E_realization.(trait_ctx_lfts)) (DropGlue_E_tys_inst : plist type DropGlue_E_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_E_realization.(trait_ctx_spec) DropGlue_E_lfts_inst DropGlue_E_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (E_rt) E_st DropGlue_E_spec_attrs-[] -[E_ty]))⌝ ∗ DropGlue_E_realization.(trait_ctx_wf) DropGlue_E_lfts_inst DropGlue_E_tys_inst π))%I).

Definition type_of_Option_T_ok_or (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_E_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (E_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; E_ty]) : ([(T_rt, T_st); (E_rt, E_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, err) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty ((T_rt)) -[] -[T_ty]), err :@: E_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, match self with | Some x => Ok x | None => Err err end @ (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) is_Some self ∧ DropGlue_E_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_unwrap (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_unwrap (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty ((T_rt)) -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, (⌜(destruct_hint self is_Some)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ T_ty;
      (* postcondition *) (λ π : thread_id, (⌜(match self with | Some x => ret = x | None => False end)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_unwrap_or (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_unwrap_or (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, def) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty ((T_rt)) -[] -[T_ty]), def :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, default def self @ T_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) is_Some self ∧ DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_drop_glue_Option (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_drop_glue_Option (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((Option_rt ((T_rt))))) ((Option_st (T_st))) ((drop_glue_Option_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.


Definition trait_incl_of_OptionTasstd_fmt_Debug_fmt (T_rt: RT) (T_st: syn_type) (Debug_T_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (T_rt) )) (Debug_T_realization: (trait_spec_realization (spec_with 0 [] (Debug_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2; ulft_3]) : 3 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (Debug_T_lfts_inst : prod_vec lft Debug_T_realization.(trait_ctx_lfts)) (Debug_T_tys_inst : plist type Debug_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Debug_spec_incl (Debug_T_realization.(trait_ctx_spec) Debug_T_lfts_inst Debug_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Debug_base_spec (T_rt) T_st DropGlue_T_spec_attrs Debug_T_spec_attrs-[] -[T_ty]))⌝ ∗ Debug_T_realization.(trait_ctx_wf) Debug_T_lfts_inst Debug_T_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_OptionTasstd_fmt_Debug_fmt (T_rt: RT) (T_st: syn_type) (Debug_T_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Debug_base_spec (((Option_rt ((T_rt))))) ((Option_st (T_st))) ((drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))) ((OptionTasstd_fmt_Debug_spec_attrs (T_rt) (Debug_T_spec_attrs) (DropGlue_T_spec_attrs))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty])]).(Debug_fmt_spec)   a b))) <MERGE!>.

Definition trait_incl_of_Option_T_as_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_as_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 (Option_ty ((T_rt)) -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γ) : ((_)), match self.cur with Some x => Some (x, γ) | None => None end @ (Option_ty (((place_rfnRT (T_rt)) * gname)%type) -[] -[(mut_ref ulft_1 T_ty)]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (match self.cur with Some _ => Some (PlaceGhost (rt := (T_rt)) γ) | None => None end))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_take (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_take (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 (Option_ty ((T_rt)) -[] -[T_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self.cur @ (Option_ty ((T_rt)) -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost ((None : option (place_rfn (T_rt)))))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Option_T_unwrap_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Option_T_unwrap_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Option_ty ((T_rt)) -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, (⌜(destruct_hint self is_Some)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ T_ty;
      (* postcondition *) (λ π : thread_id, (⌜(match self with | Some x => ret = x | None => False end)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
Section OptionTasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition OptionTasstd_clone_Clone_spec (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec (((Option_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_OptionTasstd_clone_Clone_clone ((T_rt)) (T_st)) Clone_T_spec_attrs DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((Option_rt ((T_rt))))) ((Option_st (T_st)))) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (OptionTasstd_clone_Clone_spec_attrs (T_rt) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs)) 
             <TY> (Option_ty ((T_rt)) -[] -[T_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments OptionTasstd_clone_Clone_spec : simpl never.

  Program Definition OptionTasstd_clone_Clone_realization (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_T_realization: (trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) ((Option_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (Clone_T_lfts_inst : prod_vec lft Clone_T_realization.(trait_ctx_lfts)) (Clone_T_tys_inst : plist type Clone_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Clone_spec_incl (Clone_T_realization.(trait_ctx_spec) Clone_T_lfts_inst Clone_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (T_rt) T_st DropGlue_T_spec_attrs Clone_T_spec_attrs-[] -[T_ty]))⌝ ∗ Clone_T_realization.(trait_ctx_wf) Clone_T_lfts_inst Clone_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (OptionTasstd_clone_Clone_spec (T_rt) (T_st) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition OptionTasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(Clone_T_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (OptionTasstd_clone_Clone_spec (T_rt) (T_st) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Clone_base_spec ((Option_rt ((T_rt)))) (Option_st (T_st)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (OptionTasstd_clone_Clone_spec_attrs (T_rt) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty])])))).
End OptionTasstd_clone_Clone_spec.

Section OptionTasstd_fmt_Debug_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition OptionTasstd_fmt_Debug_spec (T_rt: RT) (T_st: syn_type) (Debug_T_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Debug_spec (((Option_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Debug_fmt_spec  :=
          (type_of_OptionTasstd_fmt_Debug_fmt ((T_rt)) (T_st)) Debug_T_spec_attrs DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 3 [] fn_spec);
      |}
  .
  Arguments OptionTasstd_fmt_Debug_spec : simpl never.

  Program Definition OptionTasstd_fmt_Debug_realization (T_rt: RT) (T_st: syn_type) (Debug_T_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (T_rt) )) (Debug_T_realization: (trait_spec_realization (spec_with 0 [] (Debug_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Debug_spec (RRGS:=RRGS) ((Option_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (Debug_T_lfts_inst : prod_vec lft Debug_T_realization.(trait_ctx_lfts)) (Debug_T_tys_inst : plist type Debug_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Debug_spec_incl (Debug_T_realization.(trait_ctx_spec) Debug_T_lfts_inst Debug_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Debug_base_spec (T_rt) T_st DropGlue_T_spec_attrs Debug_T_spec_attrs-[] -[T_ty]))⌝ ∗ Debug_T_realization.(trait_ctx_wf) Debug_T_lfts_inst Debug_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (OptionTasstd_fmt_Debug_spec (T_rt) (T_st) (Debug_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition OptionTasstd_fmt_Debug_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(Debug_T_spec_attrs : !(Debug_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Debug_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (OptionTasstd_fmt_Debug_spec (T_rt) (T_st) (Debug_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Debug_base_spec ((Option_rt ((T_rt)))) (Option_st (T_st)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (OptionTasstd_fmt_Debug_spec_attrs (T_rt) (Debug_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty])])))).
End OptionTasstd_fmt_Debug_spec.

Section OptionTasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition OptionTasstd_marker_Copy_spec (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Copy_T_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec (((Option_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (((Option_rt ((T_rt)))))).
  Arguments OptionTasstd_marker_Copy_spec : simpl never.

  Program Definition OptionTasstd_marker_Copy_realization (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_T_realization: (trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt))))) (Copy_T_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) (Copy_T_realization: (trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) ((Option_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (Clone_T_lfts_inst : prod_vec lft Clone_T_realization.(trait_ctx_lfts)) (Clone_T_tys_inst : plist type Clone_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Clone_spec_incl (Clone_T_realization.(trait_ctx_spec) Clone_T_lfts_inst Clone_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (T_rt) T_st DropGlue_T_spec_attrs Clone_T_spec_attrs-[] -[T_ty]))⌝ ∗ Clone_T_realization.(trait_ctx_wf) Clone_T_lfts_inst Clone_T_tys_inst π)
  ∗ (∃ (Copy_T_lfts_inst : prod_vec lft Copy_T_realization.(trait_ctx_lfts)) (Copy_T_tys_inst : plist type Copy_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Copy_spec_incl (Copy_T_realization.(trait_ctx_spec) Copy_T_lfts_inst Copy_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Copy_base_spec (T_rt) T_st Clone_T_spec_attrs DropGlue_T_spec_attrs Copy_T_spec_attrs-[] -[T_ty]))⌝ ∗ Copy_T_realization.(trait_ctx_wf) Copy_T_lfts_inst Copy_T_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (OptionTasstd_marker_Copy_spec (T_rt) (T_st) (Clone_T_spec_attrs) (Copy_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition OptionTasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(Clone_T_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) `(Copy_T_spec_attrs : !(Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (OptionTasstd_marker_Copy_spec (T_rt) (T_st) (Clone_T_spec_attrs) (Copy_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Copy_base_spec ((Option_rt ((T_rt)))) (Option_st (T_st)) (OptionTasstd_clone_Clone_spec_attrs ((T_rt)) (Clone_T_spec_attrs) (DropGlue_T_spec_attrs)) (drop_glue_Option_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (OptionTasstd_marker_Copy_spec_attrs (T_rt) (Clone_T_spec_attrs) (Copy_T_spec_attrs) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty])])))).
  Lemma OptionTasstd_marker_Copy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) (_: (Copy_semantic_interp (T_rt) T_ty)) : (Copy_semantic_interp ((Option_rt ((T_rt)))) (Option_ty ((T_rt)) -[] -[T_ty])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End OptionTasstd_marker_Copy_spec.

Section drop_glue_Option_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_Option_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (DropGlue_spec (((Option_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_Option ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments drop_glue_Option_spec : simpl never.

  Program Definition drop_glue_Option_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) ((Option_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (drop_glue_Option_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition drop_glue_Option_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (drop_glue_Option_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((DropGlue_base_spec ((Option_rt ((T_rt)))) (Option_st (T_st)) (drop_glue_Option_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(Option_ty ((T_rt)) -[] -[T_ty])])))).
End drop_glue_Option_spec.

