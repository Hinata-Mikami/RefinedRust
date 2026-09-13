From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.controlflow.controlflow Require Export generated_code_controlflow.

Definition convert_AsMut_AsMutFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (T_rt))).
Definition convert_AsMut_AsMutBackFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) (convert_AsMut_AsMutFn: (convert_AsMut_AsMutFn_sig (Self_rt) (T_rt))) :=
  ((RT_xt (T_rt)) → (RT_xt (Self_rt))).
Record convert_AsMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_AsMut_spec_attrs {
  convert_AsMut_AsMutFn  : (convert_AsMut_AsMutFn_sig (Self_rt) (T_rt));
  convert_AsMut_AsMutBackFn  : (convert_AsMut_AsMutBackFn_sig (Self_rt) (T_rt) (convert_AsMut_AsMutFn));
}.
#[global] Arguments convert_AsMut_spec_attrs : clear implicits.

#[global] Arguments convert_AsMut_spec_attrs {_ _}.

#[global] Arguments mk_convert_AsMut_spec_attrs  {_} {_} {_} {_}.


Definition convert_AsRef_AsRefFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (T_rt))).
Record convert_AsRef_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_AsRef_spec_attrs {
  convert_AsRef_AsRefFn  : (convert_AsRef_AsRefFn_sig (Self_rt) (T_rt));
}.
#[global] Arguments convert_AsRef_spec_attrs : clear implicits.

#[global] Arguments convert_AsRef_spec_attrs {_ _}.

#[global] Arguments mk_convert_AsRef_spec_attrs  {_} {_} {_} {_}.


Definition convert_From_FromFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) :=
  ((RT_xt (T_rt)) → (RT_xt (Self_rt))).
Record convert_From_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_From_spec_attrs {
  convert_From_FromFn  : (convert_From_FromFn_sig (Self_rt) (T_rt));
}.
#[global] Arguments convert_From_spec_attrs : clear implicits.

#[global] Arguments convert_From_spec_attrs {_ _}.

#[global] Arguments mk_convert_From_spec_attrs  {_} {_} {_} {_}.


Definition convert_Into_IntoFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (T_rt))).
Record convert_Into_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_Into_spec_attrs {
  convert_Into_IntoFn  : (convert_Into_IntoFn_sig (Self_rt) (T_rt));
}.
#[global] Arguments convert_Into_spec_attrs : clear implicits.

#[global] Arguments convert_Into_spec_attrs {_ _}.

#[global] Arguments mk_convert_Into_spec_attrs  {_} {_} {_} {_}.


Definition FromResidual_FromResidualFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (R_rt: RT) :=
  ((RT_xt (R_rt)) → option (RT_xt (Self_rt))).
Record FromResidual_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{R_rt : !RT} : Type := mk_FromResidual_spec_attrs {
  FromResidual_FromResidualFn  : (FromResidual_FromResidualFn_sig (Self_rt) (R_rt));
}.
#[global] Arguments FromResidual_spec_attrs : clear implicits.

#[global] Arguments FromResidual_spec_attrs {_ _}.

#[global] Arguments mk_FromResidual_spec_attrs  {_} {_} {_} {_}.


Record Residual_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{O_rt : !RT} `{TryType_rt : !RT} : Type := mk_Residual_spec_attrs {
}.
#[global] Arguments Residual_spec_attrs : clear implicits.

#[global] Arguments Residual_spec_attrs {_ _}.

#[global] Arguments mk_Residual_spec_attrs  {_} {_} {_} {_} {_}.


Definition Try_FromOutputFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) :=
  ((RT_xt (Output_rt)) → (RT_xt (Self_rt))).
Definition Try_BranchFn_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (Try_FromOutputFn: (Try_FromOutputFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs))) :=
  ((RT_xt (Self_rt)) → sum ((RT_xt (Output_rt))) ((RT_xt (Residual_rt)))).
Definition Try_ResidualValid_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (Try_FromOutputFn: (Try_FromOutputFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs))) (Try_BranchFn: (Try_BranchFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn))) :=
  ((RT_xt (Residual_rt)) → Prop).
Definition Try_BranchValid_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (Try_FromOutputFn: (Try_FromOutputFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs))) (Try_BranchFn: (Try_BranchFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn))) (Try_ResidualValid: (Try_ResidualValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn))) :=
  (∀ r x, Try_BranchFn r = inr x → Try_ResidualValid x).
Definition Try_BranchLawResidual_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (Try_FromOutputFn: (Try_FromOutputFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs))) (Try_BranchFn: (Try_BranchFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn))) (Try_ResidualValid: (Try_ResidualValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn))) (Try_BranchValid: (Try_BranchValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn) (Try_ResidualValid))) :=
  (∀ x r, Try_ResidualValid r → FromResidual_Self_SelfasTry_Residual_spec_attrs.(FromResidual_FromResidualFn) r = Some x → Try_BranchFn x = inr r).
Definition Try_BranchLawOutput_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (Try_FromOutputFn: (Try_FromOutputFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs))) (Try_BranchFn: (Try_BranchFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn))) (Try_ResidualValid: (Try_ResidualValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn))) (Try_BranchValid: (Try_BranchValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn) (Try_ResidualValid))) (Try_BranchLawResidual: (Try_BranchLawResidual_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn) (Try_ResidualValid) (Try_BranchValid))) :=
  (∀ x r, Try_FromOutputFn r = x → Try_BranchFn x = inl r).
Record Try_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Output_rt : !RT} `{Residual_rt : !RT} `{FromResidual_Self_SelfasTry_Residual_spec_attrs : !(FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )} : Type := mk_Try_spec_attrs {
  Try_FromOutputFn  : (Try_FromOutputFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs));
  Try_BranchFn  : (Try_BranchFn_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn));
  Try_ResidualValid  : (Try_ResidualValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn));
  Try_BranchValid  : (Try_BranchValid_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn) (Try_ResidualValid));
  Try_BranchLawResidual  : (Try_BranchLawResidual_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn) (Try_ResidualValid) (Try_BranchValid));
  Try_BranchLawOutput  : (Try_BranchLawOutput_sig (Self_rt) (Output_rt) (Residual_rt) (FromResidual_Self_SelfasTry_Residual_spec_attrs) (Try_FromOutputFn) (Try_BranchFn) (Try_ResidualValid) (Try_BranchValid) (Try_BranchLawResidual));
}.
#[global] Arguments Try_spec_attrs : clear implicits.

#[global] Arguments Try_spec_attrs {_ _}.

#[global] Arguments mk_Try_spec_attrs  {_} {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition Tasconvert_FromT_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((convert_From_spec_attrs ((T_rt)) ((T_rt)))) :=
  {|
    convert_From_FromFn  :=
      (id) : ((convert_From_FromFn_sig ((T_rt)) ((T_rt))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition Tasconvert_IntoU_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (U_rt: RT) (convert_From_U_T_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (U_rt) (T_rt) )) : ((convert_Into_spec_attrs ((T_rt)) ((U_rt)))) :=
  {|
    convert_Into_IntoFn  :=
      (convert_From_U_T_spec_attrs.(convert_From_FromFn)) : ((convert_Into_IntoFn_sig ((T_rt)) ((U_rt))));
  |}
.


End attrs.

Section ControlFlow_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {B_rt : RT} {C_rt : RT}.
  Section components.
    Definition ControlFlow_Continue_ty  : (spec_with 0 [(B_rt); (C_rt)] ((type (plist place_rfnRT [(C_rt) : RT])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (struct_t (ControlFlow_Continue_sls ((ty_syn_type B_ty MetaNone)) ((ty_syn_type C_ty MetaNone))) +[(C_ty)])).
    Defined.

    Definition ControlFlow_Continue_rt  : RT.
    Proof using B_rt C_rt .
      let __a := (normalized_rt_of_spec_ty (ControlFlow_Continue_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent ControlFlow_Continue_rt.
    #[global] Typeclasses Transparent ControlFlow_Continue_ty.
    Definition ControlFlow_Break_ty  : (spec_with 0 [(B_rt); (C_rt)] ((type (plist place_rfnRT [(B_rt) : RT])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (struct_t (ControlFlow_Break_sls ((ty_syn_type B_ty MetaNone)) ((ty_syn_type C_ty MetaNone))) +[(B_ty)])).
    Defined.

    Definition ControlFlow_Break_rt  : RT.
    Proof using B_rt C_rt .
      let __a := (normalized_rt_of_spec_ty (ControlFlow_Break_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent ControlFlow_Break_rt.
    #[global] Typeclasses Transparent ControlFlow_Break_ty.
    Definition ControlFlow_enum_rt  :=
      λ rfn : (sum (place_rfn (C_rt)) (place_rfn (B_rt))), match rfn with | (inl (x)) => ControlFlow_Continue_rt| (inr (x)) => ControlFlow_Break_rt end.
    Definition ControlFlow_enum_ty  : (spec_with 0 [(B_rt); (C_rt)] (∀ (x: _), (type (ControlFlow_enum_rt (x))))) :=
      spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), λ rfn, match rfn as x return type (ControlFlow_enum_rt x) with | (inl (x)) => ControlFlow_Continue_ty -[] -[B_ty; C_ty]| (inr (x)) => ControlFlow_Break_ty -[] -[B_ty; C_ty] end.
    Program Definition ControlFlow_enum  : (spec_with 0 [(B_rt); (C_rt)] ((enum ((sum (place_rfn (C_rt)) (place_rfn (B_rt))))))) :=
      spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), mk_enum
        _
        ((ControlFlow_els ((ty_syn_type B_ty MetaNone)) ((ty_syn_type C_ty MetaNone))))
        (λ rfn, Some (match rfn with | (inl (x)) => "Continue" | (inr (x)) => "Break" end))
        (ControlFlow_enum_rt)
        (ControlFlow_enum_ty -[] -[B_ty; C_ty])
        (λ rfn, match rfn with | (inl (x)) => *[x]| (inr (x)) => *[x] end)
        ([("Continue", mk_enum_tag_sem _ (ControlFlow_Continue_ty -[] -[B_ty; C_ty]) (λ '( *[x]), (inl (x)))); ("Break", mk_enum_tag_sem _ (ControlFlow_Break_ty -[] -[B_ty; C_ty]) (λ '( *[x]), (inr (x))))])
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

    Next Obligation.
      solve_mk_enum_tag_inj_roundtrip.
    Defined.

    #[global] Arguments ControlFlow_enum : simpl never.

    Definition ControlFlow_ty_pre  : (spec_with 0 [(B_rt); (C_rt)] ((type _))) :=
      spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), enum_t (ControlFlow_enum -[] -[B_ty; C_ty]).
    Definition ControlFlow_rt_pre  : RT.
    Proof using B_rt C_rt .
      let __a := (normalized_rt_of_spec_ty (ControlFlow_ty_pre)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent ControlFlow_rt_pre.
  End components.
  Arguments enum_ty : simpl never.

  Definition ControlFlow_ty  : (spec_with 0 [(B_rt); (C_rt)] ((type _))) :=
    spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), enum_t (ControlFlow_enum -[] -[B_ty; C_ty]).
  Definition ControlFlow_rt  : RT.
  Proof using B_rt C_rt .
    let __a := (normalized_rt_of_spec_ty (ControlFlow_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent ControlFlow_rt.
End ControlFlow_ty.
#[global] Typeclasses Transparent ControlFlow_ty.
#[global] Typeclasses Transparent ControlFlow_rt.
#[global] Arguments ControlFlow_enum : simpl never.

#[global] Arguments ControlFlow_rt : clear implicits.

#[global] Arguments ControlFlow_ty : clear implicits.

#[global] Arguments ControlFlow_ty {_ _} _ _  .

Global Hint Unfold ControlFlow_ty : solve_protected_eq_db.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition ControlFlowBasResidualC_spec_attrs `{RRGS : !(refinedrustGS Σ)} (B_rt: RT) (C_rt: RT) : ((Residual_spec_attrs (((ControlFlow_rt ((B_rt)) (unit)))) ((C_rt)) (((ControlFlow_rt ((B_rt)) ((C_rt))))))) :=
  mk_Residual_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition ControlFlowBCasFromResidualControlFlowB_spec_attrs `{RRGS : !(refinedrustGS Σ)} (B_rt: RT) (C_rt: RT) : ((FromResidual_spec_attrs (((ControlFlow_rt ((B_rt)) ((C_rt))))) (((ControlFlow_rt ((B_rt)) (unit)))))) :=
  {|
    FromResidual_FromResidualFn  :=
      (λ s, match s with | inl(x) => None | inr(x) => Some (inr x) end) : ((FromResidual_FromResidualFn_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) (((ControlFlow_rt ((B_rt)) (unit))))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionasResidualT_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Residual_spec_attrs (((((Option_rt)) (unit)))) ((T_rt)) (((((Option_rt)) ((T_rt))))))) :=
  mk_Residual_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionTasFromResidual_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((FromResidual_spec_attrs (((((Option_rt)) ((T_rt))))) (((((Option_rt)) (unit)))))) :=
  {|
    FromResidual_FromResidualFn  :=
      (λ _, Some None) : ((FromResidual_FromResidualFn_sig (((((Option_rt)) ((T_rt))))) (((((Option_rt)) (unit))))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_result_ResultEasResidualT_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (E_rt: RT) : ((Residual_spec_attrs (((((Result_rt)) (unit) ((E_rt))))) ((T_rt)) (((((Result_rt)) ((T_rt)) ((E_rt))))))) :=
  mk_Residual_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (E_rt: RT) (F_rt: RT) (convert_From_F_E_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (F_rt) (E_rt) )) : ((FromResidual_spec_attrs (((((Result_rt)) ((T_rt)) ((F_rt))))) (((((Result_rt)) (unit) ((E_rt))))))) :=
  {|
    FromResidual_FromResidualFn  :=
      (λ s, match s with | inl(x) => None | inr(x) => Some (inr ((convert_From_F_E_spec_attrs.(convert_From_FromFn) x))) end) : ((FromResidual_FromResidualFn_sig (((((Result_rt)) ((T_rt)) ((F_rt))))) (((((Result_rt)) (unit) ((E_rt)))))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition ControlFlowBCasTry_spec_attrs `{RRGS : !(refinedrustGS Σ)} (B_rt: RT) (C_rt: RT) : ((Try_spec_attrs (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))))) :=
  {|
    Try_FromOutputFn  :=
      (λ out, inl (out)) : ((Try_FromOutputFn_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt))))));
    Try_BranchFn  :=
      (result_xmap id (inr)) : ((Try_BranchFn_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) (_)));
    Try_ResidualValid  :=
      (λ x, is_Err x) : ((Try_ResidualValid_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) (_) (_)));
    Try_BranchValid  :=
      (_) : ((Try_BranchValid_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) (_) (_) (_)));
    Try_BranchLawResidual  :=
      (_) : ((Try_BranchLawResidual_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) (_) (_) (_) (_)));
    Try_BranchLawOutput  :=
      (_) : ((Try_BranchLawOutput_sig (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??? [] ?; simpl; solve_goal.
Qed.

Next Obligation.
  intros ??? [] ?; simpl; solve_goal.
Qed.

Next Obligation.
  intros ??? [] ?; simpl; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_option_OptionTasTry_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Try_spec_attrs (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))))) :=
  {|
    Try_FromOutputFn  :=
      (λ out, Some out) : ((Try_FromOutputFn_sig (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt))))));
    Try_BranchFn  :=
      (λ s, match s with | Some(x) => inl(x) | None => inr(None) end) : ((Try_BranchFn_sig (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) (_)));
    Try_ResidualValid  :=
      (λ x, x = None) : ((Try_ResidualValid_sig (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) (_) (_)));
    Try_BranchValid  :=
      (_) : ((Try_BranchValid_sig (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) (_) (_) (_)));
    Try_BranchLawResidual  :=
      (_) : ((Try_BranchLawResidual_sig (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) (_) (_) (_) (_)));
    Try_BranchLawOutput  :=
      (_) : ((Try_BranchLawOutput_sig (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ?? [] ?; simpl; solve_goal.
Qed.

Next Obligation.
  intros ?? [] ?; simpl; solve_goal.
Qed.

Next Obligation.
  intros ?? [] ?; simpl; solve_goal.
Qed.



End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_result_ResultTEasTry_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (E_rt: RT) : ((Try_spec_attrs (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))))) :=
  {|
    Try_FromOutputFn  :=
      (λ out, Ok (out)) : ((Try_FromOutputFn_sig (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt))))))));
    Try_BranchFn  :=
      (result_xmap id (λ x, (Err x))) : ((Try_BranchFn_sig (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) (_)));
    Try_ResidualValid  :=
      (λ x, is_Err x) : ((Try_ResidualValid_sig (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) (_) (_)));
    Try_BranchValid  :=
      (_) : ((Try_BranchValid_sig (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) (_) (_) (_)));
    Try_BranchLawResidual  :=
      (_) : ((Try_BranchLawResidual_sig (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) (_) (_) (_) (_)));
    Try_BranchLawOutput  :=
      (_) : ((Try_BranchLawOutput_sig (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) (_) (_) (_) (_) (_)));
  |}
.
Next Obligation.
  intros ??? [] ?; simpl; solve_goal.
Qed.

Next Obligation.
  intros ??? [] ?; simpl; solve_goal.
Qed.

Next Obligation.
  intros ??? [] ?; simpl; solve_goal.
Qed.



End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Lemma branchfn_from_output_eq {Self_rt Output_rt ResidualRt} (A: FromResidual_spec_attrs Self_rt ResidualRt) (B : Try_spec_attrs Self_rt Output_rt ResidualRt A) r :
  B.(Try_BranchFn) (B.(Try_FromOutputFn) r) = inl r.
Proof.
  by apply B.(Try_BranchLawOutput).
Qed.

Lemma branchfn_from_residual_eq {Self_rt Output_rt ResidualRt} (A: FromResidual_spec_attrs Self_rt ResidualRt) (B : Try_spec_attrs Self_rt Output_rt ResidualRt A) r x :
  B.(Try_ResidualValid) r →
  (A.(FromResidual_FromResidualFn) r = Some x) →
  B.(Try_BranchFn) x = inr r.
Proof.
  by apply B.(Try_BranchLawResidual).
Qed.

Global Instance simpl_impl_from_residual {Self_rt Output_rt ResidualRt} (A: FromResidual_spec_attrs Self_rt ResidualRt) (B : Try_spec_attrs Self_rt Output_rt ResidualRt A) x y r `{Heq : !TCDone (B.(Try_BranchFn) y = inr r)}:
  SimplImplRel (=) false (A.(FromResidual_FromResidualFn) r) (Some x) (λ T, A.(FromResidual_FromResidualFn) r = Some x → B.(Try_BranchFn) x = inr r → T).
Proof.
  intros T. 
  unfold TCDone in Heq.
  split.
  - intros Hb Hres. apply Hb; first done. 
    eapply Try_BranchLawResidual; last done. 
    by eapply Try_BranchValid.
  - intros Hb Hres ?. apply Hb. 
    done.
Qed.
End extra_specs.

Global Hint Rewrite -> @branchfn_from_residual_eq using done : lithium_rewrite.
Global Hint Rewrite -> @branchfn_from_output_eq : lithium_rewrite.
Record convert_AsMut_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_AsMut_spec {
  convert_AsMut_as_mut_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments convert_AsMut_spec : clear implicits.

#[global] Arguments convert_AsMut_spec {_ _}.


Record convert_AsRef_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_AsRef_spec {
  convert_AsRef_as_ref_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments convert_AsRef_spec : clear implicits.

#[global] Arguments convert_AsRef_spec {_ _}.


Record convert_From_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_From_spec {
  convert_From_from_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments convert_From_spec : clear implicits.

#[global] Arguments convert_From_spec {_ _}.


Record convert_Into_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} : Type := mk_convert_Into_spec {
  convert_Into_into_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments convert_Into_spec : clear implicits.

#[global] Arguments convert_Into_spec {_ _}.


Record FromResidual_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{R_rt : !RT} : Type := mk_FromResidual_spec {
  FromResidual_from_residual_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments FromResidual_spec : clear implicits.

#[global] Arguments FromResidual_spec {_ _}.


Record Residual_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{O_rt : !RT} `{TryType_rt : !RT} : Type := mk_Residual_spec {
}.
#[global] Arguments Residual_spec : clear implicits.

#[global] Arguments Residual_spec {_ _}.


Record Try_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Output_rt : !RT} `{Residual_rt : !RT} `{Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt : !RT} : Type := mk_Try_spec {
  Try_branch_spec  : (spec_with 0 [] fn_spec);
  Try_from_output_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments Try_spec : clear implicits.

#[global] Arguments Try_spec {_ _}.


Section convert_AsMut.
Context `{RRGS : !refinedrustGS Σ}.
Definition convert_AsMut_spec_incl `{Self_rt : !RT} `{T_rt : !RT} (spec1: ((convert_AsMut_spec (Self_rt) (T_rt)))) (spec2: ((convert_AsMut_spec (Self_rt) (T_rt)))) : Prop :=
  ((function_subtype (spec1.(convert_AsMut_as_mut_spec)) (spec2.(convert_AsMut_as_mut_spec)))).
Instance convert_AsMut_spec_incl_preorder `{Self_rt : !RT} `{T_rt : !RT} : (PreOrder (convert_AsMut_spec_incl (Self_rt := Self_rt) (T_rt := T_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_convert_AsMut_spec `{Self_rt : !RT} `{T_rt : !RT} : (ScopeBindable ((convert_AsMut_spec (Self_rt) (T_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((convert_AsMut_spec (Self_rt) (T_rt)))) :=
      {|
        convert_AsMut_as_mut_spec  :=
          (scope_add_typarams (rts) (tys) (s.(convert_AsMut_as_mut_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((convert_AsMut_spec (Self_rt) (T_rt)))) :=
      {|
        convert_AsMut_as_mut_spec  :=
          (scope_add_elctx (E) (s.(convert_AsMut_as_mut_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_convert_AsMut_spec.

Definition convert_AsMut_as_mut_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_AsMut_Self_T_spec_attrs: (convert_AsMut_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty]) : ([(Self_rt, Self_st); (T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γ, y) : ((_ * _)), (y, γ) @ (mut_ref ulft_1 T_ty);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition convert_AsMut_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (_ATTRS: ((convert_AsMut_spec_attrs ((Self_rt)) ((T_rt))))) : (spec_with _ _ (convert_AsMut_spec ((Self_rt)) ((T_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), {|
      convert_AsMut_as_mut_spec  :=
        (convert_AsMut_as_mut_base_spec ((Self_rt)) ((T_rt)) (Self_st) (T_st)) _ATTRS 
           <TY> Self_ty <TY> T_ty : (spec_with 1 [] fn_spec);
    |}
.

End convert_AsMut.

Section convert_AsRef.
Context `{RRGS : !refinedrustGS Σ}.
Definition convert_AsRef_spec_incl `{Self_rt : !RT} `{T_rt : !RT} (spec1: ((convert_AsRef_spec (Self_rt) (T_rt)))) (spec2: ((convert_AsRef_spec (Self_rt) (T_rt)))) : Prop :=
  ((function_subtype (spec1.(convert_AsRef_as_ref_spec)) (spec2.(convert_AsRef_as_ref_spec)))).
Instance convert_AsRef_spec_incl_preorder `{Self_rt : !RT} `{T_rt : !RT} : (PreOrder (convert_AsRef_spec_incl (Self_rt := Self_rt) (T_rt := T_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_convert_AsRef_spec `{Self_rt : !RT} `{T_rt : !RT} : (ScopeBindable ((convert_AsRef_spec (Self_rt) (T_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((convert_AsRef_spec (Self_rt) (T_rt)))) :=
      {|
        convert_AsRef_as_ref_spec  :=
          (scope_add_typarams (rts) (tys) (s.(convert_AsRef_as_ref_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((convert_AsRef_spec (Self_rt) (T_rt)))) :=
      {|
        convert_AsRef_as_ref_spec  :=
          (scope_add_elctx (E) (s.(convert_AsRef_as_ref_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_convert_AsRef_spec.

Definition convert_AsRef_as_ref_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_AsRef_Self_T_spec_attrs: (convert_AsRef_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty]) : ([(Self_rt, Self_st); (T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, convert_AsRef_Self_T_spec_attrs.(convert_AsRef_AsRefFn) self @ (shr_ref ulft_1 T_ty);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition convert_AsRef_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (_ATTRS: ((convert_AsRef_spec_attrs ((Self_rt)) ((T_rt))))) : (spec_with _ _ (convert_AsRef_spec ((Self_rt)) ((T_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), {|
      convert_AsRef_as_ref_spec  :=
        (convert_AsRef_as_ref_base_spec ((Self_rt)) ((T_rt)) (Self_st) (T_st)) _ATTRS 
           <TY> Self_ty <TY> T_ty : (spec_with 1 [] fn_spec);
    |}
.

End convert_AsRef.

Section convert_From.
Context `{RRGS : !refinedrustGS Σ}.
Definition convert_From_spec_incl `{Self_rt : !RT} `{T_rt : !RT} (spec1: ((convert_From_spec (Self_rt) (T_rt)))) (spec2: ((convert_From_spec (Self_rt) (T_rt)))) : Prop :=
  ((function_subtype (spec1.(convert_From_from_spec)) (spec2.(convert_From_from_spec)))).
Instance convert_From_spec_incl_preorder `{Self_rt : !RT} `{T_rt : !RT} : (PreOrder (convert_From_spec_incl (Self_rt := Self_rt) (T_rt := T_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_convert_From_spec `{Self_rt : !RT} `{T_rt : !RT} : (ScopeBindable ((convert_From_spec (Self_rt) (T_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((convert_From_spec (Self_rt) (T_rt)))) :=
      {|
        convert_From_from_spec  :=
          (scope_add_typarams (rts) (tys) (s.(convert_From_from_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((convert_From_spec (Self_rt) (T_rt)))) :=
      {|
        convert_From_from_spec  :=
          (scope_add_elctx (E) (s.(convert_From_from_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_convert_From_spec.

Definition convert_From_from_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_From_Self_T_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([(Self_rt, Self_st); (T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (value) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) value :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, convert_From_Self_T_spec_attrs.(convert_From_FromFn) value @ Self_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition convert_From_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (_ATTRS: ((convert_From_spec_attrs ((Self_rt)) ((T_rt))))) : (spec_with _ _ (convert_From_spec ((Self_rt)) ((T_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), {|
      convert_From_from_spec  :=
        (convert_From_from_base_spec ((Self_rt)) ((T_rt)) (Self_st) (T_st)) _ATTRS 
           <TY> Self_ty <TY> T_ty : (spec_with 0 [] fn_spec);
    |}
.

End convert_From.

Section convert_Into.
Context `{RRGS : !refinedrustGS Σ}.
Definition convert_Into_spec_incl `{Self_rt : !RT} `{T_rt : !RT} (spec1: ((convert_Into_spec (Self_rt) (T_rt)))) (spec2: ((convert_Into_spec (Self_rt) (T_rt)))) : Prop :=
  ((function_subtype (spec1.(convert_Into_into_spec)) (spec2.(convert_Into_into_spec)))).
Instance convert_Into_spec_incl_preorder `{Self_rt : !RT} `{T_rt : !RT} : (PreOrder (convert_Into_spec_incl (Self_rt := Self_rt) (T_rt := T_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_convert_Into_spec `{Self_rt : !RT} `{T_rt : !RT} : (ScopeBindable ((convert_Into_spec (Self_rt) (T_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((convert_Into_spec (Self_rt) (T_rt)))) :=
      {|
        convert_Into_into_spec  :=
          (scope_add_typarams (rts) (tys) (s.(convert_Into_into_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((convert_Into_spec (Self_rt) (T_rt)))) :=
      {|
        convert_Into_into_spec  :=
          (scope_add_elctx (E) (s.(convert_Into_into_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_convert_Into_spec.

Definition convert_Into_into_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_Into_Self_T_spec_attrs: (convert_Into_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([(Self_rt, Self_st); (T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, convert_Into_Self_T_spec_attrs.(convert_Into_IntoFn) self @ T_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition convert_Into_base_spec (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (_ATTRS: ((convert_Into_spec_attrs ((Self_rt)) ((T_rt))))) : (spec_with _ _ (convert_Into_spec ((Self_rt)) ((T_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), {|
      convert_Into_into_spec  :=
        (convert_Into_into_base_spec ((Self_rt)) ((T_rt)) (Self_st) (T_st)) _ATTRS 
           <TY> Self_ty <TY> T_ty : (spec_with 0 [] fn_spec);
    |}
.

End convert_Into.

Section FromResidual.
Context `{RRGS : !refinedrustGS Σ}.
Definition FromResidual_spec_incl `{Self_rt : !RT} `{R_rt : !RT} (spec1: ((FromResidual_spec (Self_rt) (R_rt)))) (spec2: ((FromResidual_spec (Self_rt) (R_rt)))) : Prop :=
  ((function_subtype (spec1.(FromResidual_from_residual_spec)) (spec2.(FromResidual_from_residual_spec)))).
Instance FromResidual_spec_incl_preorder `{Self_rt : !RT} `{R_rt : !RT} : (PreOrder (FromResidual_spec_incl (Self_rt := Self_rt) (R_rt := R_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_FromResidual_spec `{Self_rt : !RT} `{R_rt : !RT} : (ScopeBindable ((FromResidual_spec (Self_rt) (R_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((FromResidual_spec (Self_rt) (R_rt)))) :=
      {|
        FromResidual_from_residual_spec  :=
          (scope_add_typarams (rts) (tys) (s.(FromResidual_from_residual_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((FromResidual_spec (Self_rt) (R_rt)))) :=
      {|
        FromResidual_from_residual_spec  :=
          (scope_add_elctx (E) (s.(FromResidual_from_residual_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_FromResidual_spec.

Definition FromResidual_from_residual_base_spec (Self_rt: RT) (R_rt: RT) (Self_st: syn_type) (R_st: syn_type) (FromResidual_Self_R_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (R_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; R_ty]) : ([(Self_rt, Self_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (residual) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) residual :@: R_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (y) : ((_)), y @ Self_ty;
      (* postcondition *) (λ π : thread_id, (⌜(Some y = FromResidual_Self_R_spec_attrs.(FromResidual_FromResidualFn) residual)%Z⌝)) |
      (* unwind post... *) False.

Definition FromResidual_base_spec (Self_rt: RT) (R_rt: RT) (Self_st: syn_type) (R_st: syn_type) (_ATTRS: ((FromResidual_spec_attrs ((Self_rt)) ((R_rt))))) : (spec_with _ _ (FromResidual_spec ((Self_rt)) ((R_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; R_ty]) : ([Self_rt; R_rt] : list RT), {|
      FromResidual_from_residual_spec  :=
        (FromResidual_from_residual_base_spec ((Self_rt)) ((R_rt)) (Self_st) (R_st)) _ATTRS 
           <TY> Self_ty <TY> R_ty : (spec_with 0 [] fn_spec);
    |}
.

End FromResidual.

Section Residual.
Context `{RRGS : !refinedrustGS Σ}.
Definition Residual_spec_incl `{Self_rt : !RT} `{O_rt : !RT} `{TryType_rt : !RT} (spec1: ((Residual_spec (Self_rt) (O_rt) (TryType_rt)))) (spec2: ((Residual_spec (Self_rt) (O_rt) (TryType_rt)))) : Prop :=
  True.
Instance Residual_spec_incl_preorder `{Self_rt : !RT} `{O_rt : !RT} `{TryType_rt : !RT} : (PreOrder (Residual_spec_incl (Self_rt := Self_rt) (O_rt := O_rt) (TryType_rt := TryType_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Residual_spec `{Self_rt : !RT} `{O_rt : !RT} `{TryType_rt : !RT} : (ScopeBindable ((Residual_spec (Self_rt) (O_rt) (TryType_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Residual_spec (Self_rt) (O_rt) (TryType_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((Residual_spec (Self_rt) (O_rt) (TryType_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_Residual_spec.

Definition Residual_base_spec (Self_rt: RT) (O_rt: RT) (TryType_rt: RT) (Self_st: syn_type) (O_st: syn_type) (TryType_st: syn_type) (FromResidual_SelfasResidualO_TryType_SelfasResidualO_TryTypeasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (TryType_rt) (Self_rt) )) (Try_SelfasResidualO_TryType_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (TryType_rt) (O_rt) (Self_rt) FromResidual_SelfasResidualO_TryType_SelfasResidualO_TryTypeasTry_Residual_spec_attrs)) (_ATTRS: ((Residual_spec_attrs ((Self_rt)) ((O_rt)) ((TryType_rt))))) : (spec_with _ _ (Residual_spec ((Self_rt)) ((O_rt)) ((TryType_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; O_ty; TryType_ty]) : ([Self_rt; O_rt; TryType_rt] : list RT), (@mk_Residual_spec _ _ ((Self_rt)) ((O_rt)) ((TryType_rt))).

End Residual.

Section Try.
Context `{RRGS : !refinedrustGS Σ}.
Definition Try_spec_incl `{Self_rt : !RT} `{Output_rt : !RT} `{Residual_rt : !RT} `{Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt : !RT} (spec1: ((Try_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (spec2: ((Try_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) : Prop :=
  ((function_subtype (spec1.(Try_branch_spec)) (spec2.(Try_branch_spec)))) ∧ ((function_subtype (spec1.(Try_from_output_spec)) (spec2.(Try_from_output_spec)))).
Instance Try_spec_incl_preorder `{Self_rt : !RT} `{Output_rt : !RT} `{Residual_rt : !RT} `{Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt : !RT} : (PreOrder (Try_spec_incl (Self_rt := Self_rt) (Output_rt := Output_rt) (Residual_rt := Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt := Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Try_spec `{Self_rt : !RT} `{Output_rt : !RT} `{Residual_rt : !RT} `{Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt : !RT} : (ScopeBindable ((Try_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Try_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) :=
      {|
        Try_branch_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Try_branch_spec)));
        Try_from_output_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Try_from_output_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Try_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) :=
      {|
        Try_branch_spec  :=
          (scope_add_elctx (E) (s.(Try_branch_spec)));
        Try_from_output_spec  :=
          (scope_add_elctx (E) (s.(Try_from_output_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Try_spec.

Definition Try_branch_base_spec (Self_rt: RT) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt: RT) (Output_rt: RT) (Residual_rt: RT) (Self_st: syn_type) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st: syn_type) (Output_st: syn_type) (Residual_st: syn_type) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) )) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs)) (Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs: (Residual_spec_attrs (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) )) (Try_Self_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Self_rt) (Output_rt) (Residual_rt) FromResidual_Self_SelfasTry_Residual_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Output_ty; Residual_ty]) : ([(Self_rt, Self_st); (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt, Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st); (Output_rt, Output_st); (Residual_rt, Residual_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Try_Self_spec_attrs.(Try_BranchFn) (self) @ (ControlFlow_ty ((Residual_rt)) ((Output_rt)) -[] -[Residual_ty; Output_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition Try_from_output_base_spec (Self_rt: RT) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt: RT) (Output_rt: RT) (Residual_rt: RT) (Self_st: syn_type) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st: syn_type) (Output_st: syn_type) (Residual_st: syn_type) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) )) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs)) (Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs: (Residual_spec_attrs (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) )) (Try_Self_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Self_rt) (Output_rt) (Residual_rt) FromResidual_Self_SelfasTry_Residual_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Output_ty; Residual_ty]) : ([(Self_rt, Self_st); (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt, Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st); (Output_rt, Output_st); (Residual_rt, Residual_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (output) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) output :@: Output_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Try_Self_spec_attrs.(Try_FromOutputFn) (output) @ Self_ty;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition Try_base_spec (Self_rt: RT) (Output_rt: RT) (Residual_rt: RT) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt: RT) (Self_st: syn_type) (Output_st: syn_type) (Residual_st: syn_type) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st: syn_type) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) )) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs)) (Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs: (Residual_spec_attrs (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) )) (_ATTRS: ((Try_spec_attrs ((Self_rt)) ((Output_rt)) ((Residual_rt)) (FromResidual_Self_SelfasTry_Residual_spec_attrs)))) : (spec_with _ _ (Try_spec ((Self_rt)) ((Output_rt)) ((Residual_rt)) ((Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Output_ty; Residual_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]) : ([Self_rt; Output_rt; Residual_rt; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt] : list RT), {|
      Try_branch_spec  :=
        (Try_branch_base_spec ((Self_rt)) ((Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)) ((Output_rt)) ((Residual_rt)) (Self_st) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st) (Output_st) (Residual_st)) FromResidual_Self_SelfasTry_Residual_spec_attrs FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty <TY> Output_ty <TY> Residual_ty : (spec_with 0 [] fn_spec);
      Try_from_output_spec  :=
        (Try_from_output_base_spec ((Self_rt)) ((Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)) ((Output_rt)) ((Residual_rt)) (Self_st) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st) (Output_st) (Residual_st)) FromResidual_Self_SelfasTry_Residual_spec_attrs FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty <TY> Output_ty <TY> Residual_ty : (spec_with 0 [] fn_spec);
    |}
.

End Try.

Section convert_AsMut_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_convert_AsMut_as_mut (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_AsMut_Self_T_spec_attrs: (convert_AsMut_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) (convert_AsMut_Self_T_spec: (spec_with 0 [] (convert_AsMut_spec (RRGS:=RRGS) (Self_rt) (T_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), ((trait_incl_marker (lift_trait_incl convert_AsMut_spec_incl convert_AsMut_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), convert_AsMut_base_spec (Self_rt) (T_rt) Self_st T_st convert_AsMut_Self_T_spec_attrs-[] -[Self_ty; T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).
End convert_AsMut_trait_req_incls.

Section convert_AsRef_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_convert_AsRef_as_ref (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_AsRef_Self_T_spec_attrs: (convert_AsRef_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) (convert_AsRef_Self_T_spec: (spec_with 0 [] (convert_AsRef_spec (RRGS:=RRGS) (Self_rt) (T_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), ((trait_incl_marker (lift_trait_incl convert_AsRef_spec_incl convert_AsRef_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), convert_AsRef_base_spec (Self_rt) (T_rt) Self_st T_st convert_AsRef_Self_T_spec_attrs-[] -[Self_ty; T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).
End convert_AsRef_trait_req_incls.

Section convert_From_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_convert_From_from (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_From_Self_T_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) (convert_From_Self_T_spec: (spec_with 0 [] (convert_From_spec (RRGS:=RRGS) (Self_rt) (T_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), ((trait_incl_marker (lift_trait_incl convert_From_spec_incl convert_From_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), convert_From_base_spec (Self_rt) (T_rt) Self_st T_st convert_From_Self_T_spec_attrs-[] -[Self_ty; T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).
End convert_From_trait_req_incls.

Section convert_Into_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_convert_Into_into (Self_rt: RT) (T_rt: RT) (Self_st: syn_type) (T_st: syn_type) (convert_Into_Self_T_spec_attrs: (convert_Into_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) )) (convert_Into_Self_T_spec: (spec_with 0 [] (convert_Into_spec (RRGS:=RRGS) (Self_rt) (T_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; T_ty]) : ([Self_rt; T_rt] : list RT), ((trait_incl_marker (lift_trait_incl convert_Into_spec_incl convert_Into_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), convert_Into_base_spec (Self_rt) (T_rt) Self_st T_st convert_Into_Self_T_spec_attrs-[] -[Self_ty; T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).
End convert_Into_trait_req_incls.

Section FromResidual_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_FromResidual_from_residual (Self_rt: RT) (R_rt: RT) (Self_st: syn_type) (R_st: syn_type) (FromResidual_Self_R_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (R_rt) )) (FromResidual_Self_R_spec: (spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (Self_rt) (R_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_R_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; R_ty]) : ([Self_rt; R_rt] : list RT), ((trait_incl_marker (lift_trait_incl FromResidual_spec_incl FromResidual_Self_R_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FromResidual_base_spec (Self_rt) (R_rt) Self_st R_st FromResidual_Self_R_spec_attrs-[] -[Self_ty; R_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_R_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st-[] -[R_ty])))).
End FromResidual_trait_req_incls.

Section Residual_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Residual_trait_req_incls.

Section Try_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Try_branch (Self_rt: RT) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt: RT) (Output_rt: RT) (Residual_rt: RT) (Self_st: syn_type) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st: syn_type) (Output_st: syn_type) (Residual_st: syn_type) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (FromResidual_Self_SelfasTry_Residual_spec: (spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (Self_rt) (Residual_rt)))) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) )) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec: (spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt)))) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs)) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec: (spec_with 0 [] (Try_spec (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs: (Residual_spec_attrs (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) )) (Residual_SelfasTry_Residual_SelfasTry_Output_spec: (spec_with 0 [] (Residual_spec (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (Try_Self_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Self_rt) (Output_rt) (Residual_rt) FromResidual_Self_SelfasTry_Residual_spec_attrs)) (Try_Self_spec: (spec_with 0 [] (Try_spec (RRGS:=RRGS) (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (DropGlue_SelfasTry_Output_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt)))) (DropGlue_SelfasTry_Residual_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Residual_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Output_ty; Residual_ty]) : ([Self_rt; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt; Output_rt; Residual_rt] : list RT), ((trait_incl_marker (lift_trait_incl FromResidual_spec_incl FromResidual_Self_SelfasTry_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FromResidual_base_spec (Self_rt) (Residual_rt) Self_st Residual_st FromResidual_Self_SelfasTry_Residual_spec_attrs-[] -[Self_ty; Residual_ty]))) ∧ (trait_incl_marker (lift_trait_incl FromResidual_spec_incl FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FromResidual_base_spec (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st Residual_st FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs-[] -[Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Residual_ty]))) ∧ (trait_incl_marker (lift_trait_incl Try_spec_incl Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Try_base_spec (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st Output_st Residual_st Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs-[] -[Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Output_ty; Residual_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl Residual_spec_incl Residual_SelfasTry_Residual_SelfasTry_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Residual_base_spec (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Residual_st Output_st Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs-[] -[Residual_ty; Output_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl Try_spec_incl Try_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Try_base_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Self_st Output_st Residual_st Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st FromResidual_Self_SelfasTry_Residual_spec_attrs FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs Try_Self_spec_attrs-[] -[Self_ty; Output_ty; Residual_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st-[] -[Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasTry_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st-[] -[Output_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasTry_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Residual_rt) Residual_st-[] -[Residual_ty])))).
  Definition trait_incl_of_Try_from_output (Self_rt: RT) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt: RT) (Output_rt: RT) (Residual_rt: RT) (Self_st: syn_type) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st: syn_type) (Output_st: syn_type) (Residual_st: syn_type) (FromResidual_Self_SelfasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Self_rt) (Residual_rt) )) (FromResidual_Self_SelfasTry_Residual_spec: (spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (Self_rt) (Residual_rt)))) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) )) (FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec: (spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt)))) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs)) (Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec: (spec_with 0 [] (Try_spec (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs: (Residual_spec_attrs (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) )) (Residual_SelfasTry_Residual_SelfasTry_Output_spec: (spec_with 0 [] (Residual_spec (RRGS:=RRGS) (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (Try_Self_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (Self_rt) (Output_rt) (Residual_rt) FromResidual_Self_SelfasTry_Residual_spec_attrs)) (Try_Self_spec: (spec_with 0 [] (Try_spec (RRGS:=RRGS) (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (DropGlue_Self_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt)))) (DropGlue_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt)))) (DropGlue_SelfasTry_Output_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt)))) (DropGlue_SelfasTry_Residual_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Residual_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Output_ty; Residual_ty]) : ([Self_rt; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt; Output_rt; Residual_rt] : list RT), ((trait_incl_marker (lift_trait_incl FromResidual_spec_incl FromResidual_Self_SelfasTry_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FromResidual_base_spec (Self_rt) (Residual_rt) Self_st Residual_st FromResidual_Self_SelfasTry_Residual_spec_attrs-[] -[Self_ty; Residual_ty]))) ∧ (trait_incl_marker (lift_trait_incl FromResidual_spec_incl FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FromResidual_base_spec (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Residual_rt) Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st Residual_st FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs-[] -[Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Residual_ty]))) ∧ (trait_incl_marker (lift_trait_incl Try_spec_incl Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Try_base_spec (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st Output_st Residual_st Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs-[] -[Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty; Output_ty; Residual_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl Residual_spec_incl Residual_SelfasTry_Residual_SelfasTry_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Residual_base_spec (Residual_rt) (Output_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Residual_st Output_st Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs-[] -[Residual_ty; Output_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl Try_spec_incl Try_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Try_base_spec (Self_rt) (Output_rt) (Residual_rt) (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Self_st Output_st Residual_st Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st FromResidual_Self_SelfasTry_Residual_spec_attrs FromResidual_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_SelfasTry_ResidualasResidualSelfasTry_Output_TryTypeasTry_Residual_spec_attrs Try_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec_attrs Residual_SelfasTry_Residual_SelfasTry_Output_spec_attrs Try_Self_spec_attrs-[] -[Self_ty; Output_ty; Residual_ty; Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasTry_ResidualasResidualSelfasTry_Output_TryType_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Residual_SelfasTry_Residual_SelfasTry_Output_TryType_rt) Residual_SelfasTry_Residual_SelfasTry_Output_TryType_st-[] -[Residual_SelfasTry_Residual_SelfasTry_Output_TryType_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasTry_Output_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st-[] -[Output_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_SelfasTry_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Residual_rt) Residual_st-[] -[Residual_ty])))).
End Try_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_Tasconvert_FromT_from (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_Tasconvert_FromT_from (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((convert_From_base_spec ((T_rt)) ((T_rt)) (T_st) (T_st) ((Tasconvert_FromT_spec_attrs (T_rt))))
    -[] -[T_ty; T_ty]).(convert_From_from_spec)   a b))) <MERGE!>.

Definition trait_incl_of_Tasconvert_IntoU_into (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (convert_From_U_T_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (U_rt) (T_rt) )) (convert_From_U_T_spec: (spec_with 0 [] (convert_From_spec (RRGS:=RRGS) (U_rt) (T_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_U_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), ((trait_incl_marker (lift_trait_incl convert_From_spec_incl convert_From_U_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), convert_From_base_spec (U_rt) (T_rt) U_st T_st convert_From_U_T_spec_attrs-[] -[U_ty; T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_U_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (U_rt) U_st-[] -[U_ty])))).

Definition type_of_Tasconvert_IntoU_into (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (convert_From_U_T_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (U_rt) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; U_ty] (scope_add_elctx (λ ϝ, []) (((convert_Into_base_spec ((T_rt)) ((U_rt)) (T_st) (U_st) ((Tasconvert_IntoU_spec_attrs (T_rt) (U_rt) (convert_From_U_T_spec_attrs))))
    -[] -[T_ty; U_ty]).(convert_Into_into_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_option_OptionTasFromResidual_from_residual (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_std_option_OptionTasFromResidual_from_residual (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((FromResidual_base_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) (unit)))) (((Option_els (T_st)) : syn_type)) (((Option_els (NeverSynType)) : syn_type)) ((std_option_OptionTasFromResidual_spec_attrs (T_rt))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty]); (Option_ty (unit) -[] -[never_t])]).(FromResidual_from_residual_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_option_OptionTasTry_branch (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_std_option_OptionTasTry_branch (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Try_base_spec (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (T_st) (((Option_els (NeverSynType)) : syn_type)) (((Option_els (T_st)) : syn_type)) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) ((std_option_OptionTasTry_spec_attrs ((T_rt)))) ((std_option_OptionasResidualT_spec_attrs ((T_rt)))) ((std_option_OptionTasTry_spec_attrs (T_rt))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty]); T_ty; (Option_ty (unit) -[] -[never_t]); (Option_ty ((T_rt)) -[] -[T_ty])]).(Try_branch_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_option_OptionTasTry_from_output (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_std_option_OptionTasTry_from_output (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((Try_base_spec (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) (((((Option_rt)) ((T_rt))))) (((Option_els (T_st)) : syn_type)) (T_st) (((Option_els (NeverSynType)) : syn_type)) (((Option_els (T_st)) : syn_type)) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) ((std_option_OptionTasFromResidual_spec_attrs ((T_rt)))) ((std_option_OptionTasTry_spec_attrs ((T_rt)))) ((std_option_OptionasResidualT_spec_attrs ((T_rt)))) ((std_option_OptionTasTry_spec_attrs (T_rt))))
    -[] -[(Option_ty ((T_rt)) -[] -[T_ty]); T_ty; (Option_ty (unit) -[] -[never_t]); (Option_ty ((T_rt)) -[] -[T_ty])]).(Try_from_output_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_result_ResultTEasTry_branch (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_E_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (E_rt) E_st-[] -[E_ty])))).

Definition type_of_std_result_ResultTEasTry_branch (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; E_ty] (scope_add_elctx (λ ϝ, []) (((Try_base_spec (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) (((((Result_rt)) ((T_rt)) ((E_rt))))) (((Result_els (T_st) (E_st)) : syn_type)) (T_st) (((Result_els (NeverSynType) (E_st)) : syn_type)) (((Result_els (T_st) (E_st)) : syn_type)) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) ((std_result_ResultTEasTry_spec_attrs ((T_rt)) ((E_rt)))) ((std_result_ResultEasResidualT_spec_attrs ((T_rt)) ((E_rt)))) ((std_result_ResultTEasTry_spec_attrs (T_rt) (E_rt))))
    -[] -[(Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]); T_ty; (Result_ty (unit) ((E_rt)) -[] -[never_t; E_ty]); (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])]).(Try_branch_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_result_ResultTEasTry_from_output (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_E_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (E_rt) E_st-[] -[E_ty])))).

Definition type_of_std_result_ResultTEasTry_from_output (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; E_ty] (scope_add_elctx (λ ϝ, []) (((Try_base_spec (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) (((((Result_rt)) ((T_rt)) ((E_rt))))) (((Result_els (T_st) (E_st)) : syn_type)) (T_st) (((Result_els (NeverSynType) (E_st)) : syn_type)) (((Result_els (T_st) (E_st)) : syn_type)) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt)))))) ((std_result_ResultTEasTry_spec_attrs ((T_rt)) ((E_rt)))) ((std_result_ResultEasResidualT_spec_attrs ((T_rt)) ((E_rt)))) ((std_result_ResultTEasTry_spec_attrs (T_rt) (E_rt))))
    -[] -[(Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]); T_ty; (Result_ty (unit) ((E_rt)) -[] -[never_t; E_ty]); (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])]).(Try_from_output_spec)   a b))) <MERGE!>.

Definition trait_incl_of_std_result_ResultTFasFromResidualstd_result_ResultE_from_residual (T_rt: RT) (E_rt: RT) (F_rt: RT) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) (convert_From_F_E_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (F_rt) (E_rt) )) (convert_From_F_E_spec: (spec_with 0 [] (convert_From_spec (RRGS:=RRGS) (F_rt) (E_rt)))) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_E_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (E_rt)))) (DropGlue_F_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty]) : ([T_rt; E_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl convert_From_spec_incl convert_From_F_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), convert_From_base_spec (F_rt) (E_rt) F_st E_st convert_From_F_E_spec_attrs-[] -[F_ty; E_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (E_rt) E_st-[] -[E_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_F_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st-[] -[F_ty])))).

Definition type_of_std_result_ResultTFasFromResidualstd_result_ResultE_from_residual (T_rt: RT) (E_rt: RT) (F_rt: RT) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) (convert_From_F_E_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (F_rt) (E_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty]) : ([T_rt; E_rt; F_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; E_ty; F_ty] (scope_add_elctx (λ ϝ, []) (((FromResidual_base_spec (((((Result_rt)) ((T_rt)) ((F_rt))))) (((((Result_rt)) (unit) ((E_rt))))) (((Result_els (T_st) (F_st)) : syn_type)) (((Result_els (NeverSynType) (E_st)) : syn_type)) ((std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs (T_rt) (E_rt) (F_rt) (convert_From_F_E_spec_attrs))))
    -[] -[(Result_ty ((T_rt)) ((F_rt)) -[] -[T_ty; F_ty]); (Result_ty (unit) ((E_rt)) -[] -[never_t; E_ty])]).(FromResidual_from_residual_spec)   a b))) <MERGE!>.

Definition trait_incl_of_ControlFlowBCasTry_branch (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) (DropGlue_B_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (DropGlue_C_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (C_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_B_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st-[] -[B_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_C_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (C_rt) C_st-[] -[C_ty])))).

Definition type_of_ControlFlowBCasTry_branch (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT),(λ a b, scope_add_typarams _ -[B_ty; C_ty] (scope_add_elctx (λ ϝ, []) (((Try_base_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((ControlFlow_st (B_st) (C_st))) (C_st) ((ControlFlow_st (B_st) (NeverSynType))) ((ControlFlow_st (B_st) (C_st))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBCasTry_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBasResidualC_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBCasTry_spec_attrs (B_rt) (C_rt))))
    -[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty]); C_ty; (ControlFlow_ty ((B_rt)) (unit) -[] -[B_ty; never_t]); (ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty])]).(Try_branch_spec)   a b))) <MERGE!>.

Definition trait_incl_of_ControlFlowBCasTry_from_output (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) (DropGlue_B_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (DropGlue_C_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (C_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_B_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st-[] -[B_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_C_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (C_rt) C_st-[] -[C_ty])))).

Definition type_of_ControlFlowBCasTry_from_output (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT),(λ a b, scope_add_typarams _ -[B_ty; C_ty] (scope_add_elctx (λ ϝ, []) (((Try_base_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((ControlFlow_st (B_st) (C_st))) (C_st) ((ControlFlow_st (B_st) (NeverSynType))) ((ControlFlow_st (B_st) (C_st))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBCasTry_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBasResidualC_spec_attrs ((B_rt)) ((C_rt)))) ((ControlFlowBCasTry_spec_attrs (B_rt) (C_rt))))
    -[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty]); C_ty; (ControlFlow_ty ((B_rt)) (unit) -[] -[B_ty; never_t]); (ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty])]).(Try_from_output_spec)   a b))) <MERGE!>.

Definition trait_incl_of_ControlFlowBCasFromResidualControlFlowB_from_residual (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) (DropGlue_B_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (DropGlue_C_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (C_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_B_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st-[] -[B_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_C_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (C_rt) C_st-[] -[C_ty])))).

Definition type_of_ControlFlowBCasFromResidualControlFlowB_from_residual (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT),(λ a b, scope_add_typarams _ -[B_ty; C_ty] (scope_add_elctx (λ ϝ, []) (((FromResidual_base_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))) (((ControlFlow_rt ((B_rt)) (unit)))) ((ControlFlow_st (B_st) (C_st))) ((ControlFlow_st (B_st) (NeverSynType))) ((ControlFlowBCasFromResidualControlFlowB_spec_attrs (B_rt) (C_rt))))
    -[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty]); (ControlFlow_ty ((B_rt)) (unit) -[] -[B_ty; never_t])]).(FromResidual_from_residual_spec)   a b))) <MERGE!>.

Definition trait_incl_of_ControlFlow_BC_break_value (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) (DropGlue_B_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (DropGlue_C_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (C_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_B_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st-[] -[B_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_C_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (C_rt) C_st-[] -[C_ty])))).

Definition type_of_ControlFlow_BC_break_value (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[B_ty; C_ty]) : ([(B_rt, B_st); (C_rt, C_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, match self with | Ok _ => None | Err x => Some x end @ (Option_ty ((B_rt)) -[] -[B_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_drop_glue_ControlFlow (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) (DropGlue_B_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (B_rt)))) (DropGlue_C_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (C_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_B_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (B_rt) B_st-[] -[B_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_C_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (C_rt) C_st-[] -[C_ty])))).

Definition type_of_drop_glue_ControlFlow (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT),(λ a b, scope_add_typarams _ -[B_ty; C_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((ControlFlow_st (B_st) (C_st))))
    -[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.




End specs.
Section ControlFlowBasResidualC_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition ControlFlowBasResidualC_spec (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) : (spec_with _ _ (Residual_spec (((ControlFlow_rt ((B_rt)) (unit)))) ((C_rt)) (((ControlFlow_rt ((B_rt)) ((C_rt))))))) :=
    spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (@mk_Residual_spec _ _ (((ControlFlow_rt ((B_rt)) (unit)))) ((C_rt)) (((ControlFlow_rt ((B_rt)) ((C_rt)))))).
  Definition ControlFlowBasResidualC_spec_subsumption  :=
    ∀ `(B_rt : !RT) `(C_rt : !RT) `(B_st : !syn_type) `(C_st : !syn_type), trait_incl_marker (lift_trait_incl Residual_spec_incl (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (ControlFlowBasResidualC_spec (B_rt) (C_rt) (B_st) (C_st))-[] -[B_ty; C_ty]) (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), scope_add_typarams _ -[B_ty; C_ty] ((Residual_base_spec ((ControlFlow_rt ((B_rt)) (unit))) (C_rt) ((ControlFlow_rt ((B_rt)) ((C_rt)))) (ControlFlow_st (B_st) (NeverSynType)) C_st (ControlFlow_st (B_st) (C_st)) (ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt))) (ControlFlowBCasTry_spec_attrs ((B_rt)) ((C_rt))) (ControlFlowBasResidualC_spec_attrs (B_rt) (C_rt))-[] -[(ControlFlow_ty ((B_rt)) (unit) -[] -[B_ty; never_t]); C_ty; (ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty])])))).
End ControlFlowBasResidualC_spec.

Section ControlFlowBCasFromResidualControlFlowB_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition ControlFlowBCasFromResidualControlFlowB_spec (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) : (spec_with _ _ (FromResidual_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))) (((ControlFlow_rt ((B_rt)) (unit)))))) :=
    spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), {|
        FromResidual_from_residual_spec  :=
          (type_of_ControlFlowBCasFromResidualControlFlowB_from_residual ((B_rt)) ((C_rt)) (B_st) (C_st)) 
             <TY> B_ty <TY> C_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition ControlFlowBCasFromResidualControlFlowB_spec_subsumption  :=
    ∀ `(B_rt : !RT) `(C_rt : !RT) `(B_st : !syn_type) `(C_st : !syn_type), trait_incl_marker (lift_trait_incl FromResidual_spec_incl (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (ControlFlowBCasFromResidualControlFlowB_spec (B_rt) (C_rt) (B_st) (C_st))-[] -[B_ty; C_ty]) (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), scope_add_typarams _ -[B_ty; C_ty] ((FromResidual_base_spec ((ControlFlow_rt ((B_rt)) ((C_rt)))) ((ControlFlow_rt ((B_rt)) (unit))) (ControlFlow_st (B_st) (C_st)) (ControlFlow_st (B_st) (NeverSynType)) (ControlFlowBCasFromResidualControlFlowB_spec_attrs (B_rt) (C_rt))-[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty]); (ControlFlow_ty ((B_rt)) (unit) -[] -[B_ty; never_t])])))).
End ControlFlowBCasFromResidualControlFlowB_spec.

Section ControlFlowBCasTry_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition ControlFlowBCasTry_spec (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) : (spec_with _ _ (Try_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))) ((C_rt)) (((ControlFlow_rt ((B_rt)) (unit)))) (((ControlFlow_rt ((B_rt)) ((C_rt))))))) :=
    spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), let Residual_rt := ((ControlFlow_rt ((B_rt)) (unit))) in let Output_rt := (C_rt) in {|
        Try_branch_spec  :=
          (type_of_ControlFlowBCasTry_branch ((B_rt)) ((C_rt)) (B_st) (C_st)) 
             <TY> B_ty <TY> C_ty : (spec_with 0 [] fn_spec);
        Try_from_output_spec  :=
          (type_of_ControlFlowBCasTry_from_output ((B_rt)) ((C_rt)) (B_st) (C_st)) 
             <TY> B_ty <TY> C_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition ControlFlowBCasTry_spec_subsumption  :=
    ∀ `(B_rt : !RT) `(C_rt : !RT) `(B_st : !syn_type) `(C_st : !syn_type), trait_incl_marker (lift_trait_incl Try_spec_incl (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (ControlFlowBCasTry_spec (B_rt) (C_rt) (B_st) (C_st))-[] -[B_ty; C_ty]) (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), scope_add_typarams _ -[B_ty; C_ty] ((Try_base_spec ((ControlFlow_rt ((B_rt)) ((C_rt)))) (C_rt) ((ControlFlow_rt ((B_rt)) (unit))) ((ControlFlow_rt ((B_rt)) ((C_rt)))) (ControlFlow_st (B_st) (C_st)) C_st (ControlFlow_st (B_st) (NeverSynType)) (ControlFlow_st (B_st) (C_st)) (ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt))) (ControlFlowBCasFromResidualControlFlowB_spec_attrs ((B_rt)) ((C_rt))) (ControlFlowBCasTry_spec_attrs ((B_rt)) ((C_rt))) (ControlFlowBasResidualC_spec_attrs ((B_rt)) ((C_rt))) (ControlFlowBCasTry_spec_attrs (B_rt) (C_rt))-[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty]); C_ty; (ControlFlow_ty ((B_rt)) (unit) -[] -[B_ty; never_t]); (ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty])])))).
End ControlFlowBCasTry_spec.

Section Tasconvert_FromT_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition Tasconvert_FromT_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (convert_From_spec ((T_rt)) ((T_rt)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        convert_From_from_spec  :=
          (type_of_Tasconvert_FromT_from ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition Tasconvert_FromT_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl convert_From_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Tasconvert_FromT_spec (T_rt) (T_st))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((convert_From_base_spec (T_rt) (T_rt) T_st T_st (Tasconvert_FromT_spec_attrs (T_rt))-[] -[T_ty; T_ty])))).
End Tasconvert_FromT_spec.

Section Tasconvert_IntoU_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition Tasconvert_IntoU_spec (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (convert_From_U_T_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (U_rt) (T_rt) )) : (spec_with _ _ (convert_Into_spec ((T_rt)) ((U_rt)))) :=
    spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), {|
        convert_Into_into_spec  :=
          (type_of_Tasconvert_IntoU_into ((T_rt)) ((U_rt)) (T_st) (U_st)) convert_From_U_T_spec_attrs 
             <TY> T_ty <TY> U_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition Tasconvert_IntoU_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(U_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(convert_From_U_T_spec_attrs : !(convert_From_spec_attrs (RRGS:=RRGS) (U_rt) (T_rt) )), trait_incl_marker (lift_trait_incl convert_Into_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), (Tasconvert_IntoU_spec (T_rt) (U_rt) (T_st) (U_st) (convert_From_U_T_spec_attrs))-[] -[T_ty; U_ty]) (spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), scope_add_typarams _ -[T_ty; U_ty] ((convert_Into_base_spec (T_rt) (U_rt) T_st U_st (Tasconvert_IntoU_spec_attrs (T_rt) (U_rt) (convert_From_U_T_spec_attrs))-[] -[T_ty; U_ty])))).
End Tasconvert_IntoU_spec.

Section std_option_OptionasResidualT_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionasResidualT_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Residual_spec (((((Option_rt)) (unit)))) ((T_rt)) (((((Option_rt)) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Residual_spec _ _ (((((Option_rt)) (unit)))) ((T_rt)) (((((Option_rt)) ((T_rt)))))).
  Definition std_option_OptionasResidualT_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Residual_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionasResidualT_spec (T_rt) (T_st))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Residual_base_spec ((((Option_rt)) (unit))) (T_rt) ((((Option_rt)) ((T_rt)))) ((Option_els (NeverSynType)) : syn_type) T_st ((Option_els (T_st)) : syn_type) (std_option_OptionTasFromResidual_spec_attrs ((T_rt))) (std_option_OptionTasTry_spec_attrs ((T_rt))) (std_option_OptionasResidualT_spec_attrs (T_rt))-[] -[(Option_ty (unit) -[] -[never_t]); T_ty; (Option_ty ((T_rt)) -[] -[T_ty])])))).
End std_option_OptionasResidualT_spec.

Section std_option_OptionTasFromResidual_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionTasFromResidual_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (FromResidual_spec (((((Option_rt)) ((T_rt))))) (((((Option_rt)) (unit)))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        FromResidual_from_residual_spec  :=
          (type_of_std_option_OptionTasFromResidual_from_residual ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition std_option_OptionTasFromResidual_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl FromResidual_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionTasFromResidual_spec (T_rt) (T_st))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((FromResidual_base_spec ((((Option_rt)) ((T_rt)))) ((((Option_rt)) (unit))) ((Option_els (T_st)) : syn_type) ((Option_els (NeverSynType)) : syn_type) (std_option_OptionTasFromResidual_spec_attrs (T_rt))-[] -[(Option_ty ((T_rt)) -[] -[T_ty]); (Option_ty (unit) -[] -[never_t])])))).
End std_option_OptionTasFromResidual_spec.

Section std_option_OptionTasTry_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_option_OptionTasTry_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Try_spec (((((Option_rt)) ((T_rt))))) ((T_rt)) (((((Option_rt)) (unit)))) (((((Option_rt)) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), let Residual_rt := ((((Option_rt)) (unit))) in let Output_rt := (T_rt) in {|
        Try_branch_spec  :=
          (type_of_std_option_OptionTasTry_branch ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 0 [] fn_spec);
        Try_from_output_spec  :=
          (type_of_std_option_OptionTasTry_from_output ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition std_option_OptionTasTry_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Try_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_option_OptionTasTry_spec (T_rt) (T_st))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((Try_base_spec ((((Option_rt)) ((T_rt)))) (T_rt) ((((Option_rt)) (unit))) ((((Option_rt)) ((T_rt)))) ((Option_els (T_st)) : syn_type) T_st ((Option_els (NeverSynType)) : syn_type) ((Option_els (T_st)) : syn_type) (std_option_OptionTasFromResidual_spec_attrs ((T_rt))) (std_option_OptionTasFromResidual_spec_attrs ((T_rt))) (std_option_OptionTasTry_spec_attrs ((T_rt))) (std_option_OptionasResidualT_spec_attrs ((T_rt))) (std_option_OptionTasTry_spec_attrs (T_rt))-[] -[(Option_ty ((T_rt)) -[] -[T_ty]); T_ty; (Option_ty (unit) -[] -[never_t]); (Option_ty ((T_rt)) -[] -[T_ty])])))).
End std_option_OptionTasTry_spec.

Section std_result_ResultEasResidualT_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_result_ResultEasResidualT_spec (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) : (spec_with _ _ (Residual_spec (((((Result_rt)) (unit) ((E_rt))))) ((T_rt)) (((((Result_rt)) ((T_rt)) ((E_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (@mk_Residual_spec _ _ (((((Result_rt)) (unit) ((E_rt))))) ((T_rt)) (((((Result_rt)) ((T_rt)) ((E_rt)))))).
  Definition std_result_ResultEasResidualT_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type), trait_incl_marker (lift_trait_incl Residual_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (std_result_ResultEasResidualT_spec (T_rt) (E_rt) (T_st) (E_st))-[] -[T_ty; E_ty]) (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), scope_add_typarams _ -[T_ty; E_ty] ((Residual_base_spec ((((Result_rt)) (unit) ((E_rt)))) (T_rt) ((((Result_rt)) ((T_rt)) ((E_rt)))) ((Result_els (NeverSynType) (E_st)) : syn_type) T_st ((Result_els (T_st) (E_st)) : syn_type) (std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt))))) (std_result_ResultTEasTry_spec_attrs ((T_rt)) ((E_rt))) (std_result_ResultEasResidualT_spec_attrs (T_rt) (E_rt))-[] -[(Result_ty (unit) ((E_rt)) -[] -[never_t; E_ty]); T_ty; (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])])))).
End std_result_ResultEasResidualT_spec.

Section std_result_ResultTEasTry_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_result_ResultTEasTry_spec (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) : (spec_with _ _ (Try_spec (((((Result_rt)) ((T_rt)) ((E_rt))))) ((T_rt)) (((((Result_rt)) (unit) ((E_rt))))) (((((Result_rt)) ((T_rt)) ((E_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), let Residual_rt := ((((Result_rt)) (unit) ((E_rt)))) in let Output_rt := (T_rt) in {|
        Try_branch_spec  :=
          (type_of_std_result_ResultTEasTry_branch ((T_rt)) ((E_rt)) (T_st) (E_st)) 
             <TY> T_ty <TY> E_ty : (spec_with 0 [] fn_spec);
        Try_from_output_spec  :=
          (type_of_std_result_ResultTEasTry_from_output ((T_rt)) ((E_rt)) (T_st) (E_st)) 
             <TY> T_ty <TY> E_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition std_result_ResultTEasTry_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type), trait_incl_marker (lift_trait_incl Try_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (std_result_ResultTEasTry_spec (T_rt) (E_rt) (T_st) (E_st))-[] -[T_ty; E_ty]) (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), scope_add_typarams _ -[T_ty; E_ty] ((Try_base_spec ((((Result_rt)) ((T_rt)) ((E_rt)))) (T_rt) ((((Result_rt)) (unit) ((E_rt)))) ((((Result_rt)) ((T_rt)) ((E_rt)))) ((Result_els (T_st) (E_st)) : syn_type) T_st ((Result_els (NeverSynType) (E_st)) : syn_type) ((Result_els (T_st) (E_st)) : syn_type) (std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt))))) (std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs ((T_rt)) ((E_rt)) ((E_rt)) ((Tasconvert_FromT_spec_attrs ((E_rt))))) (std_result_ResultTEasTry_spec_attrs ((T_rt)) ((E_rt))) (std_result_ResultEasResidualT_spec_attrs ((T_rt)) ((E_rt))) (std_result_ResultTEasTry_spec_attrs (T_rt) (E_rt))-[] -[(Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]); T_ty; (Result_ty (unit) ((E_rt)) -[] -[never_t; E_ty]); (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])])))).
End std_result_ResultTEasTry_spec.

Section std_result_ResultTFasFromResidualstd_result_ResultE_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_result_ResultTFasFromResidualstd_result_ResultE_spec (T_rt: RT) (E_rt: RT) (F_rt: RT) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) (convert_From_F_E_spec_attrs: (convert_From_spec_attrs (RRGS:=RRGS) (F_rt) (E_rt) )) : (spec_with _ _ (FromResidual_spec (((((Result_rt)) ((T_rt)) ((F_rt))))) (((((Result_rt)) (unit) ((E_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty]) : ([T_rt; E_rt; F_rt] : list RT), {|
        FromResidual_from_residual_spec  :=
          (type_of_std_result_ResultTFasFromResidualstd_result_ResultE_from_residual ((T_rt)) ((E_rt)) ((F_rt)) (T_st) (E_st) (F_st)) convert_From_F_E_spec_attrs 
             <TY> T_ty <TY> E_ty <TY> F_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition std_result_ResultTFasFromResidualstd_result_ResultE_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(E_rt : !RT) `(F_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(F_st : !syn_type) `(convert_From_F_E_spec_attrs : !(convert_From_spec_attrs (RRGS:=RRGS) (F_rt) (E_rt) )), trait_incl_marker (lift_trait_incl FromResidual_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty]) : ([T_rt; E_rt; F_rt] : list RT), (std_result_ResultTFasFromResidualstd_result_ResultE_spec (T_rt) (E_rt) (F_rt) (T_st) (E_st) (F_st) (convert_From_F_E_spec_attrs))-[] -[T_ty; E_ty; F_ty]) (spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty]) : ([T_rt; E_rt; F_rt] : list RT), scope_add_typarams _ -[T_ty; E_ty; F_ty] ((FromResidual_base_spec ((((Result_rt)) ((T_rt)) ((F_rt)))) ((((Result_rt)) (unit) ((E_rt)))) ((Result_els (T_st) (F_st)) : syn_type) ((Result_els (NeverSynType) (E_st)) : syn_type) (std_result_ResultTFasFromResidualstd_result_ResultE_spec_attrs (T_rt) (E_rt) (F_rt) (convert_From_F_E_spec_attrs))-[] -[(Result_ty ((T_rt)) ((F_rt)) -[] -[T_ty; F_ty]); (Result_ty (unit) ((E_rt)) -[] -[never_t; E_ty])])))).
End std_result_ResultTFasFromResidualstd_result_ResultE_spec.

Section drop_glue_ControlFlow_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_ControlFlow_spec (B_rt: RT) (C_rt: RT) (B_st: syn_type) (C_st: syn_type) : (spec_with _ _ (DropGlue_spec (((ControlFlow_rt ((B_rt)) ((C_rt))))))) :=
    spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_ControlFlow ((B_rt)) ((C_rt)) (B_st) (C_st)) 
             <TY> B_ty <TY> C_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition drop_glue_ControlFlow_spec_subsumption  :=
    ∀ `(B_rt : !RT) `(C_rt : !RT) `(B_st : !syn_type) `(C_st : !syn_type), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), (drop_glue_ControlFlow_spec (B_rt) (C_rt) (B_st) (C_st))-[] -[B_ty; C_ty]) (spec! ( *[]) : 0 | ( *[B_ty; C_ty]) : ([B_rt; C_rt] : list RT), scope_add_typarams _ -[B_ty; C_ty] ((DropGlue_base_spec ((ControlFlow_rt ((B_rt)) ((C_rt)))) (ControlFlow_st (B_st) (C_st))-[] -[(ControlFlow_ty ((B_rt)) ((C_rt)) -[] -[B_ty; C_ty])])))).
End drop_glue_ControlFlow_spec.

