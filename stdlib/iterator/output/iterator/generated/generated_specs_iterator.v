From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.iterator.theories Require Export iterator map step.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.iterator.iterator Require Export generated_code_iterator.

Definition traits_iterator_FromIterator_FromSequence_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (A_rt: RT) :=
  (list ((RT_xt (A_rt))) → (RT_xt (Self_rt))).
Record traits_iterator_FromIterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{A_rt : !RT} : Type := mk_traits_iterator_FromIterator_spec_attrs {
  traits_iterator_FromIterator_FromSequence  : (traits_iterator_FromIterator_FromSequence_sig (Self_rt) (A_rt));
}.
#[global] Arguments traits_iterator_FromIterator_spec_attrs : clear implicits.

#[global] Arguments traits_iterator_FromIterator_spec_attrs {_ _}.

#[global] Arguments mk_traits_iterator_FromIterator_spec_attrs  {_} {_} {_} {_}.


Definition traits_iterator_IntoIterator_IntoIter_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (IntoIter_rt: RT) (Item_rt: RT) :=
  ((RT_xt (Self_rt)) → (RT_xt (IntoIter_rt))).
Record traits_iterator_IntoIterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{IntoIter_rt : !RT} `{Item_rt : !RT} : Type := mk_traits_iterator_IntoIterator_spec_attrs {
  traits_iterator_IntoIterator_IntoIter  : (traits_iterator_IntoIterator_IntoIter_sig (Self_rt) (IntoIter_rt) (Item_rt));
}.
#[global] Arguments traits_iterator_IntoIterator_spec_attrs : clear implicits.

#[global] Arguments traits_iterator_IntoIterator_spec_attrs {_ _}.

#[global] Arguments mk_traits_iterator_IntoIterator_spec_attrs  {_} {_} {_} {_} {_}.




Definition step_Step_Forward_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) :=
  ((RT_xt (Self_rt)) → nat → option (RT_xt (Self_rt))).
Definition step_Step_Backward_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Forward: (step_Step_Forward_sig (Self_rt) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) :=
  ((RT_xt (Self_rt)) → nat → option (RT_xt (Self_rt))).
Definition step_Step_StepsBetween_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Forward: (step_Step_Forward_sig (Self_rt) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs))) (step_Step_Backward: (step_Step_Backward_sig (Self_rt) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (step_Step_Forward))) :=
  ((RT_xt (Self_rt)) → (RT_xt (Self_rt)) → plist (RT_xt ∘ place_rfnRT) [ZRT; optionRT ZRT]).
Record step_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Clone_Self_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )} `{PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )} `{PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)} : Type := mk_step_Step_spec_attrs {
  step_Step_Forward  : (step_Step_Forward_sig (Self_rt) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs));
  step_Step_Backward  : (step_Step_Backward_sig (Self_rt) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (step_Step_Forward));
  step_Step_StepsBetween  : (step_Step_StepsBetween_sig (Self_rt) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (step_Step_Forward) (step_Step_Backward));
}.
#[global] Arguments step_Step_spec_attrs : clear implicits.

#[global] Arguments step_Step_spec_attrs {_ _}.

#[global] Arguments mk_step_Step_spec_attrs  {_} {_} {_} {_} {_} {_}.


Record step_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Clone_Self_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )} `{PartialEq_Self_Self_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )} `{PartialOrd_Self_Self_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)} `{Copy_Self_spec_attrs : !(Copy_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs)} `{step_Step_Self_spec_attrs : !(step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)} : Type := mk_step_TrustedStep_spec_attrs {
}.
#[global] Arguments step_TrustedStep_spec_attrs : clear implicits.

#[global] Arguments step_TrustedStep_spec_attrs {_ _}.

#[global] Arguments mk_step_TrustedStep_spec_attrs  {_} {_} {_} {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition Iastraits_iterator_IntoIterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (I_rt: RT) (traits_iterator_Iterator_I_Item_rt: RT) (traits_iterator_Iterator_I_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt) )) : ((traits_iterator_IntoIterator_spec_attrs ((I_rt)) ((I_rt)) ((traits_iterator_Iterator_I_Item_rt)))) :=
  {|
    traits_iterator_IntoIterator_IntoIter  :=
      (id) : ((traits_iterator_IntoIterator_IntoIter_sig ((I_rt)) ((I_rt)) ((traits_iterator_Iterator_I_Item_rt))));
  |}
.


End attrs.

Section adapters_map_Map_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (I_rt : RT) (F_rt : RT).


Definition adapters_map_Map_ty  : (spec_with 0 [(I_rt); (F_rt)] ((type (plist place_rfnRT [(I_rt) : RT; (F_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[I_ty; F_ty]) : ([I_rt; F_rt] : list RT), ((struct_t (adapters_map_Map_sls ((I_ty.(ty_syn_type) (MetaNone))) ((F_ty.(ty_syn_type) (MetaNone)))) +[(I_ty); (F_ty)]))).
Defined.

Definition adapters_map_Map_rt  : RT.
Proof using I_rt F_rt .
  let __a := (normalized_rt_of_spec_ty (adapters_map_Map_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent adapters_map_Map_ty.
#[global] Typeclasses Transparent adapters_map_Map_rt.
End adapters_map_Map_ty.
Global Arguments adapters_map_Map_rt : clear implicits.
Section adapters_map_Map_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (I_rt : RT) (F_rt : RT).

  Program Definition adapters_map_Map_inv_t_inv_spec  : spec_with 0 [I_rt; F_rt] (ex_inv_def ((adapters_map_Map_rt (I_rt) (F_rt)))%type ((MapXRT (I_rt) (F_rt)))%type) := spec! ( *[]) : 0 | ( *[I_ty; F_ty]) : ([I_rt; F_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((MapXRT (I_rt) (F_rt))%type : RT)),
            let 'x := _ty_rfn in ⌜inner_rfn = -[#($# x.(map_it)); #($# x.(map_clos))]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition adapters_map_Map_inv_t  : spec_with 0 [I_rt; F_rt] (type ((MapXRT (I_rt) (F_rt)))%type) :=
    spec! ( *[]) : 0 | ( *[I_ty; F_ty]) : ([I_rt; F_rt] : list RT), ex_plain_t _ _ (adapters_map_Map_inv_t_inv_spec   <TY> I_ty <TY> F_ty <INST!>) ((adapters_map_Map_ty (I_rt) (F_rt))  <TY> I_ty <TY> F_ty <INST!>).
  Global Typeclasses Transparent adapters_map_Map_inv_t.
  Definition adapters_map_Map_inv_t_rt : RT.
  Proof using I_rt F_rt . let __a := normalized_rt_of_spec_ty adapters_map_Map_inv_t in exact __a. Defined.
  Global Typeclasses Transparent adapters_map_Map_inv_t_rt.
End adapters_map_Map_inv_t.
Global Arguments adapters_map_Map_inv_t_rt : clear implicits.

Section adapters_skip_Skip_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (I_rt : RT).


Definition adapters_skip_Skip_ty  : (spec_with 0 [(I_rt)] ((type (plist place_rfnRT [(I_rt) : RT; Z : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), ((struct_t (adapters_skip_Skip_sls ((I_ty.(ty_syn_type) (MetaNone)))) +[(I_ty); ((int USize))]))).
Defined.

Definition adapters_skip_Skip_rt  : RT.
Proof using I_rt .
  let __a := (normalized_rt_of_spec_ty (adapters_skip_Skip_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent adapters_skip_Skip_ty.
#[global] Typeclasses Transparent adapters_skip_Skip_rt.
End adapters_skip_Skip_ty.
Global Arguments adapters_skip_Skip_rt : clear implicits.
Section adapters_skip_Skip_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (I_rt : RT).

  Program Definition adapters_skip_Skip_inv_t_inv_spec  : spec_with 0 [I_rt] (ex_inv_def ((adapters_skip_Skip_rt (I_rt)))%type (((_ * nat)))%type) := spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((_ * nat))%type : RT)),
            let '(it, n) := _ty_rfn in ⌜inner_rfn = -[#(it); #(Z.of_nat n)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition adapters_skip_Skip_inv_t  : spec_with 0 [I_rt] (type (((_ * nat)))%type) :=
    spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), ex_plain_t _ _ (adapters_skip_Skip_inv_t_inv_spec   <TY> I_ty <INST!>) ((adapters_skip_Skip_ty (I_rt))  <TY> I_ty <INST!>).
  Global Typeclasses Transparent adapters_skip_Skip_inv_t.
  Definition adapters_skip_Skip_inv_t_rt : RT.
  Proof using I_rt . let __a := normalized_rt_of_spec_ty adapters_skip_Skip_inv_t in exact __a. Defined.
  Global Typeclasses Transparent adapters_skip_Skip_inv_t_rt.
End adapters_skip_Skip_inv_t.
Global Arguments adapters_skip_Skip_inv_t_rt : clear implicits.

Section adapters_take_Take_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (I_rt : RT).


Definition adapters_take_Take_ty  : (spec_with 0 [(I_rt)] ((type (plist place_rfnRT [(I_rt) : RT; Z : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), ((struct_t (adapters_take_Take_sls ((I_ty.(ty_syn_type) (MetaNone)))) +[(I_ty); ((int USize))]))).
Defined.

Definition adapters_take_Take_rt  : RT.
Proof using I_rt .
  let __a := (normalized_rt_of_spec_ty (adapters_take_Take_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent adapters_take_Take_ty.
#[global] Typeclasses Transparent adapters_take_Take_rt.
End adapters_take_Take_ty.
Global Arguments adapters_take_Take_rt : clear implicits.
Section adapters_take_Take_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (I_rt : RT).

  Program Definition adapters_take_Take_inv_t_inv_spec  : spec_with 0 [I_rt] (ex_inv_def ((adapters_take_Take_rt (I_rt)))%type (((_ * nat)))%type) := spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((_ * nat))%type : RT)),
            let '(it, n) := _ty_rfn in ⌜inner_rfn = -[#(it); #(Z.of_nat n)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition adapters_take_Take_inv_t  : spec_with 0 [I_rt] (type (((_ * nat)))%type) :=
    spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), ex_plain_t _ _ (adapters_take_Take_inv_t_inv_spec   <TY> I_ty <INST!>) ((adapters_take_Take_ty (I_rt))  <TY> I_ty <INST!>).
  Global Typeclasses Transparent adapters_take_Take_inv_t.
  Definition adapters_take_Take_inv_t_rt : RT.
  Proof using I_rt . let __a := normalized_rt_of_spec_ty adapters_take_Take_inv_t in exact __a. Defined.
  Global Typeclasses Transparent adapters_take_Take_inv_t_rt.
End adapters_take_Take_inv_t.
Global Arguments adapters_take_Take_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (MB_rt: RT) (MI_rt: RT) (MF_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) : ((traits_iterator_Iterator_spec_attrs (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)))) :=
  {|
    traits_iterator_Iterator_Params  :=
      ((traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Params) * (RT_xt (tuple1_rt (traits_iterator_Iterator_MI_Item_rt)) → FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Params) → Prop))%type) : ((traits_iterator_Iterator_Params_sig (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt))));
    traits_iterator_Iterator_Inv  :=
      (MapInv traits_iterator_Iterator_MI_spec_attrs FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut)) : ((traits_iterator_Iterator_Inv_sig (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) (_)));
    traits_iterator_Iterator_Next  :=
      ((λ π '(p_inner, ParamPred) s1 e s2, 
                if_iNone e (traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Next) π p_inner s1.(map_it) None s2.(map_it)) ∗
                if_iSome e (λ e, ∃ e_inner,
                    (traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Next) π p_inner s1.(map_it) (Some e_inner) s2.(map_it)) ∗
                    ∃ p_clos, ⌜ParamPred *[e_inner] p_clos⌝ ∗ boringly (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π p_clos s1.(map_clos) *[e_inner]) ∗
                    (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π p_clos s1.(map_clos) *[e_inner] s2.(map_clos) e)
                    ))%I) : ((traits_iterator_Iterator_Next_sig (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) : ((traits_iterator_Iterator_spec_attrs (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)))) :=
  {|
    traits_iterator_Iterator_Params  :=
      (traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Params)) : ((traits_iterator_Iterator_Params_sig (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt))));
    traits_iterator_Iterator_Inv  :=
      (λ π p s, traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Inv) π p s.1) : ((traits_iterator_Iterator_Inv_sig (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) (_)));
    traits_iterator_Iterator_Next  :=
      ((λ π p_inner s1 e s2, 
                if_iNone e (
                     ∃ seq s2_inner, 
                        ⌜length seq ≤ s1.2⌝ ∗ ⌜s2.2 = 0%nat⌝∗ 
                        IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.1 seq s2_inner ∗
                        traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Next) π p_inner s2_inner None s2.1) ∗ 
                if_iSome e (λ e, 
                    ∃ seq s2_inner, 
                        ⌜length seq = s1.2⌝ ∗ ⌜s2.2 = 0%nat⌝∗ 
                        IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.1 seq s2_inner ∗
                        traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Next) π p_inner s2_inner (Some e) s2.1))%I) : ((traits_iterator_Iterator_Next_sig (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) : ((traits_iterator_Iterator_spec_attrs (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)))) :=
  {|
    traits_iterator_Iterator_Params  :=
      (traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Params)) : ((traits_iterator_Iterator_Params_sig (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt))));
    traits_iterator_Iterator_Inv  :=
      (λ π p s, traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Inv) π p s.1) : ((traits_iterator_Iterator_Inv_sig (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) (_)));
    traits_iterator_Iterator_Next  :=
      ((λ π p_inner s1 e s2, 
                if_iNone e (
                    (⌜s1.2 = 0%nat⌝ ∗ True) ∨ (⌜s1.2 ≠ 0%nat⌝ ∗ ⌜s2.2 = (s1.2 - 1)%nat⌝ ∗ traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Next) π p_inner s1.1 None s2.1)) ∗ 
                if_iSome e (λ e, ⌜s1.2 > 0%nat⌝ ∗ ⌜s2.2 = (s1.2 - 1)%nat⌝ ∗ traits_iterator_Iterator_MI_spec_attrs.(traits_iterator_Iterator_Next) π p_inner s1.1 (Some e) s2.1))%I) : ((traits_iterator_Iterator_Next_sig (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ i128) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ i128) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ i16) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ i16) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ i32) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ i32) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ i64) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ i64) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ i8) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ i8) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ isize) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ isize) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ i128) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ u128) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ u16) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ u16) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ u32) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ u32) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ u64) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ u64) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ u8) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ u8) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasstep_Step_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_Step_spec_attrs (Z) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs))) :=
  {|
    step_Step_Forward  :=
      (λ a b, if bool_decide (a + b ∈ usize) then Some (a + b) else None) : ((step_Step_Forward_sig (Z) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs)));
    step_Step_Backward  :=
      (λ a b, if bool_decide (a - b ∈ usize) then Some (a - b) else None) : ((step_Step_Backward_sig (Z) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_)));
    step_Step_StepsBetween  :=
      (λ a b, if bool_decide (a ≤ b) then *[b - a; Some (b-a)] else *[0; None]) : ((step_Step_StepsBetween_sig (Z) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (step_Step_A_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (A_rt) Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs)) : ((traits_iterator_Iterator_spec_attrs (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)))) :=
  {|
    traits_iterator_Iterator_Params  :=
      (unit) : ((traits_iterator_Iterator_Params_sig (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt))));
    traits_iterator_Iterator_Inv  :=
      (λ π _ s, True%I) : ((traits_iterator_Iterator_Inv_sig (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (_)));
    traits_iterator_Iterator_Next  :=
      (λ π _ s1 e s2, ⌜s1.2 = s2.2 ∧ 
            if_None e (s1 = s2 ∧ s1.1 = s1.2) ∧ 
            if_Some e (λ e, s1.1 = e ∧ Some s2.1 = (step_Step_A_spec_attrs.(step_Step_Forward) s1.1 1)%nat ∧ PartialOrd_A_A_spec_attrs.(PartialOrd_POrd) s1.1 s1.2 = Some Less)⌝%I) : ((traits_iterator_Iterator_Next_sig (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (i128asCopy_spec_attrs) (i128asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (i16asCopy_spec_attrs) (i16asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (i32asCopy_spec_attrs) (i32asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (i64asCopy_spec_attrs) (i64asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (i8asCopy_spec_attrs) (i8asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (isizeasCopy_spec_attrs) (isizeasstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (u128asCopy_spec_attrs) (u128asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (u16asCopy_spec_attrs) (u16asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (u32asCopy_spec_attrs) (u32asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (u64asCopy_spec_attrs) (u64asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (u8asCopy_spec_attrs) (u8asstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasstep_TrustedStep_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((step_TrustedStep_spec_attrs (Z) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (usizeasCopy_spec_attrs) (usizeasstep_Step_spec_attrs))) :=
  mk_step_TrustedStep_spec_attrs.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition traits_iterator_Iterator_all_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : ((FnOnce_spec_attrs ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))))) :=
  {|
    FnOnce_Params  :=
      ((plist id [_ : Type])) : ((FnOnce_Params_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit))))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _), (∃ (pclos: _) (_arg_0: _) (b: _) (_γf: gname) (__γclos: gname) (capture_f_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_args = *[ _arg_0; b ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_f_), _γf))]))%Z⌝)
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_f_ *[b])
      ∗ (True))%I) : ((FnOnce_Pre_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_ret: _), (∃ (pclos: _) (_arg_0: _) (b: _) (_γf: gname) (__γclos: gname) (capture_f_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_f_), _γf))]))%Z⌝)
      ∗ (⌜(_args = *[ _arg_0; b ])%Z⌝)
      ∗ (∃ (res: (bool)) (capture_f__new: (RT_xt ((F_rt)))), (⌜(_ret = (if res then Ok tt else Err tt))%Z⌝)
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_f_ *[b] capture_f__new res)
      ∗ (gvar_pobs _γf ($#@{(F_rt)} capture_f__new)))
      ∗ (True))%I) : ((FnOnce_Post_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (pclos: _) (_arg_0: _) (b: _) (_γf: gname) (__γclos: gname) (capture_f_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_f_), _γf))]))%Z⌝)
      ∗ (⌜(_args = *[ _arg_0; b ])%Z⌝)
      ∗ (∃ (res: (bool)) (capture_f__new: (RT_xt ((F_rt)))), (⌜(_ret = (if res then Ok tt else Err tt))%Z⌝)
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_f_ *[b] capture_f__new res)
      ∗ (⌜(_self_post = ( *[((capture_f__new), _γf)]))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))) (_) (_) (_)));
  |}
.


Program Definition traits_iterator_Iterator_all_closure0_FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : ((FnMut_spec_attrs ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))))) :=
  mk_FnMut_spec_attrs.


Program Definition traits_iterator_Iterator_max_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : ((FnOnce_spec_attrs (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
  {|
    FnOnce_Params  :=
      ((plist id [])) : ((FnOnce_Params_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt))))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _), (∃ (a: _) (b: _) (__γclos: gname), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (True))%I) : ((FnOnce_Pre_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_ret: _), (∃ (a: _) (b: _) (__γclos: gname), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) a b))%Z⌝))
      ∗ (True))%I) : ((FnOnce_Post_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (a: _) (b: _) (__γclos: gname), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) a b))%Z⌝)
      ∗ (⌜(_self_post = (tt))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (_) (_) (_)));
  |}
.


Program Definition traits_iterator_Iterator_max_closure0_FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : ((FnMut_spec_attrs (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
  mk_FnMut_spec_attrs.


Program Definition traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : ((FnOnce_spec_attrs ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
  {|
    FnOnce_Params  :=
      ((plist id [_ : Type])) : ((FnOnce_Params_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _), (∃ (pclos: _) (a: _) (b: _) (_γcompare: gname) (__γclos: gname) (capture_compare_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_compare_), _γcompare))]))%Z⌝)
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_compare_ *[b; a])
      ∗ (True))%I) : ((FnOnce_Pre_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_ret: _), (∃ (pclos: _) (a: _) (b: _) (_γcompare: gname) (__γclos: gname) (capture_compare_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_compare_), _γcompare))]))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (∃ (ord: _) (capture_compare__new: (RT_xt ((F_rt)))), (⌜(_ret = (if bool_decide(ord = Less) then a else b))%Z⌝)
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_compare_ *[b; a] capture_compare__new ord)
      ∗ (gvar_pobs _γcompare ($#@{(F_rt)} capture_compare__new)))
      ∗ (True))%I) : ((FnOnce_Post_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (pclos: _) (a: _) (b: _) (_γcompare: gname) (__γclos: gname) (capture_compare_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_compare_), _γcompare))]))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (∃ (ord: _) (capture_compare__new: (RT_xt ((F_rt)))), (⌜(_ret = (if bool_decide(ord = Less) then a else b))%Z⌝)
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_compare_ *[b; a] capture_compare__new ord)
      ∗ (⌜(_self_post = ( *[((capture_compare__new), _γcompare)]))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (_) (_) (_)));
  |}
.


Program Definition traits_iterator_Iterator_max_by_closure0_FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : ((FnMut_spec_attrs ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
  mk_FnMut_spec_attrs.


Program Definition traits_iterator_Iterator_min_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : ((FnOnce_spec_attrs (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
  {|
    FnOnce_Params  :=
      ((plist id [])) : ((FnOnce_Params_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt))))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _), (∃ (a: _) (b: _) (__γclos: gname), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (True))%I) : ((FnOnce_Pre_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_ret: _), (∃ (a: _) (b: _) (__γclos: gname), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) a b))%Z⌝))
      ∗ (True))%I) : ((FnOnce_Post_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (a: _) (b: _) (__γclos: gname), (⌜(_params = *[  ])%Z⌝)
      ∗ (⌜(_self = (tt))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ ((⌜(_ret = (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) a b))%Z⌝)
      ∗ (⌜(_self_post = (tt))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (_) (_) (_)));
  |}
.


Program Definition traits_iterator_Iterator_min_closure0_FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : ((FnMut_spec_attrs (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
  mk_FnMut_spec_attrs.


Program Definition traits_iterator_Iterator_min_by_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : ((FnOnce_spec_attrs ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
  {|
    FnOnce_Params  :=
      ((plist id [_ : Type])) : ((FnOnce_Params_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _), (∃ (pclos: _) (a: _) (b: _) (_γcompare: gname) (__γclos: gname) (capture_compare_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_compare_), _γcompare))]))%Z⌝)
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_compare_ *[b; a])
      ∗ (True))%I) : ((FnOnce_Pre_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_ret: _), (∃ (pclos: _) (a: _) (b: _) (_γcompare: gname) (__γclos: gname) (capture_compare_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_compare_), _γcompare))]))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (∃ (ord: _) (capture_compare__new: (RT_xt ((F_rt)))), (⌜(_ret = (if bool_decide(ord = Less) then b else a))%Z⌝)
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_compare_ *[b; a] capture_compare__new ord)
      ∗ (gvar_pobs _γcompare ($#@{(F_rt)} capture_compare__new)))
      ∗ (True))%I) : ((FnOnce_Post_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (pclos: _) (a: _) (b: _) (_γcompare: gname) (__γclos: gname) (capture_compare_: (RT_xt ((F_rt)))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_compare_), _γcompare))]))%Z⌝)
      ∗ (⌜(_args = *[ a; b ])%Z⌝)
      ∗ (∃ (ord: _) (capture_compare__new: (RT_xt ((F_rt)))), (⌜(_ret = (if bool_decide(ord = Less) then b else a))%Z⌝)
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_compare_ *[b; a] capture_compare__new ord)
      ∗ (⌜(_self_post = ( *[((capture_compare__new), _γcompare)]))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (_) (_) (_)));
  |}
.


Program Definition traits_iterator_Iterator_min_by_closure0_FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : ((FnMut_spec_attrs ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
  mk_FnMut_spec_attrs.


Program Definition traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : ((FnOnce_spec_attrs ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))))) :=
  {|
    FnOnce_Params  :=
      ((plist id [_ : Type])) : ((FnOnce_Params_sig ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit))))));
    FnOnce_Pre  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _), (∃ (pclos: _) (_arg_0: _) (x: _) (_γf: gname) (_γacc: gname) (__γclos: gname) (capture_f_: (RT_xt ((F_rt)))) (capture_acc_: (RT_xt (Z))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_args = *[ _arg_0; x ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_f_), _γf)); (((capture_acc_), _γacc))]))%Z⌝)
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_f_ *[x])
      ∗ (True))%I) : ((FnOnce_Pre_sig ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))) (_)));
    FnOnce_Post  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_ret: _), (∃ (pclos: _) (_arg_0: _) (x: _) (_γf: gname) (_γacc: gname) (__γclos: gname) (capture_f_: (RT_xt ((F_rt)))) (capture_acc_: (RT_xt (Z))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_f_), _γf)); (((capture_acc_), _γacc))]))%Z⌝)
      ∗ (⌜(_args = *[ _arg_0; x ])%Z⌝)
      ∗ (∃ (res: _) (ret: _) (capture_f__new: (RT_xt ((F_rt)))) (capture_acc__new: (RT_xt (Z))), (⌜(_ret = (ret))%Z⌝)
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_f_ *[x] capture_f__new res)
      ∗ (⌜(if_Ok ret (λ ret, res = false ∧ capture_acc__new = 1+capture_acc_))%Z⌝)
      ∗ (⌜(if_Err ret (λ ret, res = true ∧ ret = capture_acc_ ∧ capture_acc__new = capture_acc_))%Z⌝)
      ∗ (gvar_pobs _γf ($#@{(F_rt)} capture_f__new))
      ∗ (gvar_pobs _γacc ($#@{Z} capture_acc__new)))
      ∗ (True))%I) : ((FnOnce_Post_sig ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))) (_) (_)));
    FnOnce_PostMut  :=
      (λ (π: thread_id) (_params: (plist id [_ : Type])) (_self: _) (_args: _) (_self_post: _) (_ret: _), (∃ (pclos: _) (_arg_0: _) (x: _) (_γf: gname) (_γacc: gname) (__γclos: gname) (capture_f_: (RT_xt ((F_rt)))) (capture_acc_: (RT_xt (Z))), (⌜(_params = *[ pclos ])%Z⌝)
      ∗ (⌜(_self = ( *[(((capture_f_), _γf)); (((capture_acc_), _γacc))]))%Z⌝)
      ∗ (⌜(_args = *[ _arg_0; x ])%Z⌝)
      ∗ (∃ (res: _) (ret: _) (capture_f__new: (RT_xt ((F_rt)))) (capture_acc__new: (RT_xt (Z))), (⌜(_ret = (ret))%Z⌝)
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_f_ *[x] capture_f__new res)
      ∗ (⌜(if_Ok ret (λ ret, res = false ∧ capture_acc__new = 1+capture_acc_))%Z⌝)
      ∗ (⌜(if_Err ret (λ ret, res = true ∧ ret = capture_acc_ ∧ capture_acc__new = capture_acc_))%Z⌝)
      ∗ (⌜(_self_post = ( *[((capture_f__new), _γf); ((capture_acc__new), _γacc)]))%Z⌝))
      ∗ (True))%I) : ((FnOnce_PostMut_sig ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))) (_) (_) (_)));
  |}
.


Program Definition traits_iterator_Iterator_position_closure0_FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : ((FnMut_spec_attrs ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))))) :=
  mk_FnMut_spec_attrs.


End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra.
  Context `{RRGS : !refinedrustGS Σ}.
  (** Map *)
  Lemma iterator_next_fused_trans_map_inv {MB_rt MI_rt MF_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  (FnOnce_attrs : FnOnce_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  (FnMut_attrs : FnMut_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt) π p ParamPred s1 hist s2 :
    IteratorNextFusedTrans (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs MB_rt MI_rt MF_rt Item_rt It_attrs FnOnce_attrs FnMut_attrs) π (p, ParamPred) s1 hist s2 -∗
    ∃ hist' states,
      ⌜states !! 0%nat = Some s1.(map_clos)⌝ ∗
      ⌜states !! (length hist) = Some s2.(map_clos)⌝ ∗
      ⌜length states = S (length hist)⌝ ∗
      IteratorNextFusedTrans It_attrs π p s1.(map_it) hist' s2.(map_it) ∗
      [∗ list] i ↦ a; b ∈ hist'; hist,
        ∃ s1 s2 p_clos, ⌜states !! i = Some s1⌝ ∗ ⌜states !! S i = Some s2⌝ ∗ ⌜ParamPred *[a] p_clos⌝ ∗ ☒ FnOnce_attrs.(FnOnce_Pre) π p_clos s1 *[a] ∗ FnOnce_attrs.(FnOnce_PostMut) π p_clos s1 *[a] s2 b
  .
  Proof.
    iInduction hist as [ | a hist] "IH" forall (s1 s2); simpl.
    { iIntros "<-". iExists [], [s1.(map_clos)]. simpl. done. }
    iIntros "(%s1' & (_ & %b & Ha & %pclos & Hpre & Hpost) & Hc)".
    iPoseProof ("IH" with "Hc") as "(%hist' & %states & % & % & %Hlen & Hit & Hclos)".
    iExists (b :: hist'), (s1.(map_clos) :: states).
    iR.
    iSplitR. { iPureIntro. simpl. done. }
    iSplitR. { iPureIntro. simpl. rewrite Hlen. done. }
    simpl. iFrame "Hclos".
    iFrame. done.
  Qed.

  (** Declared as an extern instance below, to enforce order on the argument resolution *)
  Program Definition iterator_learn_map_stateful {MB_rt MI_rt MF_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  (FnOnce_attrs : FnOnce_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  (FnMut_attrs : FnMut_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  p ParamPred
  (It_learn : IteratorLearnInductive It_attrs p)
  (FnOnce_pre_learn : ∀ π p self args, SimplifyBoringlyImpl (FnOnce_attrs.(FnOnce_Pre) π p self args))
  (FnMut_postmut_learn : ∀ π p self args self' out, SimplifyBoringlyImpl (FnOnce_attrs.(FnOnce_PostMut) π p self args self' out))
  :
    IteratorLearnInductive (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs MB_rt MI_rt MF_rt Item_rt It_attrs FnOnce_attrs FnMut_attrs) (p, ParamPred) := {|
      iterator_learn_inductive_Q s1 hist s2 :=
        ∃ π hist' clos_states,
          It_learn.(iterator_learn_inductive_Q) s1.(map_it) hist' s2.(map_it) ∧
          length clos_states = (1 + length hist')%nat ∧
          head clos_states = Some(s1.(map_clos)) ∧
          last clos_states = Some(s2.(map_clos)) ∧
          Forall2 (λ p b,
          (∃ pclos, ∃ clos1 clos2, clos_states !! p.1 = Some clos1 ∧ clos_states !! (S p.1) = Some clos2 ∧ ParamPred *[p.2] pclos ∧ (FnOnce_pre_learn π pclos clos1 *[p.2]).(simplify_boringly_impl_q _) ∧ (FnMut_postmut_learn π pclos clos1 *[p.2] clos2 b).(simplify_boringly_impl_q _))
          ) (zip (seq 0 (length hist')) hist') hist
    |}.
  Next Obligation.
    intros ???? It_attrs FnOnce_attrs FnMut_attrs p ParamPred It_learn FnOnce_pure FnMut_pure.
    simpl. iIntros (? s1 hist s2) "Hnext".
    iPoseProof (boringly_mono with "Hnext") as "Ha".
    { iApply iterator_next_fused_trans_map_inv. }
    repeat setoid_rewrite boringly_exists.
    iDestruct "Ha" as "(%hist' & %states' & Ha)".
    rewrite !boringly_sep !boringly_persistent_elim.
    iDestruct "Ha" as "(%Hlook1 & %Hlook2 & %Hlen & Hnext & Hclos)".
    iPoseProof (It_learn.(iterator_learn_inductive_proof) with "Hnext") as "%Hlearn".

    iAssert (([∗ list] i↦a;b ∈ hist';hist, ⌜∃ pclos (s0 s3 : RT_xt MF_rt), states' !! i = Some s0 ∧ states' !! S i = Some s3 ∧ ParamPred *[a] pclos ∧ simplify_boringly_impl_q (FnOnce_Pre FnOnce_attrs π pclos s0 *[a]) ∧
      simplify_boringly_impl_q (FnOnce_PostMut FnOnce_attrs π pclos s0 *[a] s3 b)⌝)%I) with "[Hclos]" as "Hclos".
    { iApply boringly_persistent_elim.
      iApply boringly_mono; last iApply "Hclos".
      iIntros "Ha". iApply (big_sepL2_impl with "Ha").
      iModIntro. iIntros (?????) "(% & % & % & % & % & %Hpred & Hpre & Hpost)".
      iPoseProof (boringly_intro with "Hpost") as "Hpost".
      rewrite ((FnMut_pure _ _ _ _ _ _).(simplify_boringly_impl_proof)).
      rewrite ((FnOnce_pure _ _ _ _).(simplify_boringly_impl_proof)).
      iDestruct "Hpre" as "%Hpre".
      iDestruct "Hpost" as "%Hpost".
      iPureIntro.
      eexists _, _, _. split_and!; done. }
    iPoseProof (big_sepL2_Forall3 with "Hclos") as "%Hf".
    opose proof* Forall3_length_lr as Hlen1; first done.
    opose proof* Forall3_length_lm as Hlen2; first done.

    iPureIntro.
    exists π, hist', states'.
    split; first done.
    simpl in *.
    split. { rewrite Hlen. lia. }
    split. { rewrite head_lookup. done. }
    split. { rewrite last_lookup. rewrite Hlen. done. }
    replace (length hist) with (length hist') by lia.
    eapply (Forall2_impl (λ '(a, b) c, _ )).
    { eapply Forall3_to_Forall2_l.
      eapply Forall3_impl; first apply Hf.
      done. }
    intros []. done.
  Qed.

  (** Declared as an extern instance below, to enforce order on the argument resolution *)
  Program Definition iterator_learn_map_stateless {MB_rt MI_rt MF_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  (FnOnce_attrs : FnOnce_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  (FnMut_attrs : FnMut_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  p ParamPred
  (It_learn : IteratorLearnInductive It_attrs p)
  (FnOnce_pre_learn : ∀ π p self args, SimplifyBoringlyImpl (FnOnce_attrs.(FnOnce_Pre) π p self args))
  (FnMut_postmut_learn : ∀ π p self args self' out, SimplifyBoringlyImpl (FnOnce_attrs.(FnOnce_PostMut) π p self args self' out))
  (FnMut_postmut_stateless : ∀ π p args out, RelationIsIdentity (λ self self', (FnMut_postmut_learn π p self args self' out).(simplify_boringly_impl_q _)))
  :
    IteratorLearnInductive (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs MB_rt MI_rt MF_rt Item_rt It_attrs FnOnce_attrs FnMut_attrs) (p, ParamPred) := {|
      iterator_learn_inductive_Q s1 hist s2 :=
        ∃ π hist',
          It_learn.(iterator_learn_inductive_Q) s1.(map_it) hist' s2.(map_it) ∧
          s1.(map_clos) = s2.(map_clos) ∧
          Forall2 (λ a b, (∃ pclos, ParamPred *[a] pclos ∧ (FnOnce_pre_learn π pclos s1.(map_clos) *[a]).(simplify_boringly_impl_q _) ∧ (FnMut_postmut_learn π pclos s1.(map_clos) *[a] s1.(map_clos) b).(simplify_boringly_impl_q _))) hist' hist
        ;
    |}.
  Next Obligation.
    intros ???? It_attrs FnOnce_attrs FnMut_attrs p ParamPred It_learn FnOnce_pure FnMut_pure FnMut_stateless.
    simpl. iIntros (? s1 hist s2) "Hnext".
    iPoseProof (boringly_mono with "Hnext") as "Ha".
    { iApply iterator_next_fused_trans_map_inv. }
    repeat setoid_rewrite boringly_exists.
    iDestruct "Ha" as "(%hist' & %states' & Ha)".
    rewrite !boringly_sep !boringly_persistent_elim.
    iDestruct "Ha" as "(%Hlook1 & %Hlook2 & %Hlen & Hnext & Hclos)".
    iPoseProof (It_learn.(iterator_learn_inductive_proof) with "Hnext") as "%Hlearn".

    iAssert (([∗ list] i↦a;b ∈ hist';hist, ∃ (s0 s3 : RT_xt MF_rt) pclos, ⌜ParamPred *[a] pclos⌝ ∗ ⌜states' !! i = Some s0⌝ ∗ ⌜states' !! S i = Some s3⌝ ∗ ☒ FnOnce_Pre FnOnce_attrs π pclos s0 *[a] ∗ ☒ FnOnce_PostMut FnOnce_attrs π pclos s0 *[a] s3 b))%I with "[Hclos]" as "Hclos".
    { iApply boringly_persistent_elim.
      iApply boringly_mono; last iApply "Hclos".
      iIntros "Ha". iApply (big_sepL2_impl with "Ha").
      iModIntro. iIntros (?????) "(% & % & % & % & % & % & Hpre & Hpost)".
      iFrame "∗%". by iApply boringly_intro. }

    iAssert (⌜∀ i x y, states' !! i = Some x → states' !! (S i) = Some y → x = y⌝)%I as "%Hstates".
    { iIntros (i ? ? Hlook3 Hlook4). iClear "Hnext".
      assert (i < length hist). { apply lookup_lt_Some in Hlook4. lia. }

      iPoseProof (big_sepL2_length with "Hclos") as "%Hlen'".
      odestruct (lookup_lt_is_Some_2 hist i _) as (sb & ?); first lia.
      odestruct (lookup_lt_is_Some_2 hist' i _) as (sa & ?). { rewrite Hlen'. lia. }

      iPoseProof (big_sepL2_lookup _ _ _ i sa sb with "Hclos") as "Ha"; [done.. | ].
      iDestruct "Ha" as "(% & % & % & % & % & % & Hpre & Hpost)".

      rewrite ((FnMut_pure π _ _ _ _ _).(simplify_boringly_impl_proof)).
      iDestruct "Hpost" as "%Hpost".
      apply FnMut_stateless in Hpost.
      simplify_eq. done. }
    (* prove that the state remains constant *)
    assert (∀ j i s, (i < j)%nat → states' !! i = Some s → s = s1.(map_clos)) as Hstates'.
    { clear -Hstates Hlook1.
      induction j as [ | j IH]; simpl in *. { intros. lia. }
      intros i s Hlt Hlook.
      apply lookup_lt_Some in Hlook as ?.
      destruct (decide (i = j)) as [-> | ?].
      - destruct j as [ | j]; first by simplify_eq.
        odestruct (lookup_lt_is_Some_2 states' j _) as (? & Hlook2); first lia.
        ospecialize (IH j _ _ _); [lia | done | ].
        subst. symmetry. by eapply (Hstates j).
      - eapply IH; last done. lia. }

    iExists π, hist'.
    iSplitR; first done.
    iSplitR. { iPureIntro. symmetry. eapply (Hstates' (S (length hist))); last done. lia. }
    iApply big_sepL2_Forall2.
    iApply (big_sepL2_impl with "Hclos").
    iModIntro. iIntros (? ?? Hlook3 Hlook4) "(%sa & %sb & %pclos & % & %Hlook5 & %Hlook6 & Hpre & Hpost)".
    rewrite ((FnMut_pure _ _ _ _ _ _).(simplify_boringly_impl_proof)).
    rewrite ((FnOnce_pure _ _ _ _).(simplify_boringly_impl_proof)).
    iDestruct "Hpre" as "%".
    iDestruct "Hpost" as "%".
    opose proof (Hstates' (S k) k _ _ Hlook5); first lia.
    opose proof (Hstates' (S (S k)) (S k) _ _ Hlook6); first lia.
    subst. iPureIntro.
    eexists _. done.
  Qed.

  (** Take *)
  Lemma iterator_next_fused_trans_take_inv {MI_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt) π p s1 hist s2 :
    IteratorNextFusedTrans (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs MI_rt Item_rt It_attrs) π p s1 hist s2 -∗
      IteratorNextFusedTrans It_attrs π p s1.1 hist s2.1 ∗
      ⌜length hist ≤ s1.2⌝ ∗ ⌜s2.2 = (s1.2 - length hist)%nat⌝
  .
  Proof.
    iInduction hist as [ | a hist] "IH" forall (s1 s2); simpl.
    { iIntros "<-". iPureIntro. split_and!; try done; try lia. }
    iIntros "(%s1' & (_ & %Hgt & %Heq & Hnext) & Hc)".
    iPoseProof ("IH" with "Hc") as "(Hit & % & %)".
    iFrame. iPureIntro.
    split; lia.
  Qed.

  Program Definition iterator_learn_take {MI_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  p
  (It_learn : IteratorLearnInductive It_attrs p)
  :
    IteratorLearnInductive (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs MI_rt Item_rt It_attrs) p := {|
      iterator_learn_inductive_Q s1 hist s2 :=
          It_learn.(iterator_learn_inductive_Q) s1.1 hist s2.1 ∧
          length hist ≤ s1.2 ∧
          s2.2 = (s1.2 - length hist)%nat
        ;
    |}.
  Next Obligation.
    iIntros (??? p It_learn π s1 hist s2).
    iIntros "Hit".
    iPoseProof (boringly_mono with "Hit") as "Ha".
    { iApply iterator_next_fused_trans_take_inv. }
    rewrite !boringly_sep. rewrite !boringly_persistent_elim.
    iDestruct "Ha" as "(Hnext & % & %)".
    iPoseProof (It_learn.(iterator_learn_inductive_proof) with "Hnext") as "%Hlearn".
    iPureIntro. done.
  Qed.
  Global Existing Instance iterator_learn_take.


  (** Skip *)
  Lemma iterator_next_fused_trans_skip_inv {MI_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt) π p s1 hist s2 :
    IteratorNextFusedTrans (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs MI_rt Item_rt It_attrs) π p s1 hist s2 -∗
      ∃ pref,
        IteratorNextFusedTrans It_attrs π p s1.1 (pref ++ hist) s2.1 ∗
        ⌜length pref ≤ s1.2⌝ ∗
        ⌜s2.2 = (s1.2 - length pref)%nat⌝ ∗
        (* TODO can I find a better formulation for this? *)
        ⌜if decide (length hist = 0%nat) then pref = [] else length pref = s1.2⌝
  .
  Proof.
    iInduction hist as [ | a hist] "IH" forall (s1 s2); simpl.
    { iIntros "<-". iExists [].
      simpl. iR. iPureIntro. split_and!; try done; try lia. }
    iIntros "(%s1' & (_ & Hnext) & Hc)".
    iDestruct "Hnext" as "(%seq & %s2_inner & %Hseq_len & %Hn' & Hnexts & Hnext)".
    iPoseProof ("IH" with "Hc") as "(%prefix & Hnext' & % & % & %Hdec)".
    destruct (decide (seq = [])) as [Hseq_zero | Hseq_nzero].
    + subst. simpl in *. iDestruct "Hnexts" as "<-".
      iExists []. simpl.
      assert (prefix = []) as ->. { destruct prefix; simpl in *; first done. lia. }
      simpl. iFrame. iPureIntro. split_and; solve_goal.
    + iExists seq. assert (prefix = []) as ->. { destruct prefix; simpl in *; solve_goal. }
      simpl. iSplitL.
      { iApply iterator_next_fused_trans_app. iFrame. }
      iPureIntro. solve_goal.
  Qed.

  Program Definition iterator_learn_skip {MI_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  p
  (It_learn : IteratorLearnInductive It_attrs p)
  :
    IteratorLearnInductive (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs MI_rt Item_rt It_attrs) p := {|
      iterator_learn_inductive_Q s1 hist s2 :=
          ∃ pref,
          It_learn.(iterator_learn_inductive_Q) s1.1 (pref ++ hist) s2.1 ∧
          length pref ≤ s1.2 ∧
          s2.2 = (s1.2 - length pref)%nat ∧
          (* TODO can I find a better formulation for this? *)
          if decide (length hist = 0%nat) then pref = [] else length pref = s1.2
        ;
    |}.
  Next Obligation.
    iIntros (??? p It_learn π s1 hist s2).
    iIntros "Hit".
    iPoseProof (boringly_mono with "Hit") as "Ha".
    { iApply iterator_next_fused_trans_skip_inv. }
    rewrite boringly_exists.
    iDestruct "Ha" as "(%prefix & Ha)".
    rewrite !boringly_sep. rewrite !boringly_persistent_elim.
    iDestruct "Ha" as "(Hnext & % & % & %)".
    iPoseProof (It_learn.(iterator_learn_inductive_proof) with "Hnext") as "%Hlearn".
    iPureIntro. exists prefix. done.
  Qed.
  Global Existing Instance iterator_learn_skip.

  (** Range *)
  Program Definition iterator_learn_range_it
    (Clone_attrs : Clone_spec_attrs Z)
    (PartialEq_attrs : PartialEq_spec_attrs Z Z)
    (PartialOrd_attrs : PartialOrd_spec_attrs Z Z PartialEq_attrs)
    (Step_attrs : step_Step_spec_attrs Z Clone_attrs PartialEq_attrs PartialOrd_attrs)
    :
    (∀ a b z, Step_attrs.(step_Step_Forward) a b = Some z → z = a + b) →
    (∀ a b, PartialOrd_attrs.(PartialOrd_POrd) a b = Some (Z.compare a b)) →
    ∀ p, IteratorLearnInductive (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (Z)
      Clone_attrs PartialEq_attrs PartialOrd_attrs Step_attrs) p :=
    λ _ _ _, {| iterator_learn_inductive_Q s1 hist s2 :=
        s1.2 = s2.2 ∧ s1.1 ≤ s2.1 ∧ hist = seqZ s1.1 (s2.1 - s1.1) |}.
  Next Obligation.
    iIntros (???? Hstep Hcmp_eq [] ????) "Hx".
    iPoseProof (boringly_persistent_elim with "Hx") as "Hx".
    iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
    { iDestruct "Hx" as "%". subst. iPureIntro.
      rewrite Z.sub_diag. done. }
    iDestruct "Hx" as "(%s1' & %Ha & Hx)".
    iPoseProof ("IH" with "Hx") as "%Hb".
    iPureIntro.
    destruct Ha as (? & _ & <- & Hstep_some & Hcmp). destruct Hb as (? & ? & ->).
    destruct s1, s2, s1'; simpl in *.
    subst.
    symmetry in Hstep_some. apply Hstep in Hstep_some.
    subst z.
    rewrite Hcmp_eq in Hcmp.
    injection Hcmp.
    rewrite Z.compare_lt_iff. intros.
    split_and!; try solve_goal.
    rewrite (seqZ_cons r (r1 - r)); last lia.
    f_equiv. f_equiv; lia.
  Qed.


  Program Definition iterator_learn_range_it_i8 :=
    iterator_learn_range_it (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (i8asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i8.

  Program Definition iterator_learn_range_it_i16 :=
    iterator_learn_range_it (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (i16asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i16.

  Program Definition iterator_learn_range_it_i32 :=
    iterator_learn_range_it (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (i32asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i32.

  Program Definition iterator_learn_range_it_i64 :=
    iterator_learn_range_it (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (i64asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i64.

  Program Definition iterator_learn_range_it_i128 :=
    iterator_learn_range_it (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (i128asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i128.

  Program Definition iterator_learn_range_it_isize :=
    iterator_learn_range_it (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (isizeasstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_isize.

  Program Definition iterator_learn_range_it_u8 :=
    iterator_learn_range_it (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (u8asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u8.

  Program Definition iterator_learn_range_it_u16 :=
    iterator_learn_range_it (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (u16asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u16.

  Program Definition iterator_learn_range_it_u32 :=
    iterator_learn_range_it (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (u32asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u32.

  Program Definition iterator_learn_range_it_u64 :=
    iterator_learn_range_it (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (u64asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u64.

  Program Definition iterator_learn_range_it_u128 :=
    iterator_learn_range_it (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (u128asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u128.

  Program Definition iterator_learn_range_it_usize :=
    iterator_learn_range_it (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (usizeasstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_usize.

  Lemma simplify_goal_range_iter_inv Clone_attrs PEq_attrs POrd_attrs Step_attrs π p b T :
    T
    ⊢ simplify_goal (traits_iterator_Iterator_Inv (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs Z Clone_attrs PEq_attrs POrd_attrs Step_attrs) π p b) T.
  Proof.
    unfold traits_iterator_Iterator_Inv; simpl.
    iIntros "$".
  Qed.
  Definition simplify_goal_range_iter_inv_inst := [instance @simplify_goal_range_iter_inv with 0%N].
  Global Existing Instance simplify_goal_range_iter_inv_inst.

  (** A trivial learning instance so we can bottom out of iterator combinator learning even if we don't know the concrete shape of the iterator *)
  Global Program Instance iterator_learn_trivial {Self_rt Item_rt} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) p :
    IteratorLearnInductive A p | 1000 :=
    {| iterator_learn_inductive_Q s1 hist s2 := True; |}.
  Next Obligation.
    iIntros (????????) "_". done.
  Qed.
End extra.
Global Hint Extern 100 (IteratorLearnInductive (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs _ _ _ _ _ _ _) _ ) =>
  unshelve notypeclasses refine (iterator_learn_map_stateless _ _ _ _ _ _ _ _ _); [ tc_solve | tc_solve | tc_solve | tc_solve] : typeclass_instances.
Global Hint Extern 101 (IteratorLearnInductive (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs _ _ _ _ _ _ _) _) =>
  unshelve notypeclasses refine (iterator_learn_map_stateful _ _ _ _ _ _ _ _); [ tc_solve | tc_solve | tc_solve] : typeclass_instances.
Record traits_iterator_FromIterator_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{A_rt : !RT} : Type := mk_traits_iterator_FromIterator_spec {
  traits_iterator_FromIterator_from_iter_spec (T_rt: RT) (traits_iterator_IntoIterator_T_IntoIter_rt: RT) (T_st: syn_type) (traits_iterator_IntoIterator_T_IntoIter_st: syn_type) (traits_iterator_IntoIterator_T_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt) )) : (spec_with 0 [T_rt; traits_iterator_IntoIterator_T_IntoIter_rt] fn_spec);
}.
#[global] Arguments traits_iterator_FromIterator_spec : clear implicits.

#[global] Arguments traits_iterator_FromIterator_spec {_ _}.


Record traits_iterator_IntoIterator_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{IntoIter_rt : !RT} `{Item_rt : !RT} : Type := mk_traits_iterator_IntoIterator_spec {
  traits_iterator_IntoIterator_into_iter_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments traits_iterator_IntoIterator_spec : clear implicits.

#[global] Arguments traits_iterator_IntoIterator_spec {_ _}.


Record traits_iterator_Iterator_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Item_rt : !RT} : Type := mk_traits_iterator_Iterator_spec {
  traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) : (spec_with 1 [F_rt] fn_spec);
  traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) : (spec_with 0 [B_rt] fn_spec);
  traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) : (spec_with 0 [B_rt; F_rt] fn_spec);
  traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) : (spec_with 0 [B_rt; F_rt] fn_spec);
  traits_iterator_Iterator_max_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : (spec_with 0 [] fn_spec);
  traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) : (spec_with 0 [F_rt] fn_spec);
  traits_iterator_Iterator_min_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : (spec_with 0 [] fn_spec);
  traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) : (spec_with 0 [F_rt] fn_spec);
  traits_iterator_Iterator_next_spec  : (spec_with 1 [] fn_spec);
  traits_iterator_Iterator_nth_spec  : (spec_with 1 [] fn_spec);
  traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) : (spec_with 1 [F_rt] fn_spec);
  traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) : (spec_with 0 [F_rt] fn_spec);
  traits_iterator_Iterator_skip_spec  : (spec_with 0 [] fn_spec);
  traits_iterator_Iterator_take_spec  : (spec_with 0 [] fn_spec);
  traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
}.
#[global] Arguments traits_iterator_Iterator_spec : clear implicits.

#[global] Arguments traits_iterator_Iterator_spec {_ _}.


Record step_Step_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_step_Step_spec {
  step_Step_backward_spec  : (spec_with 0 [] fn_spec);
  step_Step_backward_checked_spec  : (spec_with 0 [] fn_spec);
  step_Step_backward_unchecked_spec  : (spec_with 0 [] fn_spec);
  step_Step_forward_spec  : (spec_with 0 [] fn_spec);
  step_Step_forward_checked_spec  : (spec_with 0 [] fn_spec);
  step_Step_forward_unchecked_spec  : (spec_with 0 [] fn_spec);
  step_Step_steps_between_spec  : (spec_with 2 [] fn_spec);
}.
#[global] Arguments step_Step_spec : clear implicits.

#[global] Arguments step_Step_spec {_ _}.


Record step_TrustedStep_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_step_TrustedStep_spec {
}.
#[global] Arguments step_TrustedStep_spec : clear implicits.

#[global] Arguments step_TrustedStep_spec {_ _}.


Section traits_iterator_FromIterator.
Context `{RRGS : !refinedrustGS Σ}.
Definition traits_iterator_FromIterator_spec_incl `{Self_rt : !RT} `{A_rt : !RT} (spec1: ((traits_iterator_FromIterator_spec (Self_rt) (A_rt)))) (spec2: ((traits_iterator_FromIterator_spec (Self_rt) (A_rt)))) : Prop :=
  (∀ (T_rt: RT) (traits_iterator_IntoIterator_T_IntoIter_rt: RT) (T_st: syn_type) (traits_iterator_IntoIterator_T_IntoIter_st: syn_type) (traits_iterator_IntoIterator_T_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt) )), (function_subtype ((spec1.(traits_iterator_FromIterator_from_iter_spec) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (T_st) (traits_iterator_IntoIterator_T_IntoIter_st) (traits_iterator_IntoIterator_T_spec_attrs))) ((spec2.(traits_iterator_FromIterator_from_iter_spec) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (T_st) (traits_iterator_IntoIterator_T_IntoIter_st) (traits_iterator_IntoIterator_T_spec_attrs))))).
Instance traits_iterator_FromIterator_spec_incl_preorder `{Self_rt : !RT} `{A_rt : !RT} : (PreOrder (traits_iterator_FromIterator_spec_incl (Self_rt := Self_rt) (A_rt := A_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition traits_iterator_FromIterator_from_iter_base_spec (Self_rt: RT) (A_rt: RT) (T_rt: RT) (traits_iterator_IntoIterator_T_IntoIter_rt: RT) (Self_st: syn_type) (A_st: syn_type) (T_st: syn_type) (traits_iterator_IntoIterator_T_IntoIter_st: syn_type) (traits_iterator_FromIterator_Self_A_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (Self_rt) (A_rt) )) (traits_iterator_IntoIterator_T_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; A_ty; T_ty; traits_iterator_IntoIterator_T_IntoIter_ty]) : ([(Self_rt, Self_st); (A_rt, A_st); (T_rt, T_st); (traits_iterator_IntoIterator_T_IntoIter_rt, traits_iterator_IntoIterator_T_IntoIter_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (iter) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) iter :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ Self_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition traits_iterator_FromIterator_base_spec (Self_rt: RT) (A_rt: RT) (Self_st: syn_type) (A_st: syn_type) (_ATTRS: ((traits_iterator_FromIterator_spec_attrs ((Self_rt)) ((A_rt))))) : (spec_with _ _ (traits_iterator_FromIterator_spec ((Self_rt)) ((A_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; A_ty]) : ([Self_rt; A_rt] : list RT), {|
      traits_iterator_FromIterator_from_iter_spec (T_rt: RT) (traits_iterator_IntoIterator_T_IntoIter_rt: RT) (T_st: syn_type) (traits_iterator_IntoIterator_T_IntoIter_st: syn_type) (traits_iterator_IntoIterator_T_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt) )) :=
        (traits_iterator_FromIterator_from_iter_base_spec ((Self_rt)) ((A_rt)) ((T_rt)) ((traits_iterator_IntoIterator_T_IntoIter_rt)) (Self_st) (A_st) (T_st) (traits_iterator_IntoIterator_T_IntoIter_st)) _ATTRS traits_iterator_IntoIterator_T_spec_attrs
           <TY> Self_ty <TY> A_ty : (spec_with 0 [T_rt; traits_iterator_IntoIterator_T_IntoIter_rt] fn_spec);
    |}
.

End traits_iterator_FromIterator.

Section traits_iterator_IntoIterator.
Context `{RRGS : !refinedrustGS Σ}.
Definition traits_iterator_IntoIterator_spec_incl `{Self_rt : !RT} `{IntoIter_rt : !RT} `{Item_rt : !RT} (spec1: ((traits_iterator_IntoIterator_spec (Self_rt) (IntoIter_rt) (Item_rt)))) (spec2: ((traits_iterator_IntoIterator_spec (Self_rt) (IntoIter_rt) (Item_rt)))) : Prop :=
  ((function_subtype (spec1.(traits_iterator_IntoIterator_into_iter_spec)) (spec2.(traits_iterator_IntoIterator_into_iter_spec)))).
Instance traits_iterator_IntoIterator_spec_incl_preorder `{Self_rt : !RT} `{IntoIter_rt : !RT} `{Item_rt : !RT} : (PreOrder (traits_iterator_IntoIterator_spec_incl (Self_rt := Self_rt) (IntoIter_rt := IntoIter_rt) (Item_rt := Item_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition traits_iterator_IntoIterator_into_iter_base_spec (Self_rt: RT) (IntoIter_rt: RT) (Item_rt: RT) (Self_st: syn_type) (IntoIter_st: syn_type) (Item_st: syn_type) (traits_iterator_IntoIterator_Self_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (Self_rt) (IntoIter_rt) (Item_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; IntoIter_ty; Item_ty]) : ([(Self_rt, Self_st); (IntoIter_rt, IntoIter_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, traits_iterator_IntoIterator_Self_spec_attrs.(traits_iterator_IntoIterator_IntoIter) self @ IntoIter_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition traits_iterator_IntoIterator_base_spec (Self_rt: RT) (IntoIter_rt: RT) (Item_rt: RT) (Self_st: syn_type) (IntoIter_st: syn_type) (Item_st: syn_type) (_ATTRS: ((traits_iterator_IntoIterator_spec_attrs ((Self_rt)) ((IntoIter_rt)) ((Item_rt))))) : (spec_with _ _ (traits_iterator_IntoIterator_spec ((Self_rt)) ((IntoIter_rt)) ((Item_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; IntoIter_ty; Item_ty]) : ([Self_rt; IntoIter_rt; Item_rt] : list RT), {|
      traits_iterator_IntoIterator_into_iter_spec  :=
        (traits_iterator_IntoIterator_into_iter_base_spec ((Self_rt)) ((IntoIter_rt)) ((Item_rt)) (Self_st) (IntoIter_st) (Item_st)) _ATTRS 
           <TY> Self_ty <TY> IntoIter_ty <TY> Item_ty : (spec_with 0 [] fn_spec);
    |}
.

End traits_iterator_IntoIterator.

Section traits_iterator_Iterator.
Context `{RRGS : !refinedrustGS Σ}.
Definition traits_iterator_Iterator_spec_incl `{Self_rt : !RT} `{Item_rt : !RT} (spec1: ((traits_iterator_Iterator_spec (Self_rt) (Item_rt)))) (spec2: ((traits_iterator_Iterator_spec (Self_rt) (Item_rt)))) : Prop :=
  (∀ (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )), (function_subtype ((spec1.(traits_iterator_Iterator_all_spec) (F_rt) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_all_spec) (F_rt) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )), (function_subtype ((spec1.(traits_iterator_Iterator_collect_spec) (B_rt) (B_st) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_collect_spec) (B_rt) (B_st) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )), (function_subtype ((spec1.(traits_iterator_Iterator_fold_spec) (B_rt) (F_rt) (B_st) (F_st) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_fold_spec) (B_rt) (F_rt) (B_st) (F_st) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )), (function_subtype ((spec1.(traits_iterator_Iterator_map_spec) (B_rt) (F_rt) (B_st) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_map_spec) (B_rt) (F_rt) (B_st) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)), (function_subtype ((spec1.(traits_iterator_Iterator_max_spec) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_max_spec) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )), (function_subtype ((spec1.(traits_iterator_Iterator_max_by_spec) (F_rt) (F_st) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_max_by_spec) (F_rt) (F_st) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)), (function_subtype ((spec1.(traits_iterator_Iterator_min_spec) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_min_spec) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )), (function_subtype ((spec1.(traits_iterator_Iterator_min_by_spec) (F_rt) (F_st) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_min_by_spec) (F_rt) (F_st) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ ((function_subtype (spec1.(traits_iterator_Iterator_next_spec)) (spec2.(traits_iterator_Iterator_next_spec)))) ∧ ((function_subtype (spec1.(traits_iterator_Iterator_nth_spec)) (spec2.(traits_iterator_Iterator_nth_spec)))) ∧ (∀ (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )), (function_subtype ((spec1.(traits_iterator_Iterator_position_spec) (F_rt) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_position_spec) (F_rt) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ (∀ (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )), (function_subtype ((spec1.(traits_iterator_Iterator_reduce_spec) (F_rt) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs))) ((spec2.(traits_iterator_Iterator_reduce_spec) (F_rt) (F_st) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs))))) ∧ ((function_subtype (spec1.(traits_iterator_Iterator_skip_spec)) (spec2.(traits_iterator_Iterator_skip_spec)))) ∧ ((function_subtype (spec1.(traits_iterator_Iterator_take_spec)) (spec2.(traits_iterator_Iterator_take_spec)))) ∧ (∀ (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)), (function_subtype ((spec1.(traits_iterator_Iterator_try_fold_spec) (B_rt) (F_rt) (R_rt) (Try_R_Residual_rt) (B_st) (F_st) (R_st) (Try_R_Residual_st) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (Try_R_spec_attrs))) ((spec2.(traits_iterator_Iterator_try_fold_spec) (B_rt) (F_rt) (R_rt) (Try_R_Residual_rt) (B_st) (F_st) (R_st) (Try_R_Residual_st) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs) (Try_R_spec_attrs))))).
Instance traits_iterator_Iterator_spec_incl_preorder `{Self_rt : !RT} `{Item_rt : !RT} : (PreOrder (traits_iterator_Iterator_spec_incl (Self_rt := Self_rt) (Item_rt := Item_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition traits_iterator_Iterator_all_base_spec (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, P, ClosInv, self, f) : ((_ * ((RT_xt (Item_rt)) → Prop) * (map_inv_ty  _ _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)
        ∗ (ClosInv π self.cur f)
        ∗ (□ (∀ it_state it_state' clos_state e,
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π it_state clos_state -∗
                ∃ pclos, FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[e] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                (∀ b clos_state', FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[e] clos_state' b -∗ ⌜b = true ↔ P e⌝ ∗ ClosInv π it_state' clos_state')))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', ret) : ((_ * _ * _ * _)), ret @ bool_t;
      (* postcondition *) (λ π : thread_id, (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2)
      ∗ (if_iTrue ret (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2' ∗ ⌜Forall P seq⌝))
      ∗ (if_iFalse ret (⌜s2 = s2'⌝ ∗ ∃ seq' e, ⌜seq = seq' ++ [e]⌝ ∗ ⌜Forall P seq'⌝ ∗ ⌜¬ P e⌝))
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (gvar_pobs self.ghost ($# s2'))).

Definition traits_iterator_Iterator_collect_base_spec (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (B_rt, B_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2') : ((_ * _ * _)), traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs.(traits_iterator_FromIterator_FromSequence) seq @ B_ty;
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)
      ∗ (ty_ghost_drop Self_ty π ($# s2))).

Definition traits_iterator_Iterator_fold_base_spec (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (B_rt, B_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, ClosInv, self, init, f) : ((_ * (thread_id → (RT_xt (B_rt)) → list (RT_xt (Item_rt)) → (RT_xt (Self_rt)) → (RT_xt (F_rt)) → iProp Σ) * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, init :@: B_ty, f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)
        ∗ (ClosInv π init [] self f)
        ∗ (□ (∀ seq acc it_state it_state' clos_state e,
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state -∗ 
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π acc seq it_state clos_state -∗
                ∃ pclos, FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[acc; e] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state∗ 
                (∀ acc' clos_state', 
                    FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[acc; e] clos_state' acc' -∗ 
                    ClosInv π acc' (seq ++ [e]) it_state' clos_state' ∗ True)
                ))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', clos_state', ret) : ((_ * _ * _ * _ * _)), ret @ B_ty;
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)
      ∗ (ClosInv π ret seq s2 clos_state')
      ∗ (ty_ghost_drop Self_ty π ($# s2'))
      ∗ (ty_ghost_drop F_ty π ($# clos_state'))).

Definition traits_iterator_Iterator_map_base_spec (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (B_rt, B_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p_inner, Inv, ParamPred, self, f) : ((_ * (map_inv_ty _ _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) * (clos_param_pred_ty _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p_inner self)
        ∗ (Inv π self f)
        ∗ (□ (∀ it_state it_state' clos_state e,
                (☒ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p_inner it_state (Some e) it_state') -∗
                Inv π it_state clos_state -∗
                ∃ pclos, ⌜ParamPred *[e] pclos⌝ ∗ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[e] ∗
                (∀ e' clos_state', ☒ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state' ∗ True)))
        ∗ (□ (∀ it_state it_state' clos_state,
                (☒ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p_inner it_state None it_state') -∗
                Inv π it_state clos_state -∗
                Inv π it_state' clos_state ∗ True))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (adapters_map_Map_inv_t ((Self_rt)) ((F_rt))   <TY> Self_ty <TY> F_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (⌜(ret = mk_map_x self f)%Z⌝)
      ∗ (traits_iterator_Iterator_Inv (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs _ _ _ _ traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs) π (p_inner, ParamPred) ret)).

Definition traits_iterator_Iterator_max_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2') : ((_ * _ * _)), max_list_cmp Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) seq None @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)).

Definition traits_iterator_Iterator_max_by_base_spec (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, ClosInv, self, compare) : ((_ * (thread_id → (option (RT_xt (Item_rt))) → list (RT_xt (Item_rt)) → (RT_xt (Self_rt)) → (RT_xt (F_rt)) → iProp Σ) * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, compare :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)
        ∗ (ClosInv π None [] self compare)
        ∗ (∀ e it_state', 
                ClosInv π None [] self compare -∗ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self (Some e) it_state' -∗ 
                ClosInv π (Some e) [e] it_state' compare ∗ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self (Some e) it_state')
        ∗ (□ (∀ seq it_state it_state' clos_state e acc,
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state -∗ 
                □ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π (Some acc) seq it_state clos_state -∗
                ∃ pclos, FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[e; acc] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                (∀ ord clos_state', 
                    FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[e; acc] clos_state' ord -∗ 
                    ClosInv π (Some (if bool_decide (ord = Less) then acc else e)) (seq ++ [e]) it_state' clos_state' ∗ 
                    True)
                )))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', clos_state', ret) : ((_ * _ * _ * _ * _)), ret @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (ClosInv π ret seq s2 clos_state')
      ∗ (ty_ghost_drop Self_ty π ($# s2'))
      ∗ (ty_ghost_drop F_ty π ($# clos_state'))).

Definition traits_iterator_Iterator_min_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2') : ((_ * _ * _)), min_list_cmp Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) seq None @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)).

Definition traits_iterator_Iterator_min_by_base_spec (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, ClosInv, self, compare) : ((_ * (thread_id → (option (RT_xt (Item_rt))) → list (RT_xt (Item_rt)) → (RT_xt (Self_rt)) → (RT_xt (F_rt)) → iProp Σ) * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, compare :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)
        ∗ (ClosInv π None [] self compare)
        ∗ (∀ e it_state', 
                ClosInv π None [] self compare -∗ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self (Some e) it_state' -∗ 
                ClosInv π (Some e) [e] it_state' compare ∗ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self (Some e) it_state')
        ∗ (□ (∀ seq it_state it_state' clos_state e acc,
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state -∗ 
                □ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π (Some acc) seq it_state clos_state -∗
                ∃ pclos, FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[e; acc] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                (∀ ord clos_state', 
                    FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[e; acc] clos_state' ord -∗ 
                    ClosInv π (Some (if bool_decide (ord = Less) then e else acc)) (seq ++ [e]) it_state' clos_state' ∗ 
                    True)
                )))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', clos_state', ret) : ((_ * _ * _ * _ * _)), ret @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (ClosInv π ret seq s2 clos_state')
      ∗ (ty_ghost_drop Self_ty π ($# s2'))
      ∗ (ty_ghost_drop F_ty π ($# clos_state'))).

Definition traits_iterator_Iterator_next_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (new_it_state, ret) : ((((RT_xt (Self_rt))) * _)), ret @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (($# new_it_state)))
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self.cur ret new_it_state)
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p new_it_state)).

Definition traits_iterator_Iterator_nth_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, n) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), n :@: (int USize);
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (s2, s2', seq, ret) : ((_ * _ * _ * _)), ret @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2)
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (gvar_pobs self.ghost ($# s2'))
      ∗ (⌜(length seq ≤ Z.to_nat n)%Z⌝)
      ∗ (if_iNone ret (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2'))
      ∗ (if_iSome ret (λ ret, traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 (Some ret) s2' ∗ ⌜length seq = Z.to_nat n⌝))).

Definition traits_iterator_Iterator_position_base_spec (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, P, ClosInv, self, f) : ((_ * ((RT_xt (Item_rt)) → Prop) * (map_inv_ty  _ _ _ _ FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)
        ∗ (ClosInv π self.cur f)
        ∗ (□ (∀ it_state it_state' clos_state e,
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π it_state clos_state -∗
                ∃ pclos, FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[e] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                (∀ b clos_state', FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[e] clos_state' b -∗ ⌜b = true ↔ P e⌝ ∗ ClosInv π it_state' clos_state')))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', clos_state', ret) : ((_ * _ * _ * _ * _)), ret @ (Option_ty (Z)  <TY> (int USize) <INST!>);
      (* postcondition *) (λ π : thread_id, (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2)
      ∗ (⌜(Forall (λ x, ¬ P x) seq)%Z⌝)
      ∗ (if_iNone ret (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2' ∗ ClosInv π s2 clos_state'))
      ∗ (if_iSome ret (λ idx, ⌜length seq = Z.to_nat idx⌝ ∗ ∃ e, traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 (Some e) s2' ∗ ClosInv π s2' clos_state' ∗ ⌜P e⌝ ∗ True))
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (gvar_pobs self.ghost ($# s2'))
      ∗ (ty_ghost_drop F_ty π ($# clos_state'))).

Definition traits_iterator_Iterator_reduce_base_spec (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, ClosInv, self, f) : ((_ * (thread_id → option (RT_xt (Item_rt)) → list (RT_xt (Item_rt)) → (RT_xt (Self_rt)) → (RT_xt (F_rt)) → iProp Σ) * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)
        ∗ (ClosInv π None [] self f)
        ∗ (∀ e it_state', 
                ClosInv π None [] self f -∗ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self (Some e) it_state' -∗ 
                ClosInv π (Some e) [e] it_state' f ∗ traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p self (Some e) it_state')
        ∗ (□ (∀ seq acc it_state it_state' clos_state e,
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq it_state -∗ 
                □ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π (Some acc) seq it_state clos_state -∗
                ∃ pclos, FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[acc; e] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                (∀ acc' clos_state', 
                    FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[acc; e] clos_state' acc' -∗ 
                    ClosInv π (Some acc') (seq ++ [e]) it_state' clos_state' ∗ True)
                )))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', clos_state', ret) : ((_ * _ * _ * _ * _)), ret @ (Option_ty ((Item_rt))  <TY> Item_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2')
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self seq s2)
      ∗ (ClosInv π ret seq s2 clos_state')
      ∗ (ty_ghost_drop Self_ty π ($# s2'))
      ∗ (ty_ghost_drop F_ty π ($# clos_state'))).

Definition traits_iterator_Iterator_skip_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, n) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, n :@: (int USize);
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (adapters_skip_Skip_inv_t ((Self_rt))   <TY> Self_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (⌜(ret = (self, Z.to_nat n))%Z⌝)
      ∗ (traits_iterator_Iterator_Inv (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs _ _ traits_iterator_Iterator_Self_spec_attrs) π p ret)).

Definition traits_iterator_Iterator_take_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, n) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, n :@: (int USize);
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (adapters_take_Take_inv_t ((Self_rt))   <TY> Self_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (⌜(ret = (self, Z.to_nat n))%Z⌝)
      ∗ (traits_iterator_Iterator_Inv (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs _ _ traits_iterator_Iterator_Self_spec_attrs) π p ret)).

Definition traits_iterator_Iterator_try_fold_base_spec (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; B_ty; F_ty; R_ty; Try_R_Residual_ty]) : ([(Self_rt, Self_st); (Item_rt, Item_st); (B_rt, B_st); (F_rt, F_st); (R_rt, R_st); (Try_R_Residual_rt, Try_R_Residual_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, ClosInv, self, init, f) : ((_ * (thread_id → result (RT_xt (B_rt)) _ → list (RT_xt (Item_rt)) → (RT_xt (Self_rt)) → (RT_xt (F_rt)) → iProp Σ) * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), init :@: B_ty, f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p self.cur)
        ∗ (ClosInv π (Ok init) [] self.cur f)
        ∗ (□ (∀ seq acc it_state it_state' clos_state e,
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq it_state -∗ 
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' -∗
                ClosInv π (Ok acc) seq it_state clos_state -∗
                ∃ pclos, FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos clos_state *[acc; e] ∗
                traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p it_state (Some e) it_state' ∗ 
                IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq it_state ∗  
                (∀ b clos_state', FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos clos_state *[acc; e] clos_state' b -∗ 
                    ClosInv π (Try_R_spec_attrs.(Try_BranchFn) b) (seq ++ [e]) it_state' clos_state' ∗ True)
                    ))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (seq, s2, s2', clos_state', ret) : ((_ * _ * _ * _ * _)), ret @ R_ty;
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost ($# s2'))
      ∗ (traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Inv) π p s2')
      ∗ (IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π p self.cur seq s2)
      ∗ (ClosInv π (Try_R_spec_attrs.(Try_BranchFn) ret) seq s2 clos_state')
      ∗ (if_iOk (Try_R_spec_attrs.(Try_BranchFn) ret) (λ ret, traits_iterator_Iterator_Self_spec_attrs.(traits_iterator_Iterator_Next) π p s2 None s2' ∗ True))
      ∗ (if_iErr (Try_R_spec_attrs.(Try_BranchFn) ret) (λ err, ⌜s2 = s2'⌝ ∗ True))
      ∗ (ty_ghost_drop F_ty π ($# clos_state'))).

Definition traits_iterator_Iterator_base_spec (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (_ATTRS: ((traits_iterator_Iterator_spec_attrs ((Self_rt)) ((Item_rt))))) : (spec_with _ _ (traits_iterator_Iterator_spec ((Self_rt)) ((Item_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), {|
      traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
        (traits_iterator_Iterator_all_base_spec ((Self_rt)) ((Item_rt)) ((F_rt)) (Self_st) (Item_st) (F_st)) _ATTRS FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 1 [F_rt] fn_spec);
      traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
        (traits_iterator_Iterator_collect_base_spec ((Self_rt)) ((Item_rt)) ((B_rt)) (Self_st) (Item_st) (B_st)) _ATTRS traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [B_rt] fn_spec);
      traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
        (traits_iterator_Iterator_fold_base_spec ((Self_rt)) ((Item_rt)) ((B_rt)) ((F_rt)) (Self_st) (Item_st) (B_st) (F_st)) _ATTRS FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
      traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
        (traits_iterator_Iterator_map_base_spec ((Self_rt)) ((Item_rt)) ((B_rt)) ((F_rt)) (Self_st) (Item_st) (B_st) (F_st)) _ATTRS FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
      traits_iterator_Iterator_max_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
        (traits_iterator_Iterator_max_base_spec ((Self_rt)) ((Item_rt)) (Self_st) (Item_st)) _ATTRS PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [] fn_spec);
      traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
        (traits_iterator_Iterator_max_by_base_spec ((Self_rt)) ((Item_rt)) ((F_rt)) (Self_st) (Item_st) (F_st)) _ATTRS FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [F_rt] fn_spec);
      traits_iterator_Iterator_min_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
        (traits_iterator_Iterator_min_base_spec ((Self_rt)) ((Item_rt)) (Self_st) (Item_st)) _ATTRS PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [] fn_spec);
      traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
        (traits_iterator_Iterator_min_by_base_spec ((Self_rt)) ((Item_rt)) ((F_rt)) (Self_st) (Item_st) (F_st)) _ATTRS FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [F_rt] fn_spec);
      traits_iterator_Iterator_next_spec  :=
        (traits_iterator_Iterator_next_base_spec ((Self_rt)) ((Item_rt)) (Self_st) (Item_st)) _ATTRS 
           <TY> Self_ty <TY> Item_ty : (spec_with 1 [] fn_spec);
      traits_iterator_Iterator_nth_spec  :=
        (traits_iterator_Iterator_nth_base_spec ((Self_rt)) ((Item_rt)) (Self_st) (Item_st)) _ATTRS 
           <TY> Self_ty <TY> Item_ty : (spec_with 1 [] fn_spec);
      traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
        (traits_iterator_Iterator_position_base_spec ((Self_rt)) ((Item_rt)) ((F_rt)) (Self_st) (Item_st) (F_st)) _ATTRS FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 1 [F_rt] fn_spec);
      traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
        (traits_iterator_Iterator_reduce_base_spec ((Self_rt)) ((Item_rt)) ((F_rt)) (Self_st) (Item_st) (F_st)) _ATTRS FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [F_rt] fn_spec);
      traits_iterator_Iterator_skip_spec  :=
        (traits_iterator_Iterator_skip_base_spec ((Self_rt)) ((Item_rt)) (Self_st) (Item_st)) _ATTRS 
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [] fn_spec);
      traits_iterator_Iterator_take_spec  :=
        (traits_iterator_Iterator_take_base_spec ((Self_rt)) ((Item_rt)) (Self_st) (Item_st)) _ATTRS 
           <TY> Self_ty <TY> Item_ty : (spec_with 0 [] fn_spec);
      traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
        (traits_iterator_Iterator_try_fold_base_spec ((Self_rt)) ((Item_rt)) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) (Self_st) (Item_st) (B_st) (F_st) (R_st) (Try_R_Residual_st)) _ATTRS FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs Try_R_spec_attrs
           <TY> Self_ty <TY> Item_ty : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
    |}
.

End traits_iterator_Iterator.

Section step_Step.
Context `{RRGS : !refinedrustGS Σ}.
Definition step_Step_spec_incl `{Self_rt : !RT} (spec1: ((step_Step_spec (Self_rt)))) (spec2: ((step_Step_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(step_Step_backward_spec)) (spec2.(step_Step_backward_spec)))) ∧ ((function_subtype (spec1.(step_Step_backward_checked_spec)) (spec2.(step_Step_backward_checked_spec)))) ∧ ((function_subtype (spec1.(step_Step_backward_unchecked_spec)) (spec2.(step_Step_backward_unchecked_spec)))) ∧ ((function_subtype (spec1.(step_Step_forward_spec)) (spec2.(step_Step_forward_spec)))) ∧ ((function_subtype (spec1.(step_Step_forward_checked_spec)) (spec2.(step_Step_forward_checked_spec)))) ∧ ((function_subtype (spec1.(step_Step_forward_unchecked_spec)) (spec2.(step_Step_forward_unchecked_spec)))) ∧ ((function_subtype (spec1.(step_Step_steps_between_spec)) (spec2.(step_Step_steps_between_spec)))).
Instance step_Step_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (step_Step_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition step_Step_backward_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (n, start, count) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) start :@: Self_ty, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(step_Step_Self_spec_attrs.(step_Step_Backward) start (Z.to_nat count) = Some n)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, n @ Self_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_backward_checked_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (start, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) start :@: Self_ty, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, step_Step_Self_spec_attrs.(step_Step_Backward) start (Z.to_nat count) @ (Option_ty ((Self_rt))  <TY> Self_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_backward_unchecked_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (n, start, count) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) start :@: Self_ty, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(step_Step_Self_spec_attrs.(step_Step_Backward) start (Z.to_nat count) = Some n)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, n @ Self_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_forward_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (n, start, count) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) start :@: Self_ty, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(step_Step_Self_spec_attrs.(step_Step_Forward) start (Z.to_nat count) = Some n)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, n @ Self_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_forward_checked_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (start, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) start :@: Self_ty, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, step_Step_Self_spec_attrs.(step_Step_Forward) start (Z.to_nat count) @ (Option_ty ((Self_rt))  <TY> Self_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_forward_unchecked_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (n, start, count) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) start :@: Self_ty, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(step_Step_Self_spec_attrs.(step_Step_Forward) start (Z.to_nat count) = Some n)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, n @ Self_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_steps_between_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (start, last) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) start :@: (shr_ref ulft_1 Self_ty), last :@: (shr_ref ulft_2 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, step_Step_Self_spec_attrs.(step_Step_StepsBetween) start last @ (tuple2_ty (Z) (((((Option_rt)) (Z))))  <TY> (int USize) <TY> (Option_ty (Z)  <TY> (int USize) <INST!>) <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition step_Step_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (_ATTRS: ((step_Step_spec_attrs ((Self_rt)) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs)))) : (spec_with _ _ (step_Step_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      step_Step_backward_spec  :=
        (step_Step_backward_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      step_Step_backward_checked_spec  :=
        (step_Step_backward_checked_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      step_Step_backward_unchecked_spec  :=
        (step_Step_backward_unchecked_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      step_Step_forward_spec  :=
        (step_Step_forward_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      step_Step_forward_checked_spec  :=
        (step_Step_forward_checked_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      step_Step_forward_unchecked_spec  :=
        (step_Step_forward_unchecked_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
      step_Step_steps_between_spec  :=
        (step_Step_steps_between_base_spec ((Self_rt)) (Self_st)) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 2 [] fn_spec);
    |}
.

End step_Step.

Section step_TrustedStep.
Context `{RRGS : !refinedrustGS Σ}.
Definition step_TrustedStep_spec_incl `{Self_rt : !RT} (spec1: ((step_TrustedStep_spec (Self_rt)))) (spec2: ((step_TrustedStep_spec (Self_rt)))) : Prop :=
  True.
Instance step_TrustedStep_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (step_TrustedStep_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition step_TrustedStep_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (Copy_Self_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs)) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (_ATTRS: ((step_TrustedStep_spec_attrs ((Self_rt)) (Clone_Self_spec_attrs) (PartialEq_Self_Self_spec_attrs) (PartialOrd_Self_Self_spec_attrs) (Copy_Self_spec_attrs) (step_Step_Self_spec_attrs)))) : (spec_with _ _ (step_TrustedStep_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_step_TrustedStep_spec _ _ ((Self_rt))).

End step_TrustedStep.

Section traits_iterator_FromIterator_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_traits_iterator_FromIterator_from_iter (Self_rt: RT) (A_rt: RT) (T_rt: RT) (traits_iterator_IntoIterator_T_IntoIter_rt: RT) (Self_st: syn_type) (A_st: syn_type) (T_st: syn_type) (traits_iterator_IntoIterator_T_IntoIter_st: syn_type) (traits_iterator_FromIterator_Self_A_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (Self_rt) (A_rt) )) (traits_iterator_FromIterator_Self_A_spec: (spec_with 0 [] (traits_iterator_FromIterator_spec (RRGS:=RRGS) (Self_rt) (A_rt)))) (traits_iterator_IntoIterator_T_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt) )) (traits_iterator_IntoIterator_T_spec: (spec_with 0 [] (traits_iterator_IntoIterator_spec (RRGS:=RRGS) (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; A_ty; T_ty; traits_iterator_IntoIterator_T_IntoIter_ty]) : ([Self_rt; A_rt; T_rt; traits_iterator_IntoIterator_T_IntoIter_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_FromIterator_spec_incl traits_iterator_FromIterator_Self_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_FromIterator_base_spec (Self_rt) (A_rt) Self_st A_st traits_iterator_FromIterator_Self_A_spec_attrs<TY> Self_ty <TY> A_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_IntoIterator_spec_incl traits_iterator_IntoIterator_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_IntoIterator_base_spec (T_rt) (traits_iterator_IntoIterator_T_IntoIter_rt) (A_rt) T_st traits_iterator_IntoIterator_T_IntoIter_st A_st traits_iterator_IntoIterator_T_spec_attrs<TY> T_ty <TY> traits_iterator_IntoIterator_T_IntoIter_ty <TY> A_ty <INST!>)))).
End traits_iterator_FromIterator_trait_req_incls.

Section traits_iterator_IntoIterator_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_traits_iterator_IntoIterator_into_iter (Self_rt: RT) (IntoIter_rt: RT) (Item_rt: RT) (Self_st: syn_type) (IntoIter_st: syn_type) (Item_st: syn_type) (traits_iterator_IntoIterator_Self_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (Self_rt) (IntoIter_rt) (Item_rt) )) (traits_iterator_IntoIterator_Self_spec: (spec_with 0 [] (traits_iterator_IntoIterator_spec (RRGS:=RRGS) (Self_rt) (IntoIter_rt) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; IntoIter_ty; Item_ty]) : ([Self_rt; IntoIter_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_IntoIterator_spec_incl traits_iterator_IntoIterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_IntoIterator_base_spec (Self_rt) (IntoIter_rt) (Item_rt) Self_st IntoIter_st Item_st traits_iterator_IntoIterator_Self_spec_attrs<TY> Self_ty <TY> IntoIter_ty <TY> Item_ty <INST!>)))).
End traits_iterator_IntoIterator_trait_req_incls.

Section traits_iterator_Iterator_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_traits_iterator_Iterator_all (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((Item_rt)))) bool F_st ((tuple1_sls (Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((Item_rt))  <TY> Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((Item_rt)))) bool F_st ((tuple1_sls (Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((Item_rt))  <TY> Item_ty <INST!>) <TY> bool_t <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_collect (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (traits_iterator_FromIterator_spec (RRGS:=RRGS) (B_rt) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty]) : ([Self_rt; Item_rt; B_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_FromIterator_spec_incl traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_FromIterator_base_spec (B_rt) (Item_rt) B_st Item_st traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> B_ty <TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_fold (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt)))) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([Self_rt; Item_rt; B_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) F_st ((tuple2_sls (B_st) (Item_st)) : syn_type) B_st FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((B_rt)) ((Item_rt))  <TY> B_ty <TY> Item_ty <INST!>) <TY> B_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_BSelfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) F_st ((tuple2_sls (B_st) (Item_st)) : syn_type) B_st FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((B_rt)) ((Item_rt))  <TY> B_ty <TY> Item_ty <INST!>) <TY> B_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_map (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt)))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; B_ty; F_ty]) : ([Self_rt; Item_rt; B_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) F_st ((tuple1_sls (Item_st)) : syn_type) B_st FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((Item_rt))  <TY> Item_ty <INST!>) <TY> B_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) F_st ((tuple1_sls (Item_st)) : syn_type) B_st FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((Item_rt))  <TY> Item_ty <INST!>) <TY> B_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_max (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Item_rt) (Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Item_rt) (Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Item_rt) (Item_rt) Item_st Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Item_rt) Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Item_rt) (Item_rt) Item_st Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Item_rt) Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_max_by (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt)))  <TY> (shr_ref _lft_for_1 Item_ty) <TY> (shr_ref _lft_for_0 Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt)))  <TY> (shr_ref _lft_for_1 Item_ty) <TY> (shr_ref _lft_for_0 Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_min (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Item_rt) (Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Item_rt) (Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Item_rt) (Item_rt) Item_st Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (Item_rt) Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Item_rt) (Item_rt) Item_st Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (Item_rt) Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_min_by (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt)))  <TY> (shr_ref _lft_for_1 Item_ty) <TY> (shr_ref _lft_for_0 Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt)))  <TY> (shr_ref _lft_for_1 Item_ty) <TY> (shr_ref _lft_for_0 Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_next (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_nth (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_position (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((Item_rt)))) bool F_st ((tuple1_sls (Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((Item_rt))  <TY> Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((Item_rt)))) bool F_st ((tuple1_sls (Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((Item_rt))  <TY> Item_ty <INST!>) <TY> bool_t <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_reduce (Self_rt: RT) (Item_rt: RT) (F_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt)))) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty; F_ty]) : ([Self_rt; Item_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) F_st ((tuple2_sls (Item_st) (Item_st)) : syn_type) Item_st FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((Item_rt)) ((Item_rt))  <TY> Item_ty <TY> Item_ty <INST!>) <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) F_st ((tuple2_sls (Item_st) (Item_st)) : syn_type) Item_st FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((Item_rt)) ((Item_rt))  <TY> Item_ty <TY> Item_ty <INST!>) <TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_skip (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_take (Self_rt: RT) (Item_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Item_ty]) : ([Self_rt; Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>)))).
  Definition trait_incl_of_traits_iterator_Iterator_try_fold (Self_rt: RT) (Item_rt: RT) (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (Item_rt)))) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt)))) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec: (spec_with 0 [] (FromResidual_spec (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt)))) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt)))) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) (Try_R_spec: (spec_with 0 [] (Try_spec (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Item_ty; B_ty; F_ty; R_ty; Try_R_Residual_ty]) : ([Self_rt; Item_rt; B_rt; F_rt; R_rt; Try_R_Residual_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (Item_rt) Self_st Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) F_st ((tuple2_sls (B_st) (Item_st)) : syn_type) R_st FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((B_rt)) ((Item_rt))  <TY> B_ty <TY> Item_ty <INST!>) <TY> R_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FromResidual_spec_incl FromResidual_R_Rasstd_ops_Try_Residual_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FromResidual_base_spec (R_rt) (Try_R_Residual_rt) R_st Try_R_Residual_st FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs<TY> R_ty <TY> Try_R_Residual_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_BSelfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) F_st ((tuple2_sls (B_st) (Item_st)) : syn_type) R_st FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((B_rt)) ((Item_rt))  <TY> B_ty <TY> Item_ty <INST!>) <TY> R_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Try_spec_incl Try_R_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Try_base_spec (R_rt) (B_rt) (Try_R_Residual_rt) R_st B_st Try_R_Residual_st FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs Try_R_spec_attrs<TY> R_ty <TY> B_ty <TY> Try_R_Residual_ty <INST!>)))).
End traits_iterator_Iterator_trait_req_incls.

Section step_Step_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_step_Step_backward (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_step_Step_backward_checked (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_step_Step_backward_unchecked (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_step_Step_forward (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_step_Step_forward_checked (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_step_Step_forward_unchecked (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_step_Step_steps_between (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) (PartialEq_Self_Self_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) )) (PartialEq_Self_Self_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (PartialOrd_Self_Self_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Self_rt) (Self_rt) PartialEq_Self_Self_spec_attrs)) (PartialOrd_Self_Self_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Self_rt) (Self_rt)))) (step_Step_Self_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (Self_rt) Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs)) (step_Step_Self_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Self_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Self_rt) (Self_rt) Self_st Self_st PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs<TY> Self_ty <TY> Self_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (Self_rt) Self_st Clone_Self_spec_attrs PartialEq_Self_Self_spec_attrs PartialOrd_Self_Self_spec_attrs step_Step_Self_spec_attrs<TY> Self_ty <INST!>)))).
End step_Step_trait_req_incls.

Section step_TrustedStep_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End step_TrustedStep_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_Iastraits_iterator_IntoIterator_into_iter (I_rt: RT) (traits_iterator_Iterator_I_Item_rt: RT) (I_st: syn_type) (traits_iterator_Iterator_I_Item_st: syn_type) (traits_iterator_Iterator_I_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt) )) (traits_iterator_Iterator_I_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[I_ty; traits_iterator_Iterator_I_Item_ty]) : ([I_rt; traits_iterator_Iterator_I_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_I_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (I_rt) (traits_iterator_Iterator_I_Item_rt) I_st traits_iterator_Iterator_I_Item_st traits_iterator_Iterator_I_spec_attrs<TY> I_ty <TY> traits_iterator_Iterator_I_Item_ty <INST!>)))).

Definition type_of_Iastraits_iterator_IntoIterator_into_iter (I_rt: RT) (traits_iterator_Iterator_I_Item_rt: RT) (I_st: syn_type) (traits_iterator_Iterator_I_Item_st: syn_type) (traits_iterator_Iterator_I_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt) )) :=
  spec! ( *[]) : 0 | ( *[I_ty; traits_iterator_Iterator_I_Item_ty]) : ([I_rt; traits_iterator_Iterator_I_Item_rt] : list RT),((traits_iterator_IntoIterator_base_spec ((I_rt)) ((I_rt)) ((traits_iterator_Iterator_I_Item_rt)) (I_st) (I_st) (traits_iterator_Iterator_I_Item_st) ((Iastraits_iterator_IntoIterator_spec_attrs (I_rt) (traits_iterator_Iterator_I_Item_rt) (traits_iterator_Iterator_I_spec_attrs))))
     <TY> I_ty <TY> I_ty <TY> traits_iterator_Iterator_I_Item_ty <INST!>).(traits_iterator_IntoIterator_into_iter_spec)   <MERGE!>.

Definition trait_incl_of_adapters_map_MapMIMFastraits_iterator_Iterator_next (MB_rt: RT) (MI_rt: RT) (MF_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MB_st: syn_type) (MI_st: syn_type) (MF_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) (traits_iterator_Iterator_MI_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt)))) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt)))) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MI_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_MI_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (MI_rt) (traits_iterator_Iterator_MI_Item_rt) MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs<TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_MF_MIastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) MF_st ((tuple1_sls (traits_iterator_Iterator_MI_Item_st)) : syn_type) MB_st FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs<TY> MF_ty <TY> (tuple1_ty ((traits_iterator_Iterator_MI_Item_rt))  <TY> traits_iterator_Iterator_MI_Item_ty <INST!>) <TY> MB_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_MF_MIastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) MF_st ((tuple1_sls (traits_iterator_Iterator_MI_Item_st)) : syn_type) MB_st FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs<TY> MF_ty <TY> (tuple1_ty ((traits_iterator_Iterator_MI_Item_rt))  <TY> traits_iterator_Iterator_MI_Item_ty <INST!>) <TY> MB_ty <INST!>)))).

Definition type_of_adapters_map_MapMIMFastraits_iterator_Iterator_next (MB_rt: RT) (MI_rt: RT) (MF_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MB_st: syn_type) (MI_st: syn_type) (MF_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) :=
  spec! ( *[]) : 0 | ( *[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MI_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT),((traits_iterator_Iterator_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) ((adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty <INST!>).(traits_iterator_Iterator_next_spec)   <MERGE!>.

Definition trait_incl_of_adapters_skip_SkipMIastraits_iterator_Iterator_next (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) (traits_iterator_Iterator_MI_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_MI_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (MI_rt) (traits_iterator_Iterator_MI_Item_rt) MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs<TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <INST!>)))).

Definition type_of_adapters_skip_SkipMIastraits_iterator_Iterator_next (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) :=
  spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT),((traits_iterator_Iterator_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) ((adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs))))
     <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty <INST!>).(traits_iterator_Iterator_next_spec)   <MERGE!>.

Definition trait_incl_of_adapters_take_TakeMIastraits_iterator_Iterator_next (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) (traits_iterator_Iterator_MI_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_MI_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (MI_rt) (traits_iterator_Iterator_MI_Item_rt) MI_st traits_iterator_Iterator_MI_Item_st traits_iterator_Iterator_MI_spec_attrs<TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <INST!>)))).

Definition type_of_adapters_take_TakeMIastraits_iterator_Iterator_next (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) :=
  spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT),((traits_iterator_Iterator_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) ((adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs))))
     <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty <INST!>).(traits_iterator_Iterator_next_spec)   <MERGE!>.

Definition trait_incl_of_u16asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U16)) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (u16asstep_Step_spec_attrs))
     <TY> (int U16) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_u32asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U32)) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (u32asstep_Step_spec_attrs))
     <TY> (int U32) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_u64asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U64)) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (u64asstep_Step_spec_attrs))
     <TY> (int U64) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_u8asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U8)) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (u8asstep_Step_spec_attrs))
     <TY> (int U8) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_usizeasstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType USize)) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (usizeasstep_Step_spec_attrs))
     <TY> (int USize) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_step_impltraits_iterator_Iteratorforstd_ops_RangeA_next (A_rt: RT) (A_st: syn_type) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (Clone_A_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (A_rt)))) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialEq_A_A_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (A_rt) (A_rt)))) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (PartialOrd_A_A_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (A_rt) (A_rt)))) (step_Step_A_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (A_rt) Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs)) (step_Step_A_spec: (spec_with 0 [] (step_Step_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (A_rt) A_st Clone_A_spec_attrs<TY> A_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_A_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (A_rt) (A_rt) A_st A_st PartialEq_A_A_spec_attrs<TY> A_ty <TY> A_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_A_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (A_rt) (A_rt) A_st A_st PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs<TY> A_ty <TY> A_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl step_Step_spec_incl step_Step_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), step_Step_base_spec (A_rt) A_st Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs step_Step_A_spec_attrs<TY> A_ty <INST!>)))).

Definition type_of_step_impltraits_iterator_Iteratorforstd_ops_RangeA_next (A_rt: RT) (A_st: syn_type) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (step_Step_A_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (A_rt) Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs)) :=
  spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT),((traits_iterator_Iterator_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) ((step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs))))
     <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty <INST!>).(traits_iterator_Iterator_next_spec)   <MERGE!>.

Definition trait_incl_of_traits_iterator_Iterator_all_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; ulft3]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>)))).

Definition type_of_traits_iterator_Iterator_all_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) :=
  fn(∀ ( *[ulft1; ulft3]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([(Self_rt, Self_st); (F_rt, F_st); (traits_iterator_Iterator_Self_Item_rt, traits_iterator_Iterator_Self_Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (capture_f_, _γf, __γclos, pclos, _arg_0, b) : (((RT_xt ((F_rt))) * gname * gname * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft1); (ϝ, ulft3)]);
      (* args......... *) (( *[(((capture_f_), _γf))]), __γclos) :@: (mut_ref ulft3 (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>)), _arg_0 :@: unit_t, b :@: traits_iterator_Iterator_Self_Item_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_f_ *[b])) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (capture_f__new, res) : (((RT_xt ((F_rt))) * (bool))), if res then Ok tt else Err tt @ (ControlFlow_ty (unit) (unit)  <TY> unit_t <TY> unit_t <INST!>);
      (* postcondition *) (λ π : thread_id, (gvar_pobs __γclos ($#@{(((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))}  *[((capture_f__new), _γf)]))
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_f_ *[b] capture_f__new res)).

Definition trait_incl_of_traits_iterator_Iterator_max_closure0 (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2; ulft3]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>)))).

Definition type_of_traits_iterator_Iterator_max_closure0 (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2; ulft3]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([(Self_rt, Self_st); (traits_iterator_Iterator_Self_Item_rt, traits_iterator_Iterator_Self_Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (__γclos, a, b) : ((gname * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2); (ϝ, ulft3)]);
      (* args......... *) ((()), __γclos) :@: (mut_ref ulft3 unit_t), a :@: (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty), b :@: (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) a b @ (Ordering_ty   <INST!>);
      (* postcondition *) (λ π : thread_id, (gvar_pobs __γclos ($#@{unit} ()))).

Definition trait_incl_of_traits_iterator_Iterator_max_by_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).

Definition type_of_traits_iterator_Iterator_max_by_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) :=
  fn(∀ ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([(Self_rt, Self_st); (F_rt, F_st); (traits_iterator_Iterator_Self_Item_rt, traits_iterator_Iterator_Self_Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (capture_compare_, _γcompare, __γclos, pclos, a, b) : (((RT_xt ((F_rt))) * gname * gname * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft1); (ϝ, ulft2)]);
      (* args......... *) (( *[(((capture_compare_), _γcompare))]), __γclos) :@: (mut_ref ulft2 (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>)), a :@: traits_iterator_Iterator_Self_Item_ty, b :@: traits_iterator_Iterator_Self_Item_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_compare_ *[b; a])) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (capture_compare__new, ord) : (((RT_xt ((F_rt))) * _)), if bool_decide(ord = Less) then a else b @ traits_iterator_Iterator_Self_Item_ty;
      (* postcondition *) (λ π : thread_id, (gvar_pobs __γclos ($#@{(((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))}  *[((capture_compare__new), _γcompare)]))
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_compare_ *[b; a] capture_compare__new ord)).

Definition trait_incl_of_traits_iterator_Iterator_min_closure0 (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2; ulft3]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>)))).

Definition type_of_traits_iterator_Iterator_min_closure0 (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  fn(∀ ( *[ulft_1; ulft_2; ulft3]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([(Self_rt, Self_st); (traits_iterator_Iterator_Self_Item_rt, traits_iterator_Iterator_Self_Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (__γclos, a, b) : ((gname * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2); (ϝ, ulft3)]);
      (* args......... *) ((()), __γclos) :@: (mut_ref ulft3 unit_t), a :@: (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty), b :@: (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) a b @ (Ordering_ty   <INST!>);
      (* postcondition *) (λ π : thread_id, (gvar_pobs __γclos ($#@{unit} ()))).

Definition trait_incl_of_traits_iterator_Iterator_min_by_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).

Definition type_of_traits_iterator_Iterator_min_by_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) :=
  fn(∀ ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([(Self_rt, Self_st); (F_rt, F_st); (traits_iterator_Iterator_Self_Item_rt, traits_iterator_Iterator_Self_Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (capture_compare_, _γcompare, __γclos, pclos, a, b) : (((RT_xt ((F_rt))) * gname * gname * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft1); (ϝ, ulft2)]);
      (* args......... *) (( *[(((capture_compare_), _γcompare))]), __γclos) :@: (mut_ref ulft2 (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>)), a :@: traits_iterator_Iterator_Self_Item_ty, b :@: traits_iterator_Iterator_Self_Item_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_compare_ *[b; a])) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (capture_compare__new, ord) : (((RT_xt ((F_rt))) * _)), if bool_decide(ord = Less) then b else a @ traits_iterator_Iterator_Self_Item_ty;
      (* postcondition *) (λ π : thread_id, (gvar_pobs __γclos ($#@{(((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))}  *[((capture_compare__new), _γcompare)]))
      ∗ (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_compare_ *[b; a] capture_compare__new ord)).

Definition trait_incl_of_adapters_map_Map_IF_new (I_rt: RT) (F_rt: RT) (I_st: syn_type) (F_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[I_ty; F_ty]) : ([I_rt; F_rt] : list RT), (True).

Definition type_of_adapters_map_Map_IF_new (I_rt: RT) (F_rt: RT) (I_st: syn_type) (F_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[I_ty; F_ty]) : ([(I_rt, I_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (iter, f) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) iter :@: I_ty, f :@: F_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, mk_map_x iter f @ (adapters_map_Map_inv_t ((I_rt)) ((F_rt))   <TY> I_ty <TY> F_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_adapters_skip_Skip_I_new (I_rt: RT) (I_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), (True).

Definition type_of_adapters_skip_Skip_I_new (I_rt: RT) (I_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[I_ty]) : ([(I_rt, I_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (iter, n) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) iter :@: I_ty, n :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (iter, Z.to_nat n) @ (adapters_skip_Skip_inv_t ((I_rt))   <TY> I_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_adapters_take_Take_I_new (I_rt: RT) (I_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[I_ty]) : ([I_rt] : list RT), (True).

Definition type_of_adapters_take_Take_I_new (I_rt: RT) (I_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[I_ty]) : ([(I_rt, I_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (iter, n) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) iter :@: I_ty, n :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (iter, Z.to_nat n) @ (adapters_take_Take_inv_t ((I_rt))   <TY> I_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).


Definition trait_incl_of_i128asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I128)) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (i128asstep_Step_spec_attrs))
     <TY> (int I128) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i128asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I128)) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (i128asstep_Step_spec_attrs))
     <TY> (int I128) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i128asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I128)) (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (i128asstep_Step_spec_attrs))
     <TY> (int I128) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_i16asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I16)) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (i16asstep_Step_spec_attrs))
     <TY> (int I16) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i16asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I16)) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (i16asstep_Step_spec_attrs))
     <TY> (int I16) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i16asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I16)) (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (i16asstep_Step_spec_attrs))
     <TY> (int I16) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_i32asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I32)) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (i32asstep_Step_spec_attrs))
     <TY> (int I32) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i32asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I32)) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (i32asstep_Step_spec_attrs))
     <TY> (int I32) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i32asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I32)) (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (i32asstep_Step_spec_attrs))
     <TY> (int I32) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_i64asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I64)) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (i64asstep_Step_spec_attrs))
     <TY> (int I64) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i64asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I64)) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (i64asstep_Step_spec_attrs))
     <TY> (int I64) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i64asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I64)) (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (i64asstep_Step_spec_attrs))
     <TY> (int I64) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_i8asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I8)) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (i8asstep_Step_spec_attrs))
     <TY> (int I8) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i8asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I8)) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (i8asstep_Step_spec_attrs))
     <TY> (int I8) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_i8asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType I8)) (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (i8asstep_Step_spec_attrs))
     <TY> (int I8) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_isizeasstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType ISize)) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (isizeasstep_Step_spec_attrs))
     <TY> (int ISize) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_isizeasstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType ISize)) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (isizeasstep_Step_spec_attrs))
     <TY> (int ISize) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_isizeasstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType ISize)) (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (isizeasstep_Step_spec_attrs))
     <TY> (int ISize) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_u128asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U128)) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (u128asstep_Step_spec_attrs))
     <TY> (int U128) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u128asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U128)) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (u128asstep_Step_spec_attrs))
     <TY> (int U128) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u128asstep_Step_steps_between  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asstep_Step_steps_between  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U128)) (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (u128asstep_Step_spec_attrs))
     <TY> (int U128) <INST!>).(step_Step_steps_between_spec)   <MERGE!>.

Definition trait_incl_of_u16asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U16)) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (u16asstep_Step_spec_attrs))
     <TY> (int U16) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u16asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U16)) (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (u16asstep_Step_spec_attrs))
     <TY> (int U16) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u32asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U32)) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (u32asstep_Step_spec_attrs))
     <TY> (int U32) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u32asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U32)) (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (u32asstep_Step_spec_attrs))
     <TY> (int U32) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u64asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U64)) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (u64asstep_Step_spec_attrs))
     <TY> (int U64) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u64asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U64)) (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (u64asstep_Step_spec_attrs))
     <TY> (int U64) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u8asstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U8)) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (u8asstep_Step_spec_attrs))
     <TY> (int U8) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_u8asstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType U8)) (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (u8asstep_Step_spec_attrs))
     <TY> (int U8) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_usizeasstep_Step_backward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasstep_Step_backward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType USize)) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (usizeasstep_Step_spec_attrs))
     <TY> (int USize) <INST!>).(step_Step_backward_checked_spec)   <MERGE!>.

Definition trait_incl_of_usizeasstep_Step_forward_checked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasstep_Step_forward_checked  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((step_Step_base_spec (Z) ((IntSynType USize)) (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (usizeasstep_Step_spec_attrs))
     <TY> (int USize) <INST!>).(step_Step_forward_checked_spec)   <MERGE!>.

Definition trait_incl_of_traits_iterator_Iterator_position_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; ulft2; ulft4]) : 3 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>)))).

Definition type_of_traits_iterator_Iterator_position_closure0 (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) :=
  fn(∀ ( *[ulft1; ulft2; ulft4]) : 3 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([(Self_rt, Self_st); (F_rt, F_st); (traits_iterator_Iterator_Self_Item_rt, traits_iterator_Iterator_Self_Item_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (capture_f_, capture_acc_, _γf, _γacc, __γclos, pclos, _arg_0, x) : (((RT_xt ((F_rt))) * (RT_xt (Z)) * gname * gname * gname * _ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft1); (ϝ, ulft2); (ϝ, ulft4)]);
      (* args......... *) (( *[(((capture_f_), _γf)); (((capture_acc_), _γacc))]), __γclos) :@: (mut_ref ulft4 (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <TY> (mut_ref ulft2 (int USize)) <INST!>)), _arg_0 :@: unit_t, x :@: traits_iterator_Iterator_Self_Item_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_Pre) π pclos capture_f_ *[x])) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (capture_f__new, capture_acc__new, res, ret) : (((RT_xt ((F_rt))) * (RT_xt (Z)) * _ * _)), ret @ (ControlFlow_ty (Z) (unit)  <TY> (int USize) <TY> unit_t <INST!>);
      (* postcondition *) (λ π : thread_id, (gvar_pobs __γclos ($#@{(((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))}  *[((capture_f__new), _γf); ((capture_acc__new), _γacc)]))
      ∗ (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs.(FnOnce_PostMut) π pclos capture_f_ *[x] capture_f__new res)
      ∗ (⌜(if_Ok ret (λ ret, res = false ∧ capture_acc__new = 1+capture_acc_))%Z⌝)
      ∗ (⌜(if_Err ret (λ ret, res = true ∧ ret = capture_acc_ ∧ capture_acc__new = capture_acc_))%Z⌝)).


Definition traits_iterator_Iterator_all_closure0_call_once_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>)))).

Definition traits_iterator_Iterator_all_closure0_call_once_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnOnce_base_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))) (((tuple1_sls (PtrSynType)) : syn_type)) (((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) ((traits_iterator_Iterator_all_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (unit) (unit)  <TY> unit_t <TY> unit_t <INST!>) <INST!>).(FnOnce_call_once_spec)   <MERGE!>.

Definition traits_iterator_Iterator_all_closure0_call_mut_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; _ref_lft]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>)))).

Definition traits_iterator_Iterator_all_closure0_call_mut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnMut_base_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))) (((tuple1_sls (PtrSynType)) : syn_type)) (((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) ((traits_iterator_Iterator_all_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((traits_iterator_Iterator_all_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (unit) (unit)  <TY> unit_t <TY> unit_t <INST!>) <INST!>).(FnMut_call_mut_spec)   <MERGE!>.

Definition traits_iterator_Iterator_max_closure0_call_once_trait_req_incl (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>)))).

Definition traits_iterator_Iterator_max_closure0_call_once_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnOnce_base_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (UnitSynType) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) ((Ordering_els : syn_type)) ((traits_iterator_Iterator_max_closure0_FnOnce_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>).(FnOnce_call_once_spec)   <MERGE!>.

Definition traits_iterator_Iterator_max_closure0_call_mut_trait_req_incl (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2; _ref_lft]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>)))).

Definition traits_iterator_Iterator_max_closure0_call_mut_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnMut_base_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (UnitSynType) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) ((Ordering_els : syn_type)) ((traits_iterator_Iterator_max_closure0_FnOnce_spec_attrs ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((traits_iterator_Iterator_max_closure0_FnMut_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>).(FnMut_call_mut_spec)   <MERGE!>.

Definition traits_iterator_Iterator_max_by_closure0_call_once_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).

Definition traits_iterator_Iterator_max_by_closure0_call_once_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnOnce_base_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (((tuple1_sls (PtrSynType)) : syn_type)) (((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (traits_iterator_Iterator_Self_Item_st) ((traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>).(FnOnce_call_once_spec)   <MERGE!>.

Definition traits_iterator_Iterator_max_by_closure0_call_mut_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; _ref_lft]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).

Definition traits_iterator_Iterator_max_by_closure0_call_mut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnMut_base_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (((tuple1_sls (PtrSynType)) : syn_type)) (((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (traits_iterator_Iterator_Self_Item_st) ((traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))) ((traits_iterator_Iterator_max_by_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>).(FnMut_call_mut_spec)   <MERGE!>.

Definition traits_iterator_Iterator_min_closure0_call_once_trait_req_incl (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>)))).

Definition traits_iterator_Iterator_min_closure0_call_once_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnOnce_base_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (UnitSynType) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) ((Ordering_els : syn_type)) ((traits_iterator_Iterator_min_closure0_FnOnce_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>).(FnOnce_call_once_spec)   <MERGE!>.

Definition traits_iterator_Iterator_min_closure0_call_mut_trait_req_incl (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Eq_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Eq_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt)))) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (Ord_spec (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2; _ref_lft]) : 3 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Eq_spec_incl Eq_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Eq_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl Ord_spec_incl Ord_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Ord_base_spec (traits_iterator_Iterator_Self_Item_rt) traits_iterator_Iterator_Self_Item_st PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> traits_iterator_Iterator_Self_Item_ty <INST!>)))).

Definition traits_iterator_Iterator_min_closure0_call_mut_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnMut_base_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))) (UnitSynType) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) ((Ordering_els : syn_type)) ((traits_iterator_Iterator_min_closure0_FnOnce_spec_attrs ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((traits_iterator_Iterator_min_closure0_FnMut_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>).(FnMut_call_mut_spec)   <MERGE!>.

Definition traits_iterator_Iterator_min_by_closure0_call_once_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).

Definition traits_iterator_Iterator_min_by_closure0_call_once_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnOnce_base_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (((tuple1_sls (PtrSynType)) : syn_type)) (((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (traits_iterator_Iterator_Self_Item_st) ((traits_iterator_Iterator_min_by_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>).(FnOnce_call_once_spec)   <MERGE!>.

Definition traits_iterator_Iterator_min_by_closure0_call_mut_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec: (spec_with 2 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt)))))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; _ref_lft]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec (spec! ( *[_lft_for_1; _lft_for_0]) : 2 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) F_st ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref _lft_for_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref _lft_for_0 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>)))).

Definition traits_iterator_Iterator_min_by_closure0_call_mut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) :=
  spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnMut_base_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)) (((tuple1_sls (PtrSynType)) : syn_type)) (((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (traits_iterator_Iterator_Self_Item_st) ((traits_iterator_Iterator_min_by_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))) ((traits_iterator_Iterator_min_by_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>).(FnMut_call_mut_spec)   <MERGE!>.

Definition traits_iterator_Iterator_position_closure0_call_once_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>)))).

Definition traits_iterator_Iterator_position_closure0_call_once_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) :=
  spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnOnce_base_spec ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) (((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) ((traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <TY> (mut_ref ulft2 (int USize)) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (Z) (unit)  <TY> (int USize) <TY> unit_t <INST!>) <INST!>).(FnOnce_call_once_spec)   <MERGE!>.

Definition traits_iterator_Iterator_position_closure0_call_mut_trait_req_incl (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec: (spec_with 0 [] (traits_iterator_Iterator_spec (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt)))) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft1; ulft2; _ref_lft]) : 3 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl traits_iterator_Iterator_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_Iterator_base_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) Self_st traits_iterator_Iterator_Self_Item_st traits_iterator_Iterator_Self_spec_attrs<TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_Selfastraits_iterator_Iterator_Item_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool F_st ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) BoolSynType FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs<TY> F_ty <TY> (tuple1_ty ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> bool_t <INST!>)))).

Definition traits_iterator_Iterator_position_closure0_call_mut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) :=
  spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT),((FnMut_base_spec ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))) (((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) (((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) (((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) ((traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))) ((traits_iterator_Iterator_position_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))))
     <TY> (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <TY> (mut_ref ulft2 (int USize)) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (Z) (unit)  <TY> (int USize) <TY> unit_t <INST!>) <INST!>).(FnMut_call_mut_spec)   <MERGE!>.


End specs.
Section Iastraits_iterator_IntoIterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition Iastraits_iterator_IntoIterator_spec (I_rt: RT) (traits_iterator_Iterator_I_Item_rt: RT) (I_st: syn_type) (traits_iterator_Iterator_I_Item_st: syn_type) (traits_iterator_Iterator_I_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt) )) : (spec_with _ _ (traits_iterator_IntoIterator_spec ((I_rt)) ((I_rt)) ((traits_iterator_Iterator_I_Item_rt)))) :=
    spec! ( *[]) : 0 | ( *[I_ty; traits_iterator_Iterator_I_Item_ty]) : ([I_rt; traits_iterator_Iterator_I_Item_rt] : list RT), let Item_rt := (traits_iterator_Iterator_I_Item_rt) in let IntoIter_rt := (I_rt) in {|
        traits_iterator_IntoIterator_into_iter_spec  :=
          (type_of_Iastraits_iterator_IntoIterator_into_iter ((I_rt)) ((traits_iterator_Iterator_I_Item_rt)) (I_st) (traits_iterator_Iterator_I_Item_st)) traits_iterator_Iterator_I_spec_attrs 
             <TY> I_ty <TY> traits_iterator_Iterator_I_Item_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition Iastraits_iterator_IntoIterator_spec_subsumption  :=
    ∀ `(I_rt : !RT) `(traits_iterator_Iterator_I_Item_rt : !RT) `(I_st : !syn_type) `(traits_iterator_Iterator_I_Item_st : !syn_type) `(traits_iterator_Iterator_I_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_Iterator_I_Item_rt) )), trait_incl_marker (lift_trait_incl traits_iterator_IntoIterator_spec_incl (spec! ( *[]) : 0 | ( *[I_ty; traits_iterator_Iterator_I_Item_ty]) : ([I_rt; traits_iterator_Iterator_I_Item_rt] : list RT), (Iastraits_iterator_IntoIterator_spec (I_rt) (traits_iterator_Iterator_I_Item_rt) (I_st) (traits_iterator_Iterator_I_Item_st) (traits_iterator_Iterator_I_spec_attrs)) <TY> I_ty <TY> traits_iterator_Iterator_I_Item_ty <INST!>) (spec! ( *[]) : 0 | ( *[I_ty; traits_iterator_Iterator_I_Item_ty]) : ([I_rt; traits_iterator_Iterator_I_Item_rt] : list RT), (traits_iterator_IntoIterator_base_spec (I_rt) (I_rt) (traits_iterator_Iterator_I_Item_rt) I_st I_st traits_iterator_Iterator_I_Item_st (Iastraits_iterator_IntoIterator_spec_attrs (I_rt) (traits_iterator_Iterator_I_Item_rt) (traits_iterator_Iterator_I_spec_attrs))<TY> I_ty <TY> I_ty <TY> traits_iterator_Iterator_I_Item_ty <INST!>))).
End Iastraits_iterator_IntoIterator_spec.

Section adapters_map_MapMIMFastraits_iterator_Iterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition adapters_map_MapMIMFastraits_iterator_Iterator_spec (MB_rt: RT) (MI_rt: RT) (MF_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MB_st: syn_type) (MI_st: syn_type) (MF_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) : (spec_with _ _ (traits_iterator_Iterator_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)))) :=
    spec! ( *[]) : 0 | ( *[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MI_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), let Item_rt := (MB_rt) in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_all_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((B_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (B_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((B_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (B_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((B_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (B_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_adapters_map_MapMIMFastraits_iterator_Iterator_next ((MB_rt)) ((MI_rt)) ((MF_rt)) ((traits_iterator_Iterator_MI_Item_rt)) (MB_st) (MI_st) (MF_st) (traits_iterator_Iterator_MI_Item_st)) traits_iterator_Iterator_MI_spec_attrs FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs 
             <TY> MB_ty <TY> MI_ty <TY> MF_ty <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) 
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_position_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((F_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (F_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) 
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) 
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt))))) ((MB_rt)) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) ((adapters_map_Map_st (MI_st) (MF_st))) (MB_st) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition adapters_map_MapMIMFastraits_iterator_Iterator_spec_subsumption  :=
    ∀ `(MB_rt : !RT) `(MI_rt : !RT) `(MF_rt : !RT) `(traits_iterator_Iterator_MI_Item_rt : !RT) `(MB_st : !syn_type) `(MI_st : !syn_type) `(MF_st : !syn_type) `(traits_iterator_Iterator_MI_Item_st : !syn_type) `(traits_iterator_Iterator_MI_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) `(FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )) `(FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (MF_rt) (((tuple1_rt) ((traits_iterator_Iterator_MI_Item_rt)))) (MB_rt) )), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[]) : 0 | ( *[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MI_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), (adapters_map_MapMIMFastraits_iterator_Iterator_spec (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (MB_st) (MI_st) (MF_st) (traits_iterator_Iterator_MI_Item_st) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs)) <TY> MB_ty <TY> MI_ty <TY> MF_ty <TY> traits_iterator_Iterator_MI_Item_ty <INST!>) (spec! ( *[]) : 0 | ( *[MB_ty; MI_ty; MF_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MB_rt; MI_rt; MF_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), (traits_iterator_Iterator_base_spec ((adapters_map_Map_inv_t_rt ((MI_rt)) ((MF_rt)))) (MB_rt) (adapters_map_Map_st (MI_st) (MF_st)) MB_st (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs (MB_rt) (MI_rt) (MF_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs) (FnOnce_MF_MIastraits_iterator_Iterator_Item_spec_attrs) (FnMut_MF_MIastraits_iterator_Iterator_Item_spec_attrs))<TY> (adapters_map_Map_inv_t ((MI_rt)) ((MF_rt))   <TY> MI_ty <TY> MF_ty <INST!>) <TY> MB_ty <INST!>))).
End adapters_map_MapMIMFastraits_iterator_Iterator_spec.

Section adapters_skip_SkipMIastraits_iterator_Iterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition adapters_skip_SkipMIastraits_iterator_Iterator_spec (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) : (spec_with _ _ (traits_iterator_Iterator_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)))) :=
    spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), let Item_rt := (traits_iterator_Iterator_MI_Item_rt) in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_all_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_adapters_skip_SkipMIastraits_iterator_Iterator_next ((MI_rt)) ((traits_iterator_Iterator_MI_Item_rt)) (MI_st) (traits_iterator_Iterator_MI_Item_st)) traits_iterator_Iterator_MI_spec_attrs 
             <TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) 
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_position_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) 
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) 
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((adapters_skip_Skip_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) ((adapters_skip_Skip_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition adapters_skip_SkipMIastraits_iterator_Iterator_spec_subsumption  :=
    ∀ `(MI_rt : !RT) `(traits_iterator_Iterator_MI_Item_rt : !RT) `(MI_st : !syn_type) `(traits_iterator_Iterator_MI_Item_st : !syn_type) `(traits_iterator_Iterator_MI_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), (adapters_skip_SkipMIastraits_iterator_Iterator_spec (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (MI_st) (traits_iterator_Iterator_MI_Item_st) (traits_iterator_Iterator_MI_spec_attrs)) <TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <INST!>) (spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), (traits_iterator_Iterator_base_spec ((adapters_skip_Skip_inv_t_rt ((MI_rt)))) (traits_iterator_Iterator_MI_Item_rt) (adapters_skip_Skip_st (MI_st)) traits_iterator_Iterator_MI_Item_st (adapters_skip_SkipMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs))<TY> (adapters_skip_Skip_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty <INST!>))).
End adapters_skip_SkipMIastraits_iterator_Iterator_spec.

Section adapters_take_TakeMIastraits_iterator_Iterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition adapters_take_TakeMIastraits_iterator_Iterator_spec (MI_rt: RT) (traits_iterator_Iterator_MI_Item_rt: RT) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) (traits_iterator_Iterator_MI_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )) : (spec_with _ _ (traits_iterator_Iterator_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)))) :=
    spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), let Item_rt := (traits_iterator_Iterator_MI_Item_rt) in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_all_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_adapters_take_TakeMIastraits_iterator_Iterator_next ((MI_rt)) ((traits_iterator_Iterator_MI_Item_rt)) (MI_st) (traits_iterator_Iterator_MI_Item_st)) traits_iterator_Iterator_MI_spec_attrs 
             <TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) 
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_position_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((F_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (F_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) 
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) 
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((adapters_take_Take_inv_t_rt ((MI_rt))))) ((traits_iterator_Iterator_MI_Item_rt)) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) ((adapters_take_Take_st (MI_st))) (traits_iterator_Iterator_MI_Item_st) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition adapters_take_TakeMIastraits_iterator_Iterator_spec_subsumption  :=
    ∀ `(MI_rt : !RT) `(traits_iterator_Iterator_MI_Item_rt : !RT) `(MI_st : !syn_type) `(traits_iterator_Iterator_MI_Item_st : !syn_type) `(traits_iterator_Iterator_MI_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (MI_rt) (traits_iterator_Iterator_MI_Item_rt) )), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), (adapters_take_TakeMIastraits_iterator_Iterator_spec (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (MI_st) (traits_iterator_Iterator_MI_Item_st) (traits_iterator_Iterator_MI_spec_attrs)) <TY> MI_ty <TY> traits_iterator_Iterator_MI_Item_ty <INST!>) (spec! ( *[]) : 0 | ( *[MI_ty; traits_iterator_Iterator_MI_Item_ty]) : ([MI_rt; traits_iterator_Iterator_MI_Item_rt] : list RT), (traits_iterator_Iterator_base_spec ((adapters_take_Take_inv_t_rt ((MI_rt)))) (traits_iterator_Iterator_MI_Item_rt) (adapters_take_Take_st (MI_st)) traits_iterator_Iterator_MI_Item_st (adapters_take_TakeMIastraits_iterator_Iterator_spec_attrs (MI_rt) (traits_iterator_Iterator_MI_Item_rt) (traits_iterator_Iterator_MI_spec_attrs))<TY> (adapters_take_Take_inv_t ((MI_rt))   <TY> MI_ty <INST!>) <TY> traits_iterator_Iterator_MI_Item_ty <INST!>))).
End adapters_take_TakeMIastraits_iterator_Iterator_spec.

Section i128asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType I128))) i128asClone_spec_attrs i128asPartialEq_spec_attrs i128asPartialOrd_spec_attrs i128asstep_Step_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_i128asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType I128))) i128asClone_spec_attrs i128asPartialEq_spec_attrs i128asPartialOrd_spec_attrs i128asstep_Step_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType I128))) i128asClone_spec_attrs i128asPartialEq_spec_attrs i128asPartialOrd_spec_attrs i128asstep_Step_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_i128asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType I128))) i128asClone_spec_attrs i128asPartialEq_spec_attrs i128asPartialOrd_spec_attrs i128asstep_Step_spec_attrs 
             <TY> (int I128) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_i128asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i128asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType I128) i128asClone_spec_attrs i128asPartialEq_spec_attrs i128asPartialOrd_spec_attrs i128asstep_Step_spec_attrs<TY> (int I128) <INST!>))).
End i128asstep_Step_spec.

Section i128asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition i128asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType I128) i128asClone_spec_attrs i128asPartialEq_spec_attrs i128asPartialOrd_spec_attrs i128asCopy_spec_attrs i128asstep_Step_spec_attrs i128asstep_TrustedStep_spec_attrs<TY> (int I128) <INST!>))).
End i128asstep_TrustedStep_spec.

Section i16asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType I16))) i16asClone_spec_attrs i16asPartialEq_spec_attrs i16asPartialOrd_spec_attrs i16asstep_Step_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_i16asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType I16))) i16asClone_spec_attrs i16asPartialEq_spec_attrs i16asPartialOrd_spec_attrs i16asstep_Step_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType I16))) i16asClone_spec_attrs i16asPartialEq_spec_attrs i16asPartialOrd_spec_attrs i16asstep_Step_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_i16asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType I16))) i16asClone_spec_attrs i16asPartialEq_spec_attrs i16asPartialOrd_spec_attrs i16asstep_Step_spec_attrs 
             <TY> (int I16) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_i16asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i16asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType I16) i16asClone_spec_attrs i16asPartialEq_spec_attrs i16asPartialOrd_spec_attrs i16asstep_Step_spec_attrs<TY> (int I16) <INST!>))).
End i16asstep_Step_spec.

Section i16asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition i16asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType I16) i16asClone_spec_attrs i16asPartialEq_spec_attrs i16asPartialOrd_spec_attrs i16asCopy_spec_attrs i16asstep_Step_spec_attrs i16asstep_TrustedStep_spec_attrs<TY> (int I16) <INST!>))).
End i16asstep_TrustedStep_spec.

Section i32asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType I32))) i32asClone_spec_attrs i32asPartialEq_spec_attrs i32asPartialOrd_spec_attrs i32asstep_Step_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_i32asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType I32))) i32asClone_spec_attrs i32asPartialEq_spec_attrs i32asPartialOrd_spec_attrs i32asstep_Step_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType I32))) i32asClone_spec_attrs i32asPartialEq_spec_attrs i32asPartialOrd_spec_attrs i32asstep_Step_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_i32asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType I32))) i32asClone_spec_attrs i32asPartialEq_spec_attrs i32asPartialOrd_spec_attrs i32asstep_Step_spec_attrs 
             <TY> (int I32) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_i32asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i32asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType I32) i32asClone_spec_attrs i32asPartialEq_spec_attrs i32asPartialOrd_spec_attrs i32asstep_Step_spec_attrs<TY> (int I32) <INST!>))).
End i32asstep_Step_spec.

Section i32asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition i32asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType I32) i32asClone_spec_attrs i32asPartialEq_spec_attrs i32asPartialOrd_spec_attrs i32asCopy_spec_attrs i32asstep_Step_spec_attrs i32asstep_TrustedStep_spec_attrs<TY> (int I32) <INST!>))).
End i32asstep_TrustedStep_spec.

Section i64asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType I64))) i64asClone_spec_attrs i64asPartialEq_spec_attrs i64asPartialOrd_spec_attrs i64asstep_Step_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_i64asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType I64))) i64asClone_spec_attrs i64asPartialEq_spec_attrs i64asPartialOrd_spec_attrs i64asstep_Step_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType I64))) i64asClone_spec_attrs i64asPartialEq_spec_attrs i64asPartialOrd_spec_attrs i64asstep_Step_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_i64asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType I64))) i64asClone_spec_attrs i64asPartialEq_spec_attrs i64asPartialOrd_spec_attrs i64asstep_Step_spec_attrs 
             <TY> (int I64) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_i64asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i64asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType I64) i64asClone_spec_attrs i64asPartialEq_spec_attrs i64asPartialOrd_spec_attrs i64asstep_Step_spec_attrs<TY> (int I64) <INST!>))).
End i64asstep_Step_spec.

Section i64asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition i64asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType I64) i64asClone_spec_attrs i64asPartialEq_spec_attrs i64asPartialOrd_spec_attrs i64asCopy_spec_attrs i64asstep_Step_spec_attrs i64asstep_TrustedStep_spec_attrs<TY> (int I64) <INST!>))).
End i64asstep_TrustedStep_spec.

Section i8asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType I8))) i8asClone_spec_attrs i8asPartialEq_spec_attrs i8asPartialOrd_spec_attrs i8asstep_Step_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_i8asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType I8))) i8asClone_spec_attrs i8asPartialEq_spec_attrs i8asPartialOrd_spec_attrs i8asstep_Step_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType I8))) i8asClone_spec_attrs i8asPartialEq_spec_attrs i8asPartialOrd_spec_attrs i8asstep_Step_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_i8asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType I8))) i8asClone_spec_attrs i8asPartialEq_spec_attrs i8asPartialOrd_spec_attrs i8asstep_Step_spec_attrs 
             <TY> (int I8) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_i8asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i8asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType I8) i8asClone_spec_attrs i8asPartialEq_spec_attrs i8asPartialOrd_spec_attrs i8asstep_Step_spec_attrs<TY> (int I8) <INST!>))).
End i8asstep_Step_spec.

Section i8asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition i8asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType I8) i8asClone_spec_attrs i8asPartialEq_spec_attrs i8asPartialOrd_spec_attrs i8asCopy_spec_attrs i8asstep_Step_spec_attrs i8asstep_TrustedStep_spec_attrs<TY> (int I8) <INST!>))).
End i8asstep_TrustedStep_spec.

Section isizeasstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType ISize))) isizeasClone_spec_attrs isizeasPartialEq_spec_attrs isizeasPartialOrd_spec_attrs isizeasstep_Step_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_isizeasstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType ISize))) isizeasClone_spec_attrs isizeasPartialEq_spec_attrs isizeasPartialOrd_spec_attrs isizeasstep_Step_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType ISize))) isizeasClone_spec_attrs isizeasPartialEq_spec_attrs isizeasPartialOrd_spec_attrs isizeasstep_Step_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_isizeasstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType ISize))) isizeasClone_spec_attrs isizeasPartialEq_spec_attrs isizeasPartialOrd_spec_attrs isizeasstep_Step_spec_attrs 
             <TY> (int ISize) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_isizeasstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition isizeasstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType ISize) isizeasClone_spec_attrs isizeasPartialEq_spec_attrs isizeasPartialOrd_spec_attrs isizeasstep_Step_spec_attrs<TY> (int ISize) <INST!>))).
End isizeasstep_Step_spec.

Section isizeasstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition isizeasstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType ISize) isizeasClone_spec_attrs isizeasPartialEq_spec_attrs isizeasPartialOrd_spec_attrs isizeasCopy_spec_attrs isizeasstep_Step_spec_attrs isizeasstep_TrustedStep_spec_attrs<TY> (int ISize) <INST!>))).
End isizeasstep_TrustedStep_spec.

Section u128asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType U128))) u128asClone_spec_attrs u128asPartialEq_spec_attrs u128asPartialOrd_spec_attrs u128asstep_Step_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_u128asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType U128))) u128asClone_spec_attrs u128asPartialEq_spec_attrs u128asPartialOrd_spec_attrs u128asstep_Step_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType U128))) u128asClone_spec_attrs u128asPartialEq_spec_attrs u128asPartialOrd_spec_attrs u128asstep_Step_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_u128asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType U128))) u128asClone_spec_attrs u128asPartialEq_spec_attrs u128asPartialOrd_spec_attrs u128asstep_Step_spec_attrs 
             <TY> (int U128) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_u128asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u128asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType U128) u128asClone_spec_attrs u128asPartialEq_spec_attrs u128asPartialOrd_spec_attrs u128asstep_Step_spec_attrs<TY> (int U128) <INST!>))).
End u128asstep_Step_spec.

Section u128asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition u128asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType U128) u128asClone_spec_attrs u128asPartialEq_spec_attrs u128asPartialOrd_spec_attrs u128asCopy_spec_attrs u128asstep_Step_spec_attrs u128asstep_TrustedStep_spec_attrs<TY> (int U128) <INST!>))).
End u128asstep_TrustedStep_spec.

Section u16asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType U16))) u16asClone_spec_attrs u16asPartialEq_spec_attrs u16asPartialOrd_spec_attrs u16asstep_Step_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_u16asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType U16))) u16asClone_spec_attrs u16asPartialEq_spec_attrs u16asPartialOrd_spec_attrs u16asstep_Step_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType U16))) u16asClone_spec_attrs u16asPartialEq_spec_attrs u16asPartialOrd_spec_attrs u16asstep_Step_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_u16asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType U16))) u16asClone_spec_attrs u16asPartialEq_spec_attrs u16asPartialOrd_spec_attrs u16asstep_Step_spec_attrs 
             <TY> (int U16) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_u16asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u16asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType U16) u16asClone_spec_attrs u16asPartialEq_spec_attrs u16asPartialOrd_spec_attrs u16asstep_Step_spec_attrs<TY> (int U16) <INST!>))).
End u16asstep_Step_spec.

Section u16asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition u16asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType U16) u16asClone_spec_attrs u16asPartialEq_spec_attrs u16asPartialOrd_spec_attrs u16asCopy_spec_attrs u16asstep_Step_spec_attrs u16asstep_TrustedStep_spec_attrs<TY> (int U16) <INST!>))).
End u16asstep_TrustedStep_spec.

Section u32asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType U32))) u32asClone_spec_attrs u32asPartialEq_spec_attrs u32asPartialOrd_spec_attrs u32asstep_Step_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_u32asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType U32))) u32asClone_spec_attrs u32asPartialEq_spec_attrs u32asPartialOrd_spec_attrs u32asstep_Step_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType U32))) u32asClone_spec_attrs u32asPartialEq_spec_attrs u32asPartialOrd_spec_attrs u32asstep_Step_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_u32asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType U32))) u32asClone_spec_attrs u32asPartialEq_spec_attrs u32asPartialOrd_spec_attrs u32asstep_Step_spec_attrs 
             <TY> (int U32) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_u32asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u32asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType U32) u32asClone_spec_attrs u32asPartialEq_spec_attrs u32asPartialOrd_spec_attrs u32asstep_Step_spec_attrs<TY> (int U32) <INST!>))).
End u32asstep_Step_spec.

Section u32asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition u32asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType U32) u32asClone_spec_attrs u32asPartialEq_spec_attrs u32asPartialOrd_spec_attrs u32asCopy_spec_attrs u32asstep_Step_spec_attrs u32asstep_TrustedStep_spec_attrs<TY> (int U32) <INST!>))).
End u32asstep_TrustedStep_spec.

Section u64asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType U64))) u64asClone_spec_attrs u64asPartialEq_spec_attrs u64asPartialOrd_spec_attrs u64asstep_Step_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_u64asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType U64))) u64asClone_spec_attrs u64asPartialEq_spec_attrs u64asPartialOrd_spec_attrs u64asstep_Step_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType U64))) u64asClone_spec_attrs u64asPartialEq_spec_attrs u64asPartialOrd_spec_attrs u64asstep_Step_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_u64asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType U64))) u64asClone_spec_attrs u64asPartialEq_spec_attrs u64asPartialOrd_spec_attrs u64asstep_Step_spec_attrs 
             <TY> (int U64) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_u64asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u64asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType U64) u64asClone_spec_attrs u64asPartialEq_spec_attrs u64asPartialOrd_spec_attrs u64asstep_Step_spec_attrs<TY> (int U64) <INST!>))).
End u64asstep_Step_spec.

Section u64asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition u64asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType U64) u64asClone_spec_attrs u64asPartialEq_spec_attrs u64asPartialOrd_spec_attrs u64asCopy_spec_attrs u64asstep_Step_spec_attrs u64asstep_TrustedStep_spec_attrs<TY> (int U64) <INST!>))).
End u64asstep_TrustedStep_spec.

Section u8asstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType U8))) u8asClone_spec_attrs u8asPartialEq_spec_attrs u8asPartialOrd_spec_attrs u8asstep_Step_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_u8asstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType U8))) u8asClone_spec_attrs u8asPartialEq_spec_attrs u8asPartialOrd_spec_attrs u8asstep_Step_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType U8))) u8asClone_spec_attrs u8asPartialEq_spec_attrs u8asPartialOrd_spec_attrs u8asstep_Step_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_u8asstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType U8))) u8asClone_spec_attrs u8asPartialEq_spec_attrs u8asPartialOrd_spec_attrs u8asstep_Step_spec_attrs 
             <TY> (int U8) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_u8asstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u8asstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType U8) u8asClone_spec_attrs u8asPartialEq_spec_attrs u8asPartialOrd_spec_attrs u8asstep_Step_spec_attrs<TY> (int U8) <INST!>))).
End u8asstep_Step_spec.

Section u8asstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition u8asstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType U8) u8asClone_spec_attrs u8asPartialEq_spec_attrs u8asPartialOrd_spec_attrs u8asCopy_spec_attrs u8asstep_Step_spec_attrs u8asstep_TrustedStep_spec_attrs<TY> (int U8) <INST!>))).
End u8asstep_TrustedStep_spec.

Section usizeasstep_Step_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasstep_Step_spec  : (spec_with _ _ (step_Step_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        step_Step_backward_spec  :=
          (step_Step_backward_base_spec (Z) ((IntSynType USize))) usizeasClone_spec_attrs usizeasPartialEq_spec_attrs usizeasPartialOrd_spec_attrs usizeasstep_Step_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
        step_Step_backward_checked_spec  :=
          type_of_usizeasstep_Step_backward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_backward_unchecked_spec  :=
          (step_Step_backward_unchecked_base_spec (Z) ((IntSynType USize))) usizeasClone_spec_attrs usizeasPartialEq_spec_attrs usizeasPartialOrd_spec_attrs usizeasstep_Step_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
        step_Step_forward_spec  :=
          (step_Step_forward_base_spec (Z) ((IntSynType USize))) usizeasClone_spec_attrs usizeasPartialEq_spec_attrs usizeasPartialOrd_spec_attrs usizeasstep_Step_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
        step_Step_forward_checked_spec  :=
          type_of_usizeasstep_Step_forward_checked 
             : (spec_with 0 [] fn_spec);
        step_Step_forward_unchecked_spec  :=
          (step_Step_forward_unchecked_base_spec (Z) ((IntSynType USize))) usizeasClone_spec_attrs usizeasPartialEq_spec_attrs usizeasPartialOrd_spec_attrs usizeasstep_Step_spec_attrs 
             <TY> (int USize) : (spec_with 0 [] fn_spec);
        step_Step_steps_between_spec  :=
          type_of_usizeasstep_Step_steps_between 
             : (spec_with 2 [] fn_spec);
      |}
  .
  Definition usizeasstep_Step_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_Step_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasstep_Step_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_Step_base_spec Z (IntSynType USize) usizeasClone_spec_attrs usizeasPartialEq_spec_attrs usizeasPartialOrd_spec_attrs usizeasstep_Step_spec_attrs<TY> (int USize) <INST!>))).
End usizeasstep_Step_spec.

Section usizeasstep_TrustedStep_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasstep_TrustedStep_spec  : (spec_with _ _ (step_TrustedStep_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_step_TrustedStep_spec _ _ (Z)).
  Definition usizeasstep_TrustedStep_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl step_TrustedStep_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasstep_TrustedStep_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (step_TrustedStep_base_spec Z (IntSynType USize) usizeasClone_spec_attrs usizeasPartialEq_spec_attrs usizeasPartialOrd_spec_attrs usizeasCopy_spec_attrs usizeasstep_Step_spec_attrs usizeasstep_TrustedStep_spec_attrs<TY> (int USize) <INST!>))).
End usizeasstep_TrustedStep_spec.

Section step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec (A_rt: RT) (A_st: syn_type) (Clone_A_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) (PartialEq_A_A_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) (PartialOrd_A_A_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) (step_Step_A_spec_attrs: (step_Step_spec_attrs (RRGS:=RRGS) (A_rt) Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs)) : (spec_with _ _ (traits_iterator_Iterator_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)))) :=
    spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), let Item_rt := (A_rt) in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_all_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((B_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (B_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((B_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (B_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((B_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (B_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (((Range_sls (A_st)) : syn_type)) (A_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (((Range_sls (A_st)) : syn_type)) (A_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_step_impltraits_iterator_Iteratorforstd_ops_RangeA_next ((A_rt)) (A_st)) Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs step_Step_A_spec_attrs 
             <TY> A_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (((Range_sls (A_st)) : syn_type)) (A_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) 
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_position_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((F_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (F_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_ItemSelfastraits_iterator_Iterator_Item_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (((Range_sls (A_st)) : syn_type)) (A_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) 
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) (((Range_sls (A_st)) : syn_type)) (A_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) 
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((((Range_inv_t_rt)) ((A_rt))))) ((A_rt)) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) (((Range_sls (A_st)) : syn_type)) (A_st) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) FnOnce_F_BSelfastraits_iterator_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfastraits_iterator_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(A_st : !syn_type) `(Clone_A_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (A_rt) )) `(PartialEq_A_A_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) )) `(PartialOrd_A_A_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (A_rt) (A_rt) PartialEq_A_A_spec_attrs)) `(step_Step_A_spec_attrs : !(step_Step_spec_attrs (RRGS:=RRGS) (A_rt) Clone_A_spec_attrs PartialEq_A_A_spec_attrs PartialOrd_A_A_spec_attrs)), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec (A_rt) (A_st) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs)) <TY> A_ty <INST!>) (spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), (traits_iterator_Iterator_base_spec ((((Range_inv_t_rt)) ((A_rt)))) (A_rt) ((Range_sls (A_st)) : syn_type) A_st (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (A_rt) (Clone_A_spec_attrs) (PartialEq_A_A_spec_attrs) (PartialOrd_A_A_spec_attrs) (step_Step_A_spec_attrs))<TY> (Range_inv_t ((A_rt))  <TY> A_ty <INST!>) <TY> A_ty <INST!>))).
End step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec.

Section traits_iterator_Iterator_all_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_all_closure0_FnOnce_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : (spec_with _ _ (FnOnce_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))))) :=
    spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), let Output_rt := ((((ControlFlow_rt)) (unit) (unit))) in {|
        FnOnce_call_once_spec  :=
          (traits_iterator_Iterator_all_closure0_call_once_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_all_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_all_closure0_FnOnce_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <INST!>) (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnOnce_base_spec (((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type))) (((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt)))) ((((ControlFlow_rt)) (unit) (unit))) ((tuple1_sls (PtrSynType)) : syn_type) ((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type) ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type) (traits_iterator_Iterator_all_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (unit) (unit)  <TY> unit_t <TY> unit_t <INST!>) <INST!>))).
End traits_iterator_Iterator_all_closure0_FnOnce_spec.

Section traits_iterator_Iterator_all_closure0_FnMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_all_closure0_FnMut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : (spec_with _ _ (FnMut_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (unit) (unit)))))) :=
    spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (traits_iterator_Iterator_all_closure0_call_mut_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_all_closure0_FnMut_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_all_closure0_FnMut_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <INST!>) (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnMut_base_spec (((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type))) (((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt)))) ((((ControlFlow_rt)) (unit) (unit))) ((tuple1_sls (PtrSynType)) : syn_type) ((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type) ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type) (traits_iterator_Iterator_all_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_all_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (unit) (unit)  <TY> unit_t <TY> unit_t <INST!>) <INST!>))).
End traits_iterator_Iterator_all_closure0_FnMut_spec.

Section traits_iterator_Iterator_max_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_max_closure0_FnOnce_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : (spec_with _ _ (FnOnce_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), let Output_rt := (((Ordering_rt))) in {|
        FnOnce_call_once_spec  :=
          (traits_iterator_Iterator_max_closure0_call_once_spec ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (traits_iterator_Iterator_Self_Item_st)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_max_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_max_closure0_FnOnce_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (traits_iterator_Iterator_Self_Item_st) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>) (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnOnce_base_spec unit (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) UnitSynType ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) (traits_iterator_Iterator_max_closure0_FnOnce_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))).
End traits_iterator_Iterator_max_closure0_FnOnce_spec.

Section traits_iterator_Iterator_max_closure0_FnMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_max_closure0_FnMut_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : (spec_with _ _ (FnMut_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (traits_iterator_Iterator_max_closure0_call_mut_spec ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (traits_iterator_Iterator_Self_Item_st)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_max_closure0_FnMut_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_max_closure0_FnMut_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (traits_iterator_Iterator_Self_Item_st) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>) (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnMut_base_spec unit (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) UnitSynType ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) (traits_iterator_Iterator_max_closure0_FnOnce_spec_attrs ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_max_closure0_FnMut_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))).
End traits_iterator_Iterator_max_closure0_FnMut_spec.

Section traits_iterator_Iterator_max_by_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_max_by_closure0_FnOnce_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : (spec_with _ _ (FnOnce_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
    spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), let Output_rt := (traits_iterator_Iterator_Self_Item_rt) in {|
        FnOnce_call_once_spec  :=
          (traits_iterator_Iterator_max_by_closure0_call_once_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_max_by_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_max_by_closure0_FnOnce_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <INST!>) (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnOnce_base_spec (((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type))) (((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_Item_rt) ((tuple1_sls (PtrSynType)) : syn_type) ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type) traits_iterator_Iterator_Self_Item_st (traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))).
End traits_iterator_Iterator_max_by_closure0_FnOnce_spec.

Section traits_iterator_Iterator_max_by_closure0_FnMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_max_by_closure0_FnMut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : (spec_with _ _ (FnMut_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
    spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (traits_iterator_Iterator_max_by_closure0_call_mut_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_max_by_closure0_FnMut_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_max_by_closure0_FnMut_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <INST!>) (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnMut_base_spec (((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type))) (((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_Item_rt) ((tuple1_sls (PtrSynType)) : syn_type) ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type) traits_iterator_Iterator_Self_Item_st (traits_iterator_Iterator_max_by_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_max_by_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))).
End traits_iterator_Iterator_max_by_closure0_FnMut_spec.

Section traits_iterator_Iterator_min_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_min_closure0_FnOnce_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : (spec_with _ _ (FnOnce_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), let Output_rt := (((Ordering_rt))) in {|
        FnOnce_call_once_spec  :=
          (traits_iterator_Iterator_min_closure0_call_once_spec ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (traits_iterator_Iterator_Self_Item_st)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_min_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_min_closure0_FnOnce_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (traits_iterator_Iterator_Self_Item_st) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>) (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnOnce_base_spec unit (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) UnitSynType ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) (traits_iterator_Iterator_min_closure0_FnOnce_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))).
End traits_iterator_Iterator_min_closure0_FnOnce_spec.

Section traits_iterator_Iterator_min_closure0_FnMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_min_closure0_FnMut_spec (Self_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) : (spec_with _ _ (FnMut_spec (unit) ((((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))))) ((((Ordering_rt)))))) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (traits_iterator_Iterator_min_closure0_call_mut_spec ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (traits_iterator_Iterator_Self_Item_st)) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs traits_iterator_Iterator_Self_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Ord_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_min_closure0_FnMut_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialEq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(Eq_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Eq_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs : !(PartialOrd_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)) `(Ord_Selfastraits_iterator_Iterator_Item_spec_attrs : !(Ord_spec_attrs (RRGS:=RRGS) (traits_iterator_Iterator_Self_Item_rt) PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs Eq_Selfastraits_iterator_Iterator_Item_spec_attrs PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs)), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_min_closure0_FnMut_spec (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (traits_iterator_Iterator_Self_Item_st) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft_1 <LFT> ulft_2 <INST!>) (spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnMut_base_spec unit (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) UnitSynType ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) (Ordering_els : syn_type) (traits_iterator_Iterator_min_closure0_FnOnce_spec_attrs ((Self_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_min_closure0_FnMut_spec_attrs (Self_rt) (traits_iterator_Iterator_Self_Item_rt) (PartialEq_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (traits_iterator_Iterator_Self_spec_attrs) (Eq_Selfastraits_iterator_Iterator_Item_spec_attrs) (PartialOrd_Selfastraits_iterator_Iterator_Item_Selfastraits_iterator_Iterator_Item_spec_attrs) (Ord_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> unit_t <TY> (tuple2_ty ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt)))  <TY> (shr_ref ulft_1 traits_iterator_Iterator_Self_Item_ty) <TY> (shr_ref ulft_2 traits_iterator_Iterator_Self_Item_ty) <INST!>) <TY> (Ordering_ty   <INST!>) <INST!>))).
End traits_iterator_Iterator_min_closure0_FnMut_spec.

Section traits_iterator_Iterator_min_by_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_min_by_closure0_FnOnce_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : (spec_with _ _ (FnOnce_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
    spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), let Output_rt := (traits_iterator_Iterator_Self_Item_rt) in {|
        FnOnce_call_once_spec  :=
          (traits_iterator_Iterator_min_by_closure0_call_once_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_min_by_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_min_by_closure0_FnOnce_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <INST!>) (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnOnce_base_spec (((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type))) (((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_Item_rt) ((tuple1_sls (PtrSynType)) : syn_type) ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type) traits_iterator_Iterator_Self_Item_st (traits_iterator_Iterator_min_by_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))).
End traits_iterator_Iterator_min_by_closure0_FnOnce_spec.

Section traits_iterator_Iterator_min_by_closure0_FnMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_min_by_closure0_FnMut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) : (spec_with _ _ (FnMut_spec ((((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type)))) ((((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))))) ((traits_iterator_Iterator_Self_Item_rt)))) :=
    spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (traits_iterator_Iterator_min_by_closure0_call_mut_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_min_by_closure0_FnMut_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )) `(FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))) ((place_rfnRT (traits_iterator_Iterator_Self_Item_rt))))) (((Ordering_rt))) )), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_min_by_closure0_FnMut_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <INST!>) (spec! ( *[ulft1]) : 1 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnMut_base_spec (((tuple1_rt) (((place_rfnRT (F_rt)) * gname)%type))) (((tuple2_rt) ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt)))) (traits_iterator_Iterator_Self_Item_rt) ((tuple1_sls (PtrSynType)) : syn_type) ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type) traits_iterator_Iterator_Self_Item_st (traits_iterator_Iterator_min_by_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_min_by_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_REFSelfastraits_iterator_Iterator_ItemREFSelfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple1_ty (((place_rfnRT (F_rt)) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <INST!>) <TY> (tuple2_ty ((traits_iterator_Iterator_Self_Item_rt)) ((traits_iterator_Iterator_Self_Item_rt))  <TY> traits_iterator_Iterator_Self_Item_ty <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> traits_iterator_Iterator_Self_Item_ty <INST!>))).
End traits_iterator_Iterator_min_by_closure0_FnMut_spec.

Section traits_iterator_Iterator_position_closure0_FnOnce_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_position_closure0_FnOnce_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : (spec_with _ _ (FnOnce_spec ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))))) :=
    spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), let Output_rt := ((((ControlFlow_rt)) (Z) (unit))) in {|
        FnOnce_call_once_spec  :=
          (traits_iterator_Iterator_position_closure0_call_once_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <LFT> ulft2 : (spec_with 0 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_position_closure0_FnOnce_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_position_closure0_FnOnce_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <LFT> ulft2 <INST!>) (spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnOnce_base_spec (((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type))) (((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt)))) ((((ControlFlow_rt)) (Z) (unit))) ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) ((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type) ((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type) (traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <TY> (mut_ref ulft2 (int USize)) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (Z) (unit)  <TY> (int USize) <TY> unit_t <INST!>) <INST!>))).
End traits_iterator_Iterator_position_closure0_FnOnce_spec.

Section traits_iterator_Iterator_position_closure0_FnMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition traits_iterator_Iterator_position_closure0_FnMut_spec (Self_rt: RT) (F_rt: RT) (traits_iterator_Iterator_Self_Item_rt: RT) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) (traits_iterator_Iterator_Self_spec_attrs: (traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) : (spec_with _ _ (FnMut_spec ((((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)))) ((((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt))))) (((((ControlFlow_rt)) (Z) (unit)))))) :=
    spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (traits_iterator_Iterator_position_closure0_call_mut_spec ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st)) traits_iterator_Iterator_Self_spec_attrs FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs 
             <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <LFT> ulft2 : (spec_with 1 [] fn_spec);
      |}
  .
  Definition traits_iterator_Iterator_position_closure0_FnMut_spec_subsumption  :=
    ∀ `(Self_rt : !RT) `(F_rt : !RT) `(traits_iterator_Iterator_Self_Item_rt : !RT) `(Self_st : !syn_type) `(F_st : !syn_type) `(traits_iterator_Iterator_Self_Item_st : !syn_type) `(traits_iterator_Iterator_Self_spec_attrs : !(traits_iterator_Iterator_spec_attrs (RRGS:=RRGS) (Self_rt) (traits_iterator_Iterator_Self_Item_rt) )) `(FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )) `(FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((traits_iterator_Iterator_Self_Item_rt)))) bool )), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (traits_iterator_Iterator_position_closure0_FnMut_spec (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (Self_st) (F_st) (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) <TY> Self_ty <TY> F_ty <TY> traits_iterator_Iterator_Self_Item_ty <LFT> ulft1 <LFT> ulft2 <INST!>) (spec! ( *[ulft1; ulft2]) : 2 | ( *[Self_ty; F_ty; traits_iterator_Iterator_Self_Item_ty]) : ([Self_rt; F_rt; traits_iterator_Iterator_Self_Item_rt] : list RT), (FnMut_base_spec (((tuple2_rt) (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type))) (((tuple2_rt) (unit) ((traits_iterator_Iterator_Self_Item_rt)))) ((((ControlFlow_rt)) (Z) (unit))) ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) ((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type) ((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type) (traits_iterator_Iterator_position_closure0_FnOnce_spec_attrs ((Self_rt)) ((F_rt)) ((traits_iterator_Iterator_Self_Item_rt)) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs)) (traits_iterator_Iterator_position_closure0_FnMut_spec_attrs (Self_rt) (F_rt) (traits_iterator_Iterator_Self_Item_rt) (traits_iterator_Iterator_Self_spec_attrs) (FnOnce_F_Selfastraits_iterator_Iterator_Item_spec_attrs) (FnMut_F_Selfastraits_iterator_Iterator_Item_spec_attrs))<TY> (tuple2_ty (((place_rfnRT (F_rt)) * gname)%type) (((place_rfnRT Z) * gname)%type)  <TY> (mut_ref ulft1 F_ty) <TY> (mut_ref ulft2 (int USize)) <INST!>) <TY> (tuple2_ty (unit) ((traits_iterator_Iterator_Self_Item_rt))  <TY> unit_t <TY> traits_iterator_Iterator_Self_Item_ty <INST!>) <TY> (ControlFlow_ty (Z) (unit)  <TY> (int USize) <TY> unit_t <INST!>) <INST!>))).
End traits_iterator_Iterator_position_closure0_FnMut_spec.

