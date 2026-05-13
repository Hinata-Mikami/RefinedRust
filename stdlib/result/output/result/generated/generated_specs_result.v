From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.theories Require Export result.
From rrstd.result.result Require Export generated_code_result.

Record Debug_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Debug_spec_attrs {
}.
#[global] Arguments Debug_spec_attrs : clear implicits.

#[global] Arguments Debug_spec_attrs {_ _}.

#[global] Arguments mk_Debug_spec_attrs  {_} {_} {_}.


Section Error_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition Error_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t Error_sls +[]))).
Defined.

Definition Error_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (Error_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Error_ty.
#[global] Typeclasses Transparent Error_rt.
End Error_ty.
Global Arguments Error_rt : clear implicits.

Section Result_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context {T_rt : RT} {E_rt : RT}.

  Section components.
Definition Result_Ok_ty  : (spec_with 0 [(T_rt); (E_rt)] ((type (plist place_rfnRT [(T_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), ((struct_t (Result_Ok_sls ((T_ty.(ty_syn_type) (MetaNone))) ((E_ty.(ty_syn_type) (MetaNone)))) +[(T_ty)]))).
Defined.

Definition Result_Ok_rt  : RT.
Proof using T_rt E_rt .
  let __a := (normalized_rt_of_spec_ty (Result_Ok_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Result_Ok_ty.
#[global] Typeclasses Transparent Result_Ok_rt.

Definition Result_Err_ty  : (spec_with 0 [(T_rt); (E_rt)] ((type (plist place_rfnRT [(E_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), ((struct_t (Result_Err_sls ((T_ty.(ty_syn_type) (MetaNone))) ((E_ty.(ty_syn_type) (MetaNone)))) +[(E_ty)]))).
Defined.

Definition Result_Err_rt  : RT.
Proof using T_rt E_rt .
  let __a := (normalized_rt_of_spec_ty (Result_Err_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Result_Err_ty.
#[global] Typeclasses Transparent Result_Err_rt.

  Definition Result_enum_rt  :=
  λ rfn : (result (place_rfn (T_rt)) (place_rfn (E_rt))), match rfn with | (Ok (x)) => Result_Ok_rt| (Err (x)) => Result_Err_rt end.
  Definition Result_enum_ty  : (spec_with 0 [(T_rt); (E_rt)] (∀ (x: _), (type (Result_enum_rt (x))))) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), λ rfn, match rfn as x return type (Result_enum_rt x) with | (Ok (x)) => Result_Ok_ty -[] -[T_ty; E_ty]| (Err (x)) => Result_Err_ty -[] -[T_ty; E_ty] end.
  Program Definition Result_enum : spec_with 0 [T_rt; E_rt] (enum ((result (place_rfn (T_rt)) (place_rfn (E_rt))))) := spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), mk_enum
    _
    ((Result_els ((ty_syn_type T_ty MetaNone)) ((ty_syn_type E_ty MetaNone))))
    (λ rfn, Some (match rfn with | (Ok (x)) => "Ok" | (Err (x)) => "Err" end))
    (Result_enum_rt)
    (Result_enum_ty -[] -[T_ty; E_ty])
    (λ rfn, match rfn with | (Ok (x)) => *[x]| (Err (x)) => *[x] end)
    (λ variant, if (decide (variant = "Ok")) then Some $ mk_enum_tag_sem _ (Result_Ok_ty -[] -[T_ty; E_ty]) (λ '( *[x]), (Ok (x))) else if (decide (variant = "Err")) then Some $ mk_enum_tag_sem _ (Result_Err_ty -[] -[T_ty; E_ty]) (λ '( *[x]), (Err (x))) else None)
    ((ty_lfts T_ty) ++ (ty_lfts E_ty) ++ [])
    ((ty_wf_E T_ty) ++ (ty_wf_E E_ty) ++ [])
    _ _ _.
  Next Obligation. solve_inhabited. Defined.
  Next Obligation. solve_mk_enum_ty_lfts_incl. Qed.
  Next Obligation. solve_mk_enum_ty_wf_E. Qed.
  Next Obligation. solve_mk_enum_tag_consistent. Defined.

  Global Arguments Result_enum : simpl never.

  End components.
  Definition Result_ty : spec_with 0 [T_rt; E_rt] (type _) := spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), enum_t (Result_enum -[] -[T_ty; E_ty]).
  Definition Result_rt : RT.
  Proof using T_rt E_rt. let __a := normalized_rt_of_spec_ty Result_ty in exact __a. Defined.
  Global Typeclasses Transparent Result_ty.
  Global Typeclasses Transparent Result_rt.

End Result_ty.
Global Arguments Result_enum : simpl never.
Global Arguments Result_rt : clear implicits.
Global Arguments Result_ty : clear implicits.
Global Arguments Result_ty {_ _}.
Global Hint Unfold Result_ty : solve_protected_eq_db.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition ResultTEasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (E_rt: RT) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_E_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) : ((Clone_spec_attrs (((Result_rt ((T_rt)) ((E_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section Formatter_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition Formatter_ty  : (spec_with 1 [] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) (((place_rfnRT Z) * gname)%type))) : RT])))).
Proof.
  exact (spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), ((struct_t Formatter_sls +[((core_marker_PhantomData_ty (((place_rfnRT Z) * gname)%type) -[] -[(mut_ref ulft_a (int I32))]))]))).
Defined.

Definition Formatter_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (Formatter_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Formatter_ty.
#[global] Typeclasses Transparent Formatter_rt.
End Formatter_ty.
Global Arguments Formatter_rt : clear implicits.
Section Formatter_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.

  Program Definition Formatter_inv_t_inv_spec  : spec_with 1 [] (ex_inv_def (Formatter_rt)%type ((unit))%type) := spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((unit)%type : RT)),
            let '() := _ty_rfn in ⌜inner_rfn = -[#(tt)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition Formatter_inv_t  : spec_with 1 [] (type ((unit))%type) :=
    spec! ( *[ulft_a]) : 1 | ( *[]) : ([] : list RT), ex_plain_t _ _ (Formatter_inv_t_inv_spec  -[ulft_a] -[]) (Formatter_ty -[ulft_a] -[]).
Global Arguments Formatter_inv_t_inv_spec : simpl never.
Global Arguments Formatter_inv_t : simpl never.
  Global Typeclasses Transparent Formatter_inv_t.
  Definition Formatter_inv_t_rt : RT.
  Proof using  . let __a := normalized_rt_of_spec_ty Formatter_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Formatter_inv_t_rt.
End Formatter_inv_t.
Global Arguments Formatter_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition ResultTEasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (E_rt: RT) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_E_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) (Copy_T_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) (Copy_E_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (E_rt) Clone_E_spec_attrs)) : ((Copy_spec_attrs (((Result_rt ((T_rt)) ((E_rt))))) ((ResultTEasstd_clone_Clone_spec_attrs ((T_rt)) ((E_rt)) (Clone_T_spec_attrs) (Clone_E_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.

(* NOTE: variance proofs are currently not automatically generated by the frontend *)
Lemma Result_ty_weak_subtype_Ok E L {T_rt1 T_rt2 U_rt} (T_ty1 : type T_rt1) (T_ty2 : type T_rt2) (U_ty1 : type U_rt) (U_ty2 : type U_rt) r1 r2 T :
  weak_subtype E L r1 r2 T_ty1 T_ty2
    (mut_subtype E L U_ty1 U_ty2 T) ⊢
  weak_subtype E L (Ok (#r1)) (Ok (#r2)) (Result_ty T_rt1 U_rt <TY> T_ty1 <TY> U_ty1 <INST!>) (Result_ty T_rt2 U_rt <TY> T_ty2 <TY> U_ty2 <INST!>) T.
Proof.
Admitted.
Definition Result_ty_weak_subtype_Ok_inst := [instance Result_ty_weak_subtype_Ok].
Global Existing Instance Result_ty_weak_subtype_Ok_inst.

Lemma Result_ty_weak_subtype_Err E L {T_rt U_rt1 U_rt2} (T_ty1 T_ty2 : type T_rt) (U_ty1 : type U_rt1) (U_ty2 : type U_rt2) r1 r2 T :
  mut_subtype E L T_ty1 T_ty2 (weak_subtype E L r1 r2 U_ty1 U_ty2 T) ⊢
  weak_subtype E L (Err (#r1)) (Err (#r2)) (Result_ty T_rt U_rt1 <TY> T_ty1 <TY> U_ty1 <INST!>) (Result_ty T_rt U_rt2 <TY> T_ty2 <TY> U_ty2 <INST!>) T.
Proof.
Admitted.
Definition Result_ty_weak_subtype_Err_inst := [instance Result_ty_weak_subtype_Err].
Global Existing Instance Result_ty_weak_subtype_Err_inst.

End extra_specs.
Record Debug_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Debug_spec {
  Debug_fmt_spec  : (spec_with 3 [] fn_spec);
}.
#[global] Arguments Debug_spec : clear implicits.

#[global] Arguments Debug_spec {_ _}.


Section Debug.
Context `{RRGS : !refinedrustGS Σ}.
Definition Debug_spec_incl `{Self_rt : !RT} (spec1: ((Debug_spec (Self_rt)))) (spec2: ((Debug_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(Debug_fmt_spec)) (spec2.(Debug_fmt_spec)))).
Instance Debug_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Debug_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Debug_spec `{Self_rt : !RT} : (ScopeBindable ((Debug_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Debug_spec (Self_rt)))) :=
      {|
        Debug_fmt_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Debug_fmt_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Debug_spec (Self_rt)))) :=
      {|
        Debug_fmt_spec  :=
          (scope_add_elctx (E) (s.(Debug_fmt_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Debug_spec.

Definition Debug_fmt_base_spec (Self_rt: RT) (Self_st: syn_type) (Debug_Self_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_1; ulft_2; ulft_3]) : 3 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, f) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2); (ϝ, ulft_3)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), f :@: (mut_ref ulft_2 (Formatter_inv_t   -[ulft_3] -[]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (Result_ty (unit) ((Error_rt)) -[] -[unit_t; (Error_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs f.ghost (tt))).

Definition Debug_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((Debug_spec_attrs ((Self_rt))))) : (spec_with _ _ (Debug_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      Debug_fmt_spec  :=
        (Debug_fmt_base_spec ((Self_rt)) (Self_st)) _ATTRS 
           <TY> Self_ty : (spec_with 3 [] fn_spec);
    |}
.

End Debug.

Section Debug_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Debug_fmt (Self_rt: RT) (Self_st: syn_type) (Debug_Self_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Debug_Self_spec: (spec_with 0 [] (Debug_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1; ulft_2; ulft_3]) : 3 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Debug_spec_incl Debug_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Debug_base_spec (Self_rt) Self_st Debug_Self_spec_attrs-[] -[Self_ty])))).
End Debug_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_ResultTEasstd_clone_Clone_clone (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_T_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt)))) (Clone_E_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) (Clone_E_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (E_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (T_rt) T_st Clone_T_spec_attrs-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (E_rt) E_st Clone_E_spec_attrs-[] -[E_ty])))).

Definition type_of_ResultTEasstd_clone_Clone_clone (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_E_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; E_ty] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (((Result_rt ((T_rt)) ((E_rt))))) ((Result_st (T_st) (E_st))) ((ResultTEasstd_clone_Clone_spec_attrs (T_rt) (E_rt) (Clone_T_spec_attrs) (Clone_E_spec_attrs))))
    -[] -[(Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_Result_TE_map (T_rt: RT) (E_rt: RT) (U_rt: RT) (F_rt: RT) (T_st: syn_type) (E_st: syn_type) (U_st: syn_type) (F_st: syn_type) (FnOnce_F_T_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) )) (FnOnce_F_T_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty; U_ty; F_ty]) : ([T_rt; E_rt; U_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) F_st ((tuple1_sls (T_st)) : syn_type) U_st FnOnce_F_T_spec_attrs-[] -[F_ty; (tuple1_ty ((T_rt)) -[] -[T_ty]); U_ty])))).

Definition type_of_Result_TE_map (T_rt: RT) (E_rt: RT) (U_rt: RT) (F_rt: RT) (T_st: syn_type) (E_st: syn_type) (U_st: syn_type) (F_st: syn_type) (FnOnce_F_T_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((T_rt)))) (U_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; E_ty; U_ty; F_ty]) : ([(T_rt, T_st); (E_rt, E_st); (U_rt, U_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (oparam, self, op) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]), op :@: F_ty;
      (* precondition. *) (λ π : thread_id, (if_iOk self (λ self, ∃ p, ⌜oparam = Some p⌝ ∗ FnOnce_F_T_spec_attrs.(FnOnce_Pre) π p op *[self]))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (Result_ty ((U_rt)) ((E_rt)) -[] -[U_ty; E_ty]);
      (* postcondition *) (λ π : thread_id, (if_iErr self (λ self, ⌜ret = Err self⌝ ∗ ty_ghost_drop F_ty π ($# op)))
      ∗ (if_iOk self (λ self, ∃ p x, ⌜oparam = Some p⌝ ∗ ⌜ret = Ok x⌝ ∗ FnOnce_F_T_spec_attrs.(FnOnce_Post) π p op *[self] x))).

Definition trait_incl_of_Result_TE_map_err (T_rt: RT) (E_rt: RT) (F_rt: RT) (O_rt: RT) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) (O_st: syn_type) (FnOnce_O_E_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (O_rt) (((tuple1_rt) ((E_rt)))) (F_rt) )) (FnOnce_O_E_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (O_rt) (((tuple1_rt) ((E_rt)))) (F_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty; F_ty; O_ty]) : ([T_rt; E_rt; F_rt; O_rt] : list RT), ((trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_O_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (O_rt) (((tuple1_rt) ((E_rt)))) (F_rt) O_st ((tuple1_sls (E_st)) : syn_type) F_st FnOnce_O_E_spec_attrs-[] -[O_ty; (tuple1_ty ((E_rt)) -[] -[E_ty]); F_ty])))).

Definition type_of_Result_TE_map_err (T_rt: RT) (E_rt: RT) (F_rt: RT) (O_rt: RT) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) (O_st: syn_type) (FnOnce_O_E_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (O_rt) (((tuple1_rt) ((E_rt)))) (F_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; E_ty; F_ty; O_ty]) : ([(T_rt, T_st); (E_rt, E_st); (F_rt, F_st); (O_rt, O_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (oparam, self, op) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]), op :@: O_ty;
      (* precondition. *) (λ π : thread_id, (if_iErr self (λ self, ∃ p, ⌜oparam = Some p⌝ ∗ FnOnce_O_E_spec_attrs.(FnOnce_Pre) π p op *[self]))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (Result_ty ((T_rt)) ((F_rt)) -[] -[T_ty; F_ty]);
      (* postcondition *) (λ π : thread_id, (if_iOk self (λ self, ⌜ret = Ok self⌝ ∗ ty_ghost_drop O_ty π ($# op)))
      ∗ (if_iErr self (λ self, ∃ p x, ⌜oparam = Some p⌝ ∗ ⌜ret = Err x⌝ ∗ FnOnce_O_E_spec_attrs.(FnOnce_Post) π p op *[self] x))).


Definition trait_incl_of_Result_TE_is_err (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (True).

Definition type_of_Result_TE_is_err (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; E_ty]) : ([(T_rt, T_st); (E_rt, E_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) x :@: (shr_ref ulft_1 (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_Err x) @ bool_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Result_TE_is_ok (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (True).

Definition type_of_Result_TE_is_ok (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; E_ty]) : ([(T_rt, T_st); (E_rt, E_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) x :@: (shr_ref ulft_1 (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_Ok x) @ bool_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Result_TE_unwrap (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (Debug_E_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (E_rt) )) (Debug_E_spec: (spec_with 0 [] (Debug_spec (RRGS:=RRGS) (E_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), ((trait_incl_marker (lift_trait_incl Debug_spec_incl Debug_E_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Debug_base_spec (E_rt) E_st Debug_E_spec_attrs-[] -[E_ty])))).

Definition type_of_Result_TE_unwrap (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (Debug_E_spec_attrs: (Debug_spec_attrs (RRGS:=RRGS) (E_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; E_ty]) : ([(T_rt, T_st); (E_rt, E_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]);
      (* precondition. *) (λ π : thread_id, (⌜(destruct_hint self is_Ok)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ T_ty;
      (* postcondition *) (λ π : thread_id, (⌜(match self with | Ok x => ret = x | Err _ => False end)%Z⌝)).

Definition trait_incl_of_Result_TE_unwrap_unchecked (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (True).

Definition type_of_Result_TE_unwrap_unchecked (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; E_ty]) : ([(T_rt, T_st); (E_rt, E_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]);
      (* precondition. *) (λ π : thread_id, (⌜(destruct_hint self is_Ok)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ T_ty;
      (* postcondition *) (λ π : thread_id, (⌜(match self with | Ok x => ret = x | Err _ => False end)%Z⌝)).



End specs.
Section ResultTEasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition ResultTEasstd_clone_Clone_spec (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_E_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) : (spec_with _ _ (Clone_spec (((Result_rt ((T_rt)) ((E_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_ResultTEasstd_clone_Clone_clone ((T_rt)) ((E_rt)) (T_st) (E_st)) Clone_T_spec_attrs Clone_E_spec_attrs 
             <TY> T_ty <TY> E_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((Result_rt ((T_rt)) ((E_rt))))) ((Result_st (T_st) (E_st)))) (ResultTEasstd_clone_Clone_spec_attrs (T_rt) (E_rt) (Clone_T_spec_attrs) (Clone_E_spec_attrs)) 
             <TY> (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition ResultTEasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(Clone_T_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) `(Clone_E_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (E_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (ResultTEasstd_clone_Clone_spec (T_rt) (E_rt) (T_st) (E_st) (Clone_T_spec_attrs) (Clone_E_spec_attrs))-[] -[T_ty; E_ty]) (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), scope_add_typarams _ -[T_ty; E_ty] ((Clone_base_spec ((Result_rt ((T_rt)) ((E_rt)))) (Result_st (T_st) (E_st)) (ResultTEasstd_clone_Clone_spec_attrs (T_rt) (E_rt) (Clone_T_spec_attrs) (Clone_E_spec_attrs))-[] -[(Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])])))).
End ResultTEasstd_clone_Clone_spec.

Section ResultTEasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition ResultTEasstd_marker_Copy_spec (T_rt: RT) (E_rt: RT) (T_st: syn_type) (E_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_E_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) (Copy_T_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) (Copy_E_spec_attrs: (Copy_spec_attrs (RRGS:=RRGS) (E_rt) Clone_E_spec_attrs)) : (spec_with _ _ (Copy_spec (((Result_rt ((T_rt)) ((E_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (@mk_Copy_spec _ _ (((Result_rt ((T_rt)) ((E_rt)))))).
  Definition ResultTEasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(E_rt : !RT) `(T_st : !syn_type) `(E_st : !syn_type) `(Clone_T_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) `(Clone_E_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (E_rt) )) `(Copy_T_spec_attrs : !(Copy_spec_attrs (RRGS:=RRGS) (T_rt) Clone_T_spec_attrs)) `(Copy_E_spec_attrs : !(Copy_spec_attrs (RRGS:=RRGS) (E_rt) Clone_E_spec_attrs)), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), (ResultTEasstd_marker_Copy_spec (T_rt) (E_rt) (T_st) (E_st) (Clone_T_spec_attrs) (Clone_E_spec_attrs) (Copy_T_spec_attrs) (Copy_E_spec_attrs))-[] -[T_ty; E_ty]) (spec! ( *[]) : 0 | ( *[T_ty; E_ty]) : ([T_rt; E_rt] : list RT), scope_add_typarams _ -[T_ty; E_ty] ((Copy_base_spec ((Result_rt ((T_rt)) ((E_rt)))) (Result_st (T_st) (E_st)) (ResultTEasstd_clone_Clone_spec_attrs ((T_rt)) ((E_rt)) (Clone_T_spec_attrs) (Clone_E_spec_attrs)) (ResultTEasstd_marker_Copy_spec_attrs (T_rt) (E_rt) (Clone_T_spec_attrs) (Clone_E_spec_attrs) (Copy_T_spec_attrs) (Copy_E_spec_attrs))-[] -[(Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])])))).
  Lemma ResultTEasstd_marker_Copy_semantic_interp (T_rt: RT) (E_rt: RT) (T_ty: (type (T_rt))) (E_ty: (type (E_rt))) (_: (Copy_semantic_interp (T_rt) T_ty)) (_: (Copy_semantic_interp (E_rt) E_ty)) : (Copy_semantic_interp ((Result_rt ((T_rt)) ((E_rt)))) (Result_ty ((T_rt)) ((E_rt)) -[] -[T_ty; E_ty])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End ResultTEasstd_marker_Copy_spec.

