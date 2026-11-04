From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.theories Require Export closures.
From rrstd.closures.closures Require Export generated_code_closures.

Record Tuple_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Tuple_spec_attrs {
}.
#[global] Arguments Tuple_spec_attrs : clear implicits.

#[global] Arguments Tuple_spec_attrs {_ _}.

#[global] Arguments mk_Tuple_spec_attrs  {_} {_} {_}.




Record FnMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : Type := mk_FnMut_spec_attrs {
}.
#[global] Arguments FnMut_spec_attrs : clear implicits.

#[global] Arguments FnMut_spec_attrs {_ _}.

#[global] Arguments mk_FnMut_spec_attrs  {_} {_} {_} {_} {_}.


Record Fn_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : Type := mk_Fn_spec_attrs {
}.
#[global] Arguments Fn_spec_attrs : clear implicits.

#[global] Arguments Fn_spec_attrs {_ _}.

#[global] Arguments mk_Fn_spec_attrs  {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFFasFnOnceA_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : ((FnOnce_spec_attrs ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
  {|
    FnOnce_Params  :=
      (FnOnce_F_A_spec_attrs.(FnOnce_Params)) : ((FnOnce_Params_sig ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt))));
    FnOnce_Pre  :=
      (FnOnce_F_A_spec_attrs.(FnOnce_Pre)) : ((FnOnce_Pre_sig ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_)));
    FnOnce_Post  :=
      (FnOnce_F_A_spec_attrs.(FnOnce_Post)) : ((FnOnce_Post_sig ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_) (_)));
    FnOnce_PostMut  :=
      (λ π p s args s2 ret, (⌜s2 = s⌝ ∗ FnOnce_F_A_spec_attrs.(FnOnce_Post) π p s args ret)%I) : ((FnOnce_PostMut_sig ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_) (_) (_)));
    FnOnce_UnwindCondition  :=
      (FnOnce_F_A_spec_attrs.(FnOnce_UnwindCondition)) : ((FnOnce_UnwindCondition_sig ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_) (_) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFmutFasFnOnceA_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : ((FnOnce_spec_attrs (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
  {|
    FnOnce_Params  :=
      (FnOnce_F_A_spec_attrs.(FnOnce_Params)) : ((FnOnce_Params_sig (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt))));
    FnOnce_Pre  :=
      (λ π p s args, FnOnce_F_A_spec_attrs.(FnOnce_Pre) π p s.cur args) : ((FnOnce_Pre_sig (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_)));
    FnOnce_Post  :=
      (λ π p s args ret, (∃ s2, FnOnce_F_A_spec_attrs.(FnOnce_PostMut) π p s.cur args s2 ret ∗ gvar_pobs s.ghost ($# s2))%I) : ((FnOnce_Post_sig (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_) (_)));
    FnOnce_PostMut  :=
      (λ π p s args s2 ret, (FnOnce_F_A_spec_attrs.(FnOnce_PostMut) π p s.cur args s2.cur ret ∗ ⌜s.ghost = s2.ghost⌝)%I) : ((FnOnce_PostMut_sig (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_) (_) (_)));
    FnOnce_UnwindCondition  :=
      (λ s p args, FnOnce_F_A_spec_attrs.(FnOnce_UnwindCondition) s.cur p args) : ((FnOnce_UnwindCondition_sig (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)) (_) (_) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFFasFnMutA_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : ((FnMut_spec_attrs ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
  mk_FnMut_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFmutFasFnMutA_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : ((FnMut_spec_attrs (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
  mk_FnMut_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFFasFnA_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : ((Fn_spec_attrs ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
  mk_Fn_spec_attrs.


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
Definition FnOnce_default_attrs {Self_rt Args_rt Output_rt : RT} : FnOnce_spec_attrs (RRGS:=RRGS) Self_rt Args_rt Output_rt :=
  mk_FnOnce_spec_attrs unit%type (λ _ _ _ _, True%I) (λ _ _ _ _ _, True%I) (λ _ _ _ _ _ _, True%I) (λ _ _ _, False).
Definition FnMut_default_attrs {Self_rt Args_rt Output_rt : RT} :
  FnMut_spec_attrs (RRGS:=RRGS) Self_rt Args_rt Output_rt :=
  mk_FnMut_spec_attrs.
Definition Fn_default_attrs {Self_rt Args_rt Output_rt : RT} :
  Fn_spec_attrs (RRGS:=RRGS) Self_rt Args_rt Output_rt :=
  mk_Fn_spec_attrs.
End extra_specs.
Record Tuple_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Tuple_spec {
}.
#[global] Arguments Tuple_spec : clear implicits.

#[global] Arguments Tuple_spec {_ _}.


Record FnOnce_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{Output_rt : !RT} : Type := mk_FnOnce_spec {
  FnOnce_call_once_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments FnOnce_spec : clear implicits.

#[global] Arguments FnOnce_spec {_ _}.


Record FnMut_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : Type := mk_FnMut_spec {
  FnMut_call_mut_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments FnMut_spec : clear implicits.

#[global] Arguments FnMut_spec {_ _}.


Record Fn_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : Type := mk_Fn_spec {
  Fn_call_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments Fn_spec : clear implicits.

#[global] Arguments Fn_spec {_ _}.


Section Tuple.
Context `{RRGS : !refinedrustGS Σ}.
Definition Tuple_spec_incl `{Self_rt : !RT} (spec1: ((Tuple_spec (Self_rt)))) (spec2: ((Tuple_spec (Self_rt)))) : Prop :=
  True.
Instance Tuple_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Tuple_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Tuple_spec `{Self_rt : !RT} : (ScopeBindable ((Tuple_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Tuple_spec (Self_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((Tuple_spec (Self_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_Tuple_spec.

Definition Tuple_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Tuple_spec_attrs ((Self_rt))))) : (spec_with _ _ (Tuple_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Tuple_spec _ _ ((Self_rt))).
Arguments Tuple_base_spec : simpl never.


End Tuple.

Section FnOnce.
Context `{RRGS : !refinedrustGS Σ}.
Definition FnOnce_spec_incl `{Self_rt : !RT} `{Args_rt : !RT} `{Output_rt : !RT} (spec1: ((FnOnce_spec (Self_rt) (Args_rt) (Output_rt)))) (spec2: ((FnOnce_spec (Self_rt) (Args_rt) (Output_rt)))) : Prop :=
  ((function_subtype (spec1.(FnOnce_call_once_spec)) (spec2.(FnOnce_call_once_spec)))).
Instance FnOnce_spec_incl_preorder `{Self_rt : !RT} `{Args_rt : !RT} `{Output_rt : !RT} : (PreOrder (FnOnce_spec_incl (Self_rt := Self_rt) (Args_rt := Args_rt) (Output_rt := Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_FnOnce_spec `{Self_rt : !RT} `{Args_rt : !RT} `{Output_rt : !RT} : (ScopeBindable ((FnOnce_spec (Self_rt) (Args_rt) (Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((FnOnce_spec (Self_rt) (Args_rt) (Output_rt)))) :=
      {|
        FnOnce_call_once_spec  :=
          (scope_add_typarams (rts) (tys) (s.(FnOnce_call_once_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((FnOnce_spec (Self_rt) (Args_rt) (Output_rt)))) :=
      {|
        FnOnce_call_once_spec  :=
          (scope_add_elctx (E) (s.(FnOnce_call_once_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_FnOnce_spec.

Definition FnOnce_call_once_base_spec (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (Output_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty; Args_ty; Output_ty]) : ([(Self_rt, Self_st); (Args_rt, Args_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, args) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: Self_ty, args :@: Args_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_Self_Args_spec_attrs.(FnOnce_Pre) π p self args)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ Output_ty;
      (* postcondition *) (λ π : thread_id, (FnOnce_Self_Args_spec_attrs.(FnOnce_Post) π p self args ret)) |
      (* unwind cond... *) FnOnce_Self_Args_spec_attrs.(FnOnce_UnwindCondition) self p args |
      (* unwind post... *) (λ π : thread_id, True).

Definition FnOnce_base_spec (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (_ATTRS: ((FnOnce_spec_attrs ((Self_rt)) ((Args_rt)) ((Output_rt))))) : (spec_with _ _ (FnOnce_spec ((Self_rt)) ((Args_rt)) ((Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Args_ty; Output_ty]) : ([Self_rt; Args_rt; Output_rt] : list RT), {|
      FnOnce_call_once_spec  :=
        (FnOnce_call_once_base_spec ((Self_rt)) ((Args_rt)) ((Output_rt)) (Self_st) (Args_st) (Output_st)) DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Args_ty <TY> Output_ty : (spec_with 0 [] fn_spec);
    |}
.
Arguments FnOnce_base_spec : simpl never.


End FnOnce.

Section FnMut.
Context `{RRGS : !refinedrustGS Σ}.
Definition FnMut_spec_incl `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} (spec1: ((FnMut_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) (spec2: ((FnMut_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) : Prop :=
  ((function_subtype (spec1.(FnMut_call_mut_spec)) (spec2.(FnMut_call_mut_spec)))).
Instance FnMut_spec_incl_preorder `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : (PreOrder (FnMut_spec_incl (Self_rt := Self_rt) (Args_rt := Args_rt) (FnOnce_Self_Args_Output_rt := FnOnce_Self_Args_Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_FnMut_spec `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : (ScopeBindable ((FnMut_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((FnMut_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) :=
      {|
        FnMut_call_mut_spec  :=
          (scope_add_typarams (rts) (tys) (s.(FnMut_call_mut_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((FnMut_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) :=
      {|
        FnMut_call_mut_spec  :=
          (scope_add_elctx (E) (s.(FnMut_call_mut_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_FnMut_spec.

Definition FnMut_call_mut_base_spec (Self_rt: RT) (Args_rt: RT) (FnOnce_Self_Args_Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (FnOnce_Self_Args_Output_st: syn_type) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt) )) (FnMut_Self_Args_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]) : ([(Self_rt, Self_st); (Args_rt, Args_st); (FnOnce_Self_Args_Output_rt, FnOnce_Self_Args_Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, args) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), args :@: Args_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_Self_Args_spec_attrs.(FnOnce_Pre) π p self.cur args)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (m', ret) : ((_ * _)), ret @ FnOnce_Self_Args_Output_ty;
      (* postcondition *) (λ π : thread_id, (FnOnce_Self_Args_spec_attrs.(FnOnce_PostMut) π p self.cur args m' ret)
      ∗ (gvar_pobs self.ghost ($# m'))) |
      (* unwind cond... *) FnOnce_Self_Args_spec_attrs.(FnOnce_UnwindCondition) self.cur p args |
      (* unwind post... *) (λ π : thread_id, True).

Definition FnMut_base_spec (Self_rt: RT) (Args_rt: RT) (FnOnce_Self_Args_Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (FnOnce_Self_Args_Output_st: syn_type) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt) )) (_ATTRS: ((FnMut_spec_attrs ((Self_rt)) ((Args_rt)) ((FnOnce_Self_Args_Output_rt))))) : (spec_with _ _ (FnMut_spec ((Self_rt)) ((Args_rt)) ((FnOnce_Self_Args_Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]) : ([Self_rt; Args_rt; FnOnce_Self_Args_Output_rt] : list RT), {|
      FnMut_call_mut_spec  :=
        (FnMut_call_mut_base_spec ((Self_rt)) ((Args_rt)) ((FnOnce_Self_Args_Output_rt)) (Self_st) (Args_st) (FnOnce_Self_Args_Output_st)) FnOnce_Self_Args_spec_attrs DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Args_ty <TY> FnOnce_Self_Args_Output_ty : (spec_with 1 [] fn_spec);
    |}
.
Arguments FnMut_base_spec : simpl never.


End FnMut.

Section Fn.
Context `{RRGS : !refinedrustGS Σ}.
Definition Fn_spec_incl `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} (spec1: ((Fn_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) (spec2: ((Fn_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) : Prop :=
  ((function_subtype (spec1.(Fn_call_spec)) (spec2.(Fn_call_spec)))).
Instance Fn_spec_incl_preorder `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : (PreOrder (Fn_spec_incl (Self_rt := Self_rt) (Args_rt := Args_rt) (FnOnce_Self_Args_Output_rt := FnOnce_Self_Args_Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Fn_spec `{Self_rt : !RT} `{Args_rt : !RT} `{FnOnce_Self_Args_Output_rt : !RT} : (ScopeBindable ((Fn_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Fn_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) :=
      {|
        Fn_call_spec  :=
          (scope_add_typarams (rts) (tys) (s.(Fn_call_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((Fn_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt)))) :=
      {|
        Fn_call_spec  :=
          (scope_add_elctx (E) (s.(Fn_call_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_Fn_spec.

Definition Fn_call_base_spec (Self_rt: RT) (Args_rt: RT) (FnOnce_Self_Args_Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (FnOnce_Self_Args_Output_st: syn_type) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (FnMut_Self_Args_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt) )) (Fn_Self_Args_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]) : ([(Self_rt, Self_st); (Args_rt, Args_st); (FnOnce_Self_Args_Output_rt, FnOnce_Self_Args_Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, args) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty), args :@: Args_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_Self_Args_spec_attrs.(FnOnce_Pre) π p self args)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ FnOnce_Self_Args_Output_ty;
      (* postcondition *) (λ π : thread_id, (FnOnce_Self_Args_spec_attrs.(FnOnce_Post) π p self args ret)) |
      (* unwind cond... *) FnOnce_Self_Args_spec_attrs.(FnOnce_UnwindCondition) self p args |
      (* unwind post... *) (λ π : thread_id, True).

Definition Fn_base_spec (Self_rt: RT) (Args_rt: RT) (FnOnce_Self_Args_Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (FnOnce_Self_Args_Output_st: syn_type) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (FnMut_Self_Args_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt) )) (_ATTRS: ((Fn_spec_attrs ((Self_rt)) ((Args_rt)) ((FnOnce_Self_Args_Output_rt))))) : (spec_with _ _ (Fn_spec ((Self_rt)) ((Args_rt)) ((FnOnce_Self_Args_Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]) : ([Self_rt; Args_rt; FnOnce_Self_Args_Output_rt] : list RT), {|
      Fn_call_spec  :=
        (Fn_call_base_spec ((Self_rt)) ((Args_rt)) ((FnOnce_Self_Args_Output_rt)) (Self_st) (Args_st) (FnOnce_Self_Args_Output_st)) FnOnce_Self_Args_spec_attrs FnMut_Self_Args_spec_attrs DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs _ATTRS 
           <TY> Self_ty <TY> Args_ty <TY> FnOnce_Self_Args_Output_ty : (spec_with 1 [] fn_spec);
    |}
.
Arguments Fn_base_spec : simpl never.


End Fn.

Section Tuple_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Tuple_trait_req_incls.

Section FnOnce_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_FnOnce_call_once (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (Output_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_Args_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Args_rt))))) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Output_rt) )) (DropGlue_SelfasFnOnceArgs_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Output_rt))))) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (Output_rt) )) (FnOnce_Self_Args_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (Self_rt) (Args_rt) (Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[]) : 0 | ( *[Self_ty; Args_ty; Output_ty]) : ([Self_rt; Args_rt; Output_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Args_lfts_inst : prod_vec lft DropGlue_Args_realization.(trait_ctx_lfts)) (DropGlue_Args_tys_inst : plist type DropGlue_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Args_realization.(trait_ctx_spec) DropGlue_Args_lfts_inst DropGlue_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Args_rt) Args_st DropGlue_Args_spec_attrs-[] -[Args_ty]))⌝ ∗ DropGlue_Args_realization.(trait_ctx_wf) DropGlue_Args_lfts_inst DropGlue_Args_tys_inst π)
      ∗ (∃ (DropGlue_SelfasFnOnceArgs_Output_lfts_inst : prod_vec lft DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_lfts)) (DropGlue_SelfasFnOnceArgs_Output_tys_inst : plist type DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_spec) DropGlue_SelfasFnOnceArgs_Output_lfts_inst DropGlue_SelfasFnOnceArgs_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Output_rt) Output_st DropGlue_SelfasFnOnceArgs_Output_spec_attrs-[] -[Output_ty]))⌝ ∗ DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_wf) DropGlue_SelfasFnOnceArgs_Output_lfts_inst DropGlue_SelfasFnOnceArgs_Output_tys_inst π)
      ∗ (∃ (FnOnce_Self_Args_lfts_inst : prod_vec lft FnOnce_Self_Args_realization.(trait_ctx_lfts)) (FnOnce_Self_Args_tys_inst : plist type FnOnce_Self_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_Self_Args_realization.(trait_ctx_spec) FnOnce_Self_Args_lfts_inst FnOnce_Self_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (Self_rt) (Args_rt) (Output_rt) Self_st Args_st Output_st DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs FnOnce_Self_Args_spec_attrs-[] -[Self_ty; Args_ty; Output_ty]))⌝ ∗ FnOnce_Self_Args_realization.(trait_ctx_wf) FnOnce_Self_Args_lfts_inst FnOnce_Self_Args_tys_inst π))%I).
End FnOnce_trait_req_incls.

Section FnMut_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_FnMut_call_mut (Self_rt: RT) (Args_rt: RT) (FnOnce_Self_Args_Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (FnOnce_Self_Args_Output_st: syn_type) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (FnOnce_Self_Args_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_Args_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Args_rt))))) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt) )) (DropGlue_SelfasFnOnceArgs_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt))))) (FnMut_Self_Args_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (FnMut_Self_Args_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]) : ([Self_rt; Args_rt; FnOnce_Self_Args_Output_rt] : list RT), (λ π, ((∃ (FnOnce_Self_Args_lfts_inst : prod_vec lft FnOnce_Self_Args_realization.(trait_ctx_lfts)) (FnOnce_Self_Args_tys_inst : plist type FnOnce_Self_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_Self_Args_realization.(trait_ctx_spec) FnOnce_Self_Args_lfts_inst FnOnce_Self_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) Self_st Args_st FnOnce_Self_Args_Output_st DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs FnOnce_Self_Args_spec_attrs-[] -[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]))⌝ ∗ FnOnce_Self_Args_realization.(trait_ctx_wf) FnOnce_Self_Args_lfts_inst FnOnce_Self_Args_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Args_lfts_inst : prod_vec lft DropGlue_Args_realization.(trait_ctx_lfts)) (DropGlue_Args_tys_inst : plist type DropGlue_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Args_realization.(trait_ctx_spec) DropGlue_Args_lfts_inst DropGlue_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Args_rt) Args_st DropGlue_Args_spec_attrs-[] -[Args_ty]))⌝ ∗ DropGlue_Args_realization.(trait_ctx_wf) DropGlue_Args_lfts_inst DropGlue_Args_tys_inst π)
      ∗ (∃ (DropGlue_SelfasFnOnceArgs_Output_lfts_inst : prod_vec lft DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_lfts)) (DropGlue_SelfasFnOnceArgs_Output_tys_inst : plist type DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_spec) DropGlue_SelfasFnOnceArgs_Output_lfts_inst DropGlue_SelfasFnOnceArgs_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_Self_Args_Output_rt) FnOnce_Self_Args_Output_st DropGlue_SelfasFnOnceArgs_Output_spec_attrs-[] -[FnOnce_Self_Args_Output_ty]))⌝ ∗ DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_wf) DropGlue_SelfasFnOnceArgs_Output_lfts_inst DropGlue_SelfasFnOnceArgs_Output_tys_inst π)
      ∗ (∃ (FnMut_Self_Args_lfts_inst : prod_vec lft FnMut_Self_Args_realization.(trait_ctx_lfts)) (FnMut_Self_Args_tys_inst : plist type FnMut_Self_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_Self_Args_realization.(trait_ctx_spec) FnMut_Self_Args_lfts_inst FnMut_Self_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) Self_st Args_st FnOnce_Self_Args_Output_st FnOnce_Self_Args_spec_attrs DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs FnMut_Self_Args_spec_attrs-[] -[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]))⌝ ∗ FnMut_Self_Args_realization.(trait_ctx_wf) FnMut_Self_Args_lfts_inst FnMut_Self_Args_tys_inst π))%I).
End FnMut_trait_req_incls.

Section Fn_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Fn_call (Self_rt: RT) (Args_rt: RT) (FnOnce_Self_Args_Output_rt: RT) (Self_st: syn_type) (Args_st: syn_type) (FnOnce_Self_Args_Output_st: syn_type) (FnOnce_Self_Args_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (FnOnce_Self_Args_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt))))) (FnMut_Self_Args_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (FnMut_Self_Args_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt))))) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (DropGlue_Args_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Args_rt) )) (DropGlue_Args_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Args_rt))))) (DropGlue_SelfasFnOnceArgs_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt) )) (DropGlue_SelfasFnOnceArgs_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_Self_Args_Output_rt))))) (Fn_Self_Args_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) )) (Fn_Self_Args_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]) : ([Self_rt; Args_rt; FnOnce_Self_Args_Output_rt] : list RT), (λ π, ((∃ (FnOnce_Self_Args_lfts_inst : prod_vec lft FnOnce_Self_Args_realization.(trait_ctx_lfts)) (FnOnce_Self_Args_tys_inst : plist type FnOnce_Self_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_Self_Args_realization.(trait_ctx_spec) FnOnce_Self_Args_lfts_inst FnOnce_Self_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) Self_st Args_st FnOnce_Self_Args_Output_st DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs FnOnce_Self_Args_spec_attrs-[] -[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]))⌝ ∗ FnOnce_Self_Args_realization.(trait_ctx_wf) FnOnce_Self_Args_lfts_inst FnOnce_Self_Args_tys_inst π)
      ∗ (∃ (FnMut_Self_Args_lfts_inst : prod_vec lft FnMut_Self_Args_realization.(trait_ctx_lfts)) (FnMut_Self_Args_tys_inst : plist type FnMut_Self_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_Self_Args_realization.(trait_ctx_spec) FnMut_Self_Args_lfts_inst FnMut_Self_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) Self_st Args_st FnOnce_Self_Args_Output_st FnOnce_Self_Args_spec_attrs DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs FnMut_Self_Args_spec_attrs-[] -[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]))⌝ ∗ FnMut_Self_Args_realization.(trait_ctx_wf) FnMut_Self_Args_lfts_inst FnMut_Self_Args_tys_inst π)
      ∗ (∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (DropGlue_Args_lfts_inst : prod_vec lft DropGlue_Args_realization.(trait_ctx_lfts)) (DropGlue_Args_tys_inst : plist type DropGlue_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Args_realization.(trait_ctx_spec) DropGlue_Args_lfts_inst DropGlue_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Args_rt) Args_st DropGlue_Args_spec_attrs-[] -[Args_ty]))⌝ ∗ DropGlue_Args_realization.(trait_ctx_wf) DropGlue_Args_lfts_inst DropGlue_Args_tys_inst π)
      ∗ (∃ (DropGlue_SelfasFnOnceArgs_Output_lfts_inst : prod_vec lft DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_lfts)) (DropGlue_SelfasFnOnceArgs_Output_tys_inst : plist type DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_spec) DropGlue_SelfasFnOnceArgs_Output_lfts_inst DropGlue_SelfasFnOnceArgs_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_Self_Args_Output_rt) FnOnce_Self_Args_Output_st DropGlue_SelfasFnOnceArgs_Output_spec_attrs-[] -[FnOnce_Self_Args_Output_ty]))⌝ ∗ DropGlue_SelfasFnOnceArgs_Output_realization.(trait_ctx_wf) DropGlue_SelfasFnOnceArgs_Output_lfts_inst DropGlue_SelfasFnOnceArgs_Output_tys_inst π)
      ∗ (∃ (Fn_Self_Args_lfts_inst : prod_vec lft Fn_Self_Args_realization.(trait_ctx_lfts)) (Fn_Self_Args_tys_inst : plist type Fn_Self_Args_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_Self_Args_realization.(trait_ctx_spec) Fn_Self_Args_lfts_inst Fn_Self_Args_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (Self_rt) (Args_rt) (FnOnce_Self_Args_Output_rt) Self_st Args_st FnOnce_Self_Args_Output_st FnOnce_Self_Args_spec_attrs FnMut_Self_Args_spec_attrs DropGlue_Self_spec_attrs DropGlue_Args_spec_attrs DropGlue_SelfasFnOnceArgs_Output_spec_attrs Fn_Self_Args_spec_attrs-[] -[Self_ty; Args_ty; FnOnce_Self_Args_Output_ty]))⌝ ∗ Fn_Self_Args_realization.(trait_ctx_wf) Fn_Self_Args_lfts_inst Fn_Self_Args_tys_inst π))%I).
End Fn_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_REFmutFasFnOnceA_call_once (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (λ π, ((∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
    ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
    ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I).

Definition type_of_REFmutFasFnOnceA_call_once (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((FnOnce_base_spec (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)) (RefSynType) (A_st) (FnOnce_F_A_Output_st) ((drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type))) (DropGlue_A_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs) ((REFmutFasFnOnceA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))))
    -[] -[(mut_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty]).(FnOnce_call_once_spec)   a b))) <MERGE!>.


Definition trait_incl_of_REFFasFnA_call (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (λ π, ((∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
    ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
    ∗ (∃ (Fn_F_A_lfts_inst : prod_vec lft Fn_F_A_realization.(trait_ctx_lfts)) (Fn_F_A_tys_inst : plist type Fn_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_F_A_realization.(trait_ctx_spec) Fn_F_A_lfts_inst Fn_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs Fn_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ Fn_F_A_realization.(trait_ctx_wf) Fn_F_A_lfts_inst Fn_F_A_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
    ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I).

Definition type_of_REFFasFnA_call (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((Fn_base_spec ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (RefSynType) (A_st) (FnOnce_F_A_Output_st) ((REFFasFnOnceA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))) ((REFFasFnMutA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (F_rt))))) (DropGlue_A_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs) ((REFFasFnA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))))
    -[] -[(shr_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty]).(Fn_call_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFFasFnMutA_call_mut (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (λ π, ((∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
    ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
    ∗ (∃ (Fn_F_A_lfts_inst : prod_vec lft Fn_F_A_realization.(trait_ctx_lfts)) (Fn_F_A_tys_inst : plist type Fn_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_F_A_realization.(trait_ctx_spec) Fn_F_A_lfts_inst Fn_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs Fn_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ Fn_F_A_realization.(trait_ctx_wf) Fn_F_A_lfts_inst Fn_F_A_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
    ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I).

Definition type_of_REFFasFnMutA_call_mut (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((FnMut_base_spec ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (RefSynType) (A_st) (FnOnce_F_A_Output_st) ((REFFasFnOnceA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (F_rt))))) (DropGlue_A_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs) ((REFFasFnMutA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))))
    -[] -[(shr_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty]).(FnMut_call_mut_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFmutFasFnMutA_call_mut (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (λ π, ((∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
    ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
    ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I).

Definition type_of_REFmutFasFnMutA_call_mut (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((FnMut_base_spec (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)) (RefSynType) (A_st) (FnOnce_F_A_Output_st) ((REFmutFasFnOnceA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))) ((drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type))) (DropGlue_A_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs) ((REFmutFasFnMutA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))))
    -[] -[(mut_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty]).(FnMut_call_mut_spec)   a b))) <MERGE!>.

Definition trait_incl_of_REFFasFnOnceA_call_once (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (λ π, ((∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
    ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
    ∗ (∃ (Fn_F_A_lfts_inst : prod_vec lft Fn_F_A_realization.(trait_ctx_lfts)) (Fn_F_A_tys_inst : plist type Fn_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_F_A_realization.(trait_ctx_spec) Fn_F_A_lfts_inst Fn_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs Fn_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ Fn_F_A_realization.(trait_ctx_wf) Fn_F_A_lfts_inst Fn_F_A_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
    ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I).

Definition type_of_REFFasFnOnceA_call_once (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) :=
  spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT),(λ a b, scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_0)]) (((FnOnce_base_spec ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)) (RefSynType) (A_st) (FnOnce_F_A_Output_st) ((drop_glue_trivial_spec_attrs ((place_rfnRT (F_rt))))) (DropGlue_A_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs) ((REFFasFnOnceA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))))
    -[] -[(shr_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty]).(FnOnce_call_once_spec)   a b))) <MERGE!>.



End specs.
Section REFFasFnA_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFFasFnA_spec (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : (spec_with _ _ (Fn_spec ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), {|
        Fn_call_spec  :=
          (type_of_REFFasFnA_call ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (A_st) (F_st) (FnOnce_F_A_Output_st)) FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs Fn_F_A_spec_attrs DropGlue_A_spec_attrs DropGlue_F_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs 
             <TY> A_ty <TY> F_ty <TY> FnOnce_F_A_Output_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments REFFasFnA_spec : simpl never.

  Program Definition REFFasFnA_realization (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (place_rfnRT (F_rt)) (A_rt) (FnOnce_F_A_Output_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt; F_rt; FnOnce_F_A_Output_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
  ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
  ∗ (∃ (Fn_F_A_lfts_inst : prod_vec lft Fn_F_A_realization.(trait_ctx_lfts)) (Fn_F_A_tys_inst : plist type Fn_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_F_A_realization.(trait_ctx_spec) Fn_F_A_lfts_inst Fn_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs Fn_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ Fn_F_A_realization.(trait_ctx_wf) Fn_F_A_lfts_inst Fn_F_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
  ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) _ _, (REFFasFnA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFFasFnA_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(F_rt : !RT) `(FnOnce_F_A_Output_rt : !RT) `(A_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_A_Output_st : !syn_type) `(FnOnce_F_A_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnMut_F_A_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(Fn_F_A_spec_attrs : !(Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_FasFnOnceA_Output_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )), trait_incl_marker (lift_trait_incl Fn_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (REFFasFnA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] ((Fn_base_spec (place_rfnRT (F_rt)) (A_rt) (FnOnce_F_A_Output_rt) RefSynType A_st FnOnce_F_A_Output_st (REFFasFnOnceA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs)) (REFFasFnMutA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (F_rt)))) DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs (REFFasFnA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[] -[(shr_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty])))).
End REFFasFnA_spec.

Section REFFasFnMutA_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFFasFnMutA_spec (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : (spec_with _ _ (FnMut_spec ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (type_of_REFFasFnMutA_call_mut ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (A_st) (F_st) (FnOnce_F_A_Output_st)) FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs Fn_F_A_spec_attrs DropGlue_A_spec_attrs DropGlue_F_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs 
             <TY> A_ty <TY> F_ty <TY> FnOnce_F_A_Output_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments REFFasFnMutA_spec : simpl never.

  Program Definition REFFasFnMutA_realization (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (place_rfnRT (F_rt)) (A_rt) (FnOnce_F_A_Output_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt; F_rt; FnOnce_F_A_Output_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
  ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
  ∗ (∃ (Fn_F_A_lfts_inst : prod_vec lft Fn_F_A_realization.(trait_ctx_lfts)) (Fn_F_A_tys_inst : plist type Fn_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_F_A_realization.(trait_ctx_spec) Fn_F_A_lfts_inst Fn_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs Fn_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ Fn_F_A_realization.(trait_ctx_wf) Fn_F_A_lfts_inst Fn_F_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
  ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) _ _, (REFFasFnMutA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFFasFnMutA_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(F_rt : !RT) `(FnOnce_F_A_Output_rt : !RT) `(A_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_A_Output_st : !syn_type) `(FnOnce_F_A_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnMut_F_A_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(Fn_F_A_spec_attrs : !(Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_FasFnOnceA_Output_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (REFFasFnMutA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] ((FnMut_base_spec (place_rfnRT (F_rt)) (A_rt) (FnOnce_F_A_Output_rt) RefSynType A_st FnOnce_F_A_Output_st (REFFasFnOnceA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (F_rt)))) DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs (REFFasFnMutA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[] -[(shr_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty])))).
End REFFasFnMutA_spec.

Section REFFasFnOnceA_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFFasFnOnceA_spec (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : (spec_with _ _ (FnOnce_spec ((place_rfnRT (F_rt))) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), let Output_rt := (FnOnce_F_A_Output_rt) in {|
        FnOnce_call_once_spec  :=
          (type_of_REFFasFnOnceA_call_once ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (A_st) (F_st) (FnOnce_F_A_Output_st)) FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs Fn_F_A_spec_attrs DropGlue_A_spec_attrs DropGlue_F_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs 
             <TY> A_ty <TY> F_ty <TY> FnOnce_F_A_Output_ty <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments REFFasFnOnceA_spec : simpl never.

  Program Definition REFFasFnOnceA_realization (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (Fn_F_A_spec_attrs: (Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (Fn_F_A_realization: (trait_spec_realization (spec_with 0 [] (Fn_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (place_rfnRT (F_rt)) (A_rt) (FnOnce_F_A_Output_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt; F_rt; FnOnce_F_A_Output_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
  ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
  ∗ (∃ (Fn_F_A_lfts_inst : prod_vec lft Fn_F_A_realization.(trait_ctx_lfts)) (Fn_F_A_tys_inst : plist type Fn_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Fn_spec_incl (Fn_F_A_realization.(trait_ctx_spec) Fn_F_A_lfts_inst Fn_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Fn_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs Fn_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ Fn_F_A_realization.(trait_ctx_wf) Fn_F_A_lfts_inst Fn_F_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
  ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) _ _, (REFFasFnOnceA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFFasFnOnceA_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(F_rt : !RT) `(FnOnce_F_A_Output_rt : !RT) `(A_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_A_Output_st : !syn_type) `(FnOnce_F_A_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnMut_F_A_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(Fn_F_A_spec_attrs : !(Fn_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_FasFnOnceA_Output_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (REFFasFnOnceA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] ((FnOnce_base_spec (place_rfnRT (F_rt)) (A_rt) (FnOnce_F_A_Output_rt) RefSynType A_st FnOnce_F_A_Output_st (drop_glue_trivial_spec_attrs ((place_rfnRT (F_rt)))) DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs (REFFasFnOnceA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (Fn_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[] -[(shr_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty])))).
End REFFasFnOnceA_spec.

Section REFmutFasFnMutA_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFmutFasFnMutA_spec (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : (spec_with _ _ (FnMut_spec (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), {|
        FnMut_call_mut_spec  :=
          (type_of_REFmutFasFnMutA_call_mut ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (A_st) (F_st) (FnOnce_F_A_Output_st)) FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_A_spec_attrs DropGlue_F_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs 
             <TY> A_ty <TY> F_ty <TY> FnOnce_F_A_Output_ty <LFT> ulft_0 : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments REFmutFasFnMutA_spec : simpl never.

  Program Definition REFmutFasFnMutA_realization (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) ((place_rfnRT (F_rt)) * gname)%type (A_rt) (FnOnce_F_A_Output_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt; F_rt; FnOnce_F_A_Output_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
  ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
  ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) _ _, (REFmutFasFnMutA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFmutFasFnMutA_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(F_rt : !RT) `(FnOnce_F_A_Output_rt : !RT) `(A_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_A_Output_st : !syn_type) `(FnOnce_F_A_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnMut_F_A_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_FasFnOnceA_Output_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )), trait_incl_marker (lift_trait_incl FnMut_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (REFmutFasFnMutA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] ((FnMut_base_spec ((place_rfnRT (F_rt)) * gname)%type (A_rt) (FnOnce_F_A_Output_rt) RefSynType A_st FnOnce_F_A_Output_st (REFmutFasFnOnceA_spec_attrs ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs)) (drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type)) DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs (REFmutFasFnMutA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[] -[(mut_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty])))).
End REFmutFasFnMutA_spec.

Section REFmutFasFnOnceA_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFmutFasFnOnceA_spec (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) : (spec_with _ _ (FnOnce_spec (((place_rfnRT (F_rt)) * gname)%type) ((A_rt)) ((FnOnce_F_A_Output_rt)))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), let Output_rt := (FnOnce_F_A_Output_rt) in {|
        FnOnce_call_once_spec  :=
          (type_of_REFmutFasFnOnceA_call_once ((A_rt)) ((F_rt)) ((FnOnce_F_A_Output_rt)) (A_st) (F_st) (FnOnce_F_A_Output_st)) FnOnce_F_A_spec_attrs FnMut_F_A_spec_attrs DropGlue_A_spec_attrs DropGlue_F_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs 
             <TY> A_ty <TY> F_ty <TY> FnOnce_F_A_Output_ty <LFT> ulft_0 : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments REFmutFasFnOnceA_spec : simpl never.

  Program Definition REFmutFasFnOnceA_realization (A_rt: RT) (F_rt: RT) (FnOnce_F_A_Output_rt: RT) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) (FnOnce_F_A_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnOnce_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (FnMut_F_A_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) (FnMut_F_A_realization: (trait_spec_realization (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) (DropGlue_FasFnOnceA_Output_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )) (DropGlue_FasFnOnceA_Output_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (FnOnce_F_A_Output_rt))))) : trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) ((place_rfnRT (F_rt)) * gname)%type (A_rt) (FnOnce_F_A_Output_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt; F_rt; FnOnce_F_A_Output_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) π, (((typaram_wf A_rt A_st A_ty)
  ∗ (typaram_wf F_rt F_st F_ty)
  ∗ (typaram_wf FnOnce_F_A_Output_rt FnOnce_F_A_Output_st FnOnce_F_A_Output_ty))
  ∗ (∃ (FnOnce_F_A_lfts_inst : prod_vec lft FnOnce_F_A_realization.(trait_ctx_lfts)) (FnOnce_F_A_tys_inst : plist type FnOnce_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_A_realization.(trait_ctx_spec) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnOnce_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnOnce_F_A_realization.(trait_ctx_wf) FnOnce_F_A_lfts_inst FnOnce_F_A_tys_inst π)
  ∗ (∃ (FnMut_F_A_lfts_inst : prod_vec lft FnMut_F_A_realization.(trait_ctx_lfts)) (FnMut_F_A_tys_inst : plist type FnMut_F_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnMut_spec_incl (FnMut_F_A_realization.(trait_ctx_spec) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (A_rt) (FnOnce_F_A_Output_rt) F_st A_st FnOnce_F_A_Output_st FnOnce_F_A_spec_attrs DropGlue_F_spec_attrs DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs FnMut_F_A_spec_attrs-[] -[F_ty; A_ty; FnOnce_F_A_Output_ty]))⌝ ∗ FnMut_F_A_realization.(trait_ctx_wf) FnMut_F_A_lfts_inst FnMut_F_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
  ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π)
  ∗ (∃ (DropGlue_FasFnOnceA_Output_lfts_inst : prod_vec lft DropGlue_FasFnOnceA_Output_realization.(trait_ctx_lfts)) (DropGlue_FasFnOnceA_Output_tys_inst : plist type DropGlue_FasFnOnceA_Output_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_FasFnOnceA_Output_realization.(trait_ctx_spec) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (FnOnce_F_A_Output_rt) FnOnce_F_A_Output_st DropGlue_FasFnOnceA_Output_spec_attrs-[] -[FnOnce_F_A_Output_ty]))⌝ ∗ DropGlue_FasFnOnceA_Output_realization.(trait_ctx_wf) DropGlue_FasFnOnceA_Output_lfts_inst DropGlue_FasFnOnceA_Output_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) _ _, (REFmutFasFnOnceA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFmutFasFnOnceA_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(F_rt : !RT) `(FnOnce_F_A_Output_rt : !RT) `(A_st : !syn_type) `(F_st : !syn_type) `(FnOnce_F_A_Output_st : !syn_type) `(FnOnce_F_A_spec_attrs : !(FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(FnMut_F_A_spec_attrs : !(FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (A_rt) (FnOnce_F_A_Output_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_F_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) `(DropGlue_FasFnOnceA_Output_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (FnOnce_F_A_Output_rt) )), trait_incl_marker (lift_trait_incl FnOnce_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), (REFmutFasFnOnceA_spec (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (A_st) (F_st) (FnOnce_F_A_Output_st) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[ulft_0] -[A_ty; F_ty; FnOnce_F_A_Output_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty; F_ty; FnOnce_F_A_Output_ty]) : ([A_rt; F_rt; FnOnce_F_A_Output_rt] : list RT), scope_add_typarams _ -[A_ty; F_ty; FnOnce_F_A_Output_ty] ((FnOnce_base_spec ((place_rfnRT (F_rt)) * gname)%type (A_rt) (FnOnce_F_A_Output_rt) RefSynType A_st FnOnce_F_A_Output_st (drop_glue_trivial_spec_attrs (((place_rfnRT (F_rt)) * gname)%type)) DropGlue_A_spec_attrs DropGlue_FasFnOnceA_Output_spec_attrs (REFmutFasFnOnceA_spec_attrs (A_rt) (F_rt) (FnOnce_F_A_Output_rt) (FnOnce_F_A_spec_attrs) (FnMut_F_A_spec_attrs) (DropGlue_A_spec_attrs) (DropGlue_F_spec_attrs) (DropGlue_FasFnOnceA_Output_spec_attrs))-[] -[(mut_ref ulft_0 F_ty); A_ty; FnOnce_F_A_Output_ty])))).
End REFmutFasFnOnceA_spec.

