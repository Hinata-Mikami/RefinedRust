From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.cell.cell.generated Require Export generated_specs_cell.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.spin.theories.once Require Export once_ghost_state.
From rrstd.spin.spin Require Export generated_code_spin.

Record relax_RelaxStrategy_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_relax_RelaxStrategy_spec_attrs {
}.
#[global] Arguments relax_RelaxStrategy_spec_attrs : clear implicits.

#[global] Arguments relax_RelaxStrategy_spec_attrs {_ _}.

#[global] Arguments mk_relax_RelaxStrategy_spec_attrs  {_} {_} {_}.


Section relax_Spin_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition relax_Spin_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t relax_Spin_sls +[])).
  Defined.

  Definition relax_Spin_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (relax_Spin_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent relax_Spin_rt.
  #[global] Typeclasses Transparent relax_Spin_ty.
End relax_Spin_ty.
#[global] Arguments relax_Spin_rt : clear implicits.

#[global] Arguments relax_Spin_ty : clear implicits.

#[global] Arguments relax_Spin_ty {_ _}  .


Section rwlock_RwLockReadGuard_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition rwlock_RwLockReadGuard_ty  : (spec_with 1 [(T_rt)] ((type (plist place_rfnRT [(place_rfnRT (T_rt)) : RT])))).
  Proof.
    exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (rwlock_RwLockReadGuard_sls ((ty_syn_type T_ty MetaNone))) +[((shr_ref ulft_a T_ty))])).
  Defined.

  Definition rwlock_RwLockReadGuard_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (rwlock_RwLockReadGuard_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent rwlock_RwLockReadGuard_rt.
  #[global] Typeclasses Transparent rwlock_RwLockReadGuard_ty.
End rwlock_RwLockReadGuard_ty.
#[global] Arguments rwlock_RwLockReadGuard_rt : clear implicits.

#[global] Arguments rwlock_RwLockReadGuard_ty : clear implicits.

#[global] Arguments rwlock_RwLockReadGuard_ty {_ _} _  .

Section rwlock_RwLockReadGuard_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition rwlock_RwLockReadGuard_inv_t_inv_spec  : (spec_with 1 [(T_rt)] ((ex_inv_def ((rwlock_RwLockReadGuard_rt (T_rt)))%type (((T_rt)))%type))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (rwlock_RwLockReadGuard_rt (T_rt))) (_ty_rfn : RT_rt (((T_rt))%type : RT)),
                  let 'x := _ty_rfn in ⌜inner_rfn = -[#(#x)]⌝ ∗ True)%I
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

  Definition rwlock_RwLockReadGuard_inv_t  : (spec_with 1 [(T_rt)] ((type ((((T_rt)))%type)))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (rwlock_RwLockReadGuard_inv_t_inv_spec  -[ulft_a] -[T_ty]) ((rwlock_RwLockReadGuard_ty (T_rt)) -[ulft_a] -[T_ty]).
  #[global] Arguments rwlock_RwLockReadGuard_inv_t_inv_spec : simpl never.

  #[global] Arguments rwlock_RwLockReadGuard_inv_t : simpl never.

  #[global] Typeclasses Transparent rwlock_RwLockReadGuard_inv_t.
  Definition rwlock_RwLockReadGuard_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (rwlock_RwLockReadGuard_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent rwlock_RwLockReadGuard_inv_t_rt.
End rwlock_RwLockReadGuard_inv_t.
#[global] Arguments rwlock_RwLockReadGuard_inv_t_rt : clear implicits.

#[global] Arguments rwlock_RwLockReadGuard_inv_t : clear implicits.

#[global] Arguments rwlock_RwLockReadGuard_inv_t {_ _} _  .

#[global] Arguments rwlock_RwLockReadGuard_inv_t_inv_spec : clear implicits.

#[global] Arguments rwlock_RwLockReadGuard_inv_t_inv_spec {_ _} _  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition relax_Spinasrelax_RelaxStrategy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((relax_RelaxStrategy_spec_attrs ((relax_Spin_rt)))) :=
  mk_relax_RelaxStrategy_spec_attrs.


End attrs.

Section once_Once_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {R_rt : RT}.
  (* Additional parameters *)
  Context `{_CTX0 : !(onceG Σ ((RT_xt (T_rt))))}.
  Definition once_Once_ty  : (spec_with 0 [(T_rt); (R_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((R_rt)))) : RT; (((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
  Proof using _CTX0.
    exact (spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (struct_t (once_Once_sls ((ty_syn_type T_ty MetaNone)) ((ty_syn_type R_ty MetaNone))) +[((core_marker_PhantomData_ty ((R_rt)) -[] -[R_ty])); ((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))])).
  Defined.

  Definition once_Once_rt  : RT.
  Proof using T_rt R_rt .
    let __a := (normalized_rt_of_spec_ty (once_Once_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent once_Once_rt.
  #[global] Typeclasses Transparent once_Once_ty.
End once_Once_ty.
#[global] Arguments once_Once_rt : clear implicits.

#[global] Arguments once_Once_ty : clear implicits.

#[global] Arguments once_Once_ty {_ _} _ _   {_}.

Section once_Once_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {R_rt : RT}.
  (* Additional parameters *)
  Context `{_CTX0 : !(onceG Σ ((RT_xt (T_rt))))}.
  Program Definition once_Once_inv_t_inv_spec  : (spec_with 0 [(T_rt); (R_rt)] ((ex_inv_def ((once_Once_rt (T_rt) (R_rt)))%type ((gname))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (once_Once_rt (T_rt) (R_rt))) (_ty_rfn : RT_rt ((gname)%type : RT)),
                  let 'η := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z) (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(x); #(y)]⌝ ∗ True)%I
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

  Definition once_Once_inv_t  : (spec_with 0 [(T_rt); (R_rt)] ((type (((gname))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ex_plain_t _ _ (once_Once_inv_t_inv_spec  -[] -[T_ty; R_ty]) ((once_Once_ty (T_rt) (R_rt)) -[] -[T_ty; R_ty]).
  #[global] Arguments once_Once_inv_t_inv_spec : simpl never.

  #[global] Arguments once_Once_inv_t : simpl never.

  #[global] Typeclasses Transparent once_Once_inv_t.
  Definition once_Once_inv_t_rt  : RT.
  Proof using T_rt R_rt .
    let __a := (normalized_rt_of_spec_ty (once_Once_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent once_Once_inv_t_rt.
End once_Once_inv_t.
#[global] Arguments once_Once_inv_t_rt : clear implicits.

#[global] Arguments once_Once_inv_t : clear implicits.

#[global] Arguments once_Once_inv_t {_ _} _ _   {_}.

#[global] Arguments once_Once_inv_t_inv_spec : clear implicits.

#[global] Arguments once_Once_inv_t_inv_spec {_ _} _ _   {_}.


Section rwlock_RwLock_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {R_rt : RT}.
  Definition rwlock_RwLock_ty  : (spec_with 0 [(T_rt); (R_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((R_rt)))) : RT; ((((UnsafeCell_inv_t_rt)) ((T_rt)))) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (struct_t (rwlock_RwLock_sls ((ty_syn_type T_ty MetaNone)) ((ty_syn_type R_ty MetaNone))) +[((core_marker_PhantomData_ty ((R_rt)) -[] -[R_ty])); ((UnsafeCell_inv_t ((T_rt)) -[] -[T_ty]))])).
  Defined.

  Definition rwlock_RwLock_rt  : RT.
  Proof using T_rt R_rt .
    let __a := (normalized_rt_of_spec_ty (rwlock_RwLock_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent rwlock_RwLock_rt.
  #[global] Typeclasses Transparent rwlock_RwLock_ty.
End rwlock_RwLock_ty.
#[global] Arguments rwlock_RwLock_rt : clear implicits.

#[global] Arguments rwlock_RwLock_ty : clear implicits.

#[global] Arguments rwlock_RwLock_ty {_ _} _ _  .

Section rwlock_RwLock_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {R_rt : RT}.
  Program Definition rwlock_RwLock_inv_t_inv_spec  : (spec_with 0 [(T_rt); (R_rt)] ((ex_inv_def ((rwlock_RwLock_rt (T_rt) (R_rt)))%type ((unit))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (rwlock_RwLock_rt (T_rt) (R_rt))) (_ty_rfn : RT_rt ((unit)%type : RT)),
                  let '() := _ty_rfn in ∃ (x: name_hint_ty "x" (((RT_xt (T_rt))))%Z) (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(y); #($# x)]⌝ ∗ True)%I
          (false)
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

  Definition rwlock_RwLock_inv_t  : (spec_with 0 [(T_rt); (R_rt)] ((type (((unit))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ex_plain_t _ _ (rwlock_RwLock_inv_t_inv_spec  -[] -[T_ty; R_ty]) ((rwlock_RwLock_ty (T_rt) (R_rt)) -[] -[T_ty; R_ty]).
  #[global] Arguments rwlock_RwLock_inv_t_inv_spec : simpl never.

  #[global] Arguments rwlock_RwLock_inv_t : simpl never.

  #[global] Typeclasses Transparent rwlock_RwLock_inv_t.
  Definition rwlock_RwLock_inv_t_rt  : RT.
  Proof using T_rt R_rt .
    let __a := (normalized_rt_of_spec_ty (rwlock_RwLock_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent rwlock_RwLock_inv_t_rt.
End rwlock_RwLock_inv_t.
#[global] Arguments rwlock_RwLock_inv_t_rt : clear implicits.

#[global] Arguments rwlock_RwLock_inv_t : clear implicits.

#[global] Arguments rwlock_RwLock_inv_t {_ _} _ _  .

#[global] Arguments rwlock_RwLock_inv_t_inv_spec : clear implicits.

#[global] Arguments rwlock_RwLock_inv_t_inv_spec {_ _} _ _  .


Section rwlock_RwLockWriteGuard_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {R_rt : RT}.
  Definition rwlock_RwLockWriteGuard_ty  : (spec_with 1 [(T_rt); (R_rt)] ((type (plist place_rfnRT [(place_rfnRT ((rwlock_RwLock_inv_t_rt ((T_rt)) ((relax_Spin_rt))))) : RT; (R_rt) : RT])))).
  Proof.
    exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (struct_t (rwlock_RwLockWriteGuard_sls ((ty_syn_type T_ty MetaNone)) ((ty_syn_type R_ty MetaNone))) +[((shr_ref ulft_a (rwlock_RwLock_inv_t ((T_rt)) ((relax_Spin_rt))  -[] -[T_ty; (relax_Spin_ty   -[] -[])]))); (R_ty)])).
  Defined.

  Definition rwlock_RwLockWriteGuard_rt  : RT.
  Proof using T_rt R_rt .
    let __a := (normalized_rt_of_spec_ty (rwlock_RwLockWriteGuard_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent rwlock_RwLockWriteGuard_rt.
  #[global] Typeclasses Transparent rwlock_RwLockWriteGuard_ty.
End rwlock_RwLockWriteGuard_ty.
#[global] Arguments rwlock_RwLockWriteGuard_rt : clear implicits.

#[global] Arguments rwlock_RwLockWriteGuard_ty : clear implicits.

#[global] Arguments rwlock_RwLockWriteGuard_ty {_ _} _ _  .

Section rwlock_RwLockWriteGuard_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {R_rt : RT}.
  Program Definition rwlock_RwLockWriteGuard_inv_t_inv_spec  : (spec_with 1 [(T_rt); (R_rt)] ((ex_inv_def ((rwlock_RwLockWriteGuard_rt (T_rt) (R_rt)))%type ((place_rfn (T_rt)))%type))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (rwlock_RwLockWriteGuard_rt (T_rt) (R_rt))) (_ty_rfn : RT_rt ((place_rfn (T_rt))%type : RT)),
                  let 'x := _ty_rfn in ∃ (y: name_hint_ty "y" (((RT_xt (R_rt))))%Z), ⌜inner_rfn = -[#(#tt); #($# y)]⌝ ∗ True)%I
          (false)
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

  Definition rwlock_RwLockWriteGuard_inv_t  : (spec_with 1 [(T_rt); (R_rt)] ((type (((place_rfn (T_rt)))%type)))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ex_plain_t _ _ (rwlock_RwLockWriteGuard_inv_t_inv_spec  -[ulft_a] -[T_ty; R_ty]) ((rwlock_RwLockWriteGuard_ty (T_rt) (R_rt)) -[ulft_a] -[T_ty; R_ty]).
  #[global] Arguments rwlock_RwLockWriteGuard_inv_t_inv_spec : simpl never.

  #[global] Arguments rwlock_RwLockWriteGuard_inv_t : simpl never.

  #[global] Typeclasses Transparent rwlock_RwLockWriteGuard_inv_t.
  Definition rwlock_RwLockWriteGuard_inv_t_rt  : RT.
  Proof using T_rt R_rt .
    let __a := (normalized_rt_of_spec_ty (rwlock_RwLockWriteGuard_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent rwlock_RwLockWriteGuard_inv_t_rt.
End rwlock_RwLockWriteGuard_inv_t.
#[global] Arguments rwlock_RwLockWriteGuard_inv_t_rt : clear implicits.

#[global] Arguments rwlock_RwLockWriteGuard_inv_t : clear implicits.

#[global] Arguments rwlock_RwLockWriteGuard_inv_t {_ _} _ _  .

#[global] Arguments rwlock_RwLockWriteGuard_inv_t_inv_spec : clear implicits.

#[global] Arguments rwlock_RwLockWriteGuard_inv_t_inv_spec {_ _} _ _  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (R_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : ((Deref_spec_attrs (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)))) :=
  {|
    Deref_DerefInto  :=
      (id) : ((Deref_DerefInto_sig (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (R_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : ((DerefMut_spec_attrs (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))))) :=
  {|
    DerefMut_DerefMutInject  :=
      (λ old γ, 👻 γ) : ((DerefMut_DerefMutInject_sig (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs)))));
  |}
.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition drop_glue_rwlock_RwLock_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (R_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : ((DropGlue_spec_attrs (((rwlock_RwLock_inv_t_rt ((T_rt)) ((R_rt))))))) :=
  {|
    DropGlue_DropGlueUnwind  :=
      (DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind)) : ((DropGlue_DropGlueUnwind_sig (((rwlock_RwLock_inv_t_rt ((T_rt)) ((R_rt)))))));
  |}
.


Program Definition drop_glue_rwlock_RwLockWriteGuard_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (R_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : ((DropGlue_spec_attrs (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))))) :=
  {|
    DropGlue_DropGlueUnwind  :=
      (False) : ((DropGlue_DropGlueUnwind_sig (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))))));
  |}
.


End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)

Section extra.
Context `{RRGS : !refinedrustGS Σ}.


Lemma resolve_ghost_writeguard {T_rt R_rt} (T_ty : type T_rt) (R_ty : type R_rt) (lft_a : lft) π E L r rm T :
    (∀ l', resolve_ghost π E L rm true l' (◁ T_ty) Owned r T)
    ⊢ resolve_ghost_adt π E L rm r (rwlock_RwLockWriteGuard_inv_t T_rt R_rt <LFT> lft_a <TY> T_ty <TY> R_ty <INST!>) T.
  Proof.
  Admitted.
Definition resolve_ghost_writeguard_inst := [instance @resolve_ghost_writeguard].
Global Existing Instance resolve_ghost_writeguard_inst.

End extra.
Record relax_RelaxStrategy_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_relax_RelaxStrategy_spec {
  relax_RelaxStrategy_relax_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments relax_RelaxStrategy_spec : clear implicits.

#[global] Arguments relax_RelaxStrategy_spec {_ _}.


Section relax_RelaxStrategy.
Context `{RRGS : !refinedrustGS Σ}.
Definition relax_RelaxStrategy_spec_incl `{Self_rt : !RT} (spec1: ((relax_RelaxStrategy_spec (Self_rt)))) (spec2: ((relax_RelaxStrategy_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(relax_RelaxStrategy_relax_spec)) (spec2.(relax_RelaxStrategy_relax_spec)))).
Instance relax_RelaxStrategy_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (relax_RelaxStrategy_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_relax_RelaxStrategy_spec `{Self_rt : !RT} : (ScopeBindable ((relax_RelaxStrategy_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((relax_RelaxStrategy_spec (Self_rt)))) :=
      {|
        relax_RelaxStrategy_relax_spec  :=
          (scope_add_typarams (rts) (tys) (s.(relax_RelaxStrategy_relax_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((relax_RelaxStrategy_spec (Self_rt)))) :=
      {|
        relax_RelaxStrategy_relax_spec  :=
          (scope_add_elctx (E) (s.(relax_RelaxStrategy_relax_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_relax_RelaxStrategy_spec.

Definition relax_RelaxStrategy_relax_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (relax_RelaxStrategy_Self_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ unit_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition relax_RelaxStrategy_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((relax_RelaxStrategy_spec_attrs ((Self_rt))))) : (spec_with _ _ (relax_RelaxStrategy_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      relax_RelaxStrategy_relax_spec  :=
        (relax_RelaxStrategy_relax_base_spec ((Self_rt)) (Self_st)) DropGlue_Self_spec_attrs _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
    |}
.
Arguments relax_RelaxStrategy_base_spec : simpl never.


End relax_RelaxStrategy.

Section relax_RelaxStrategy_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_relax_RelaxStrategy_relax (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Self_rt))))) (relax_RelaxStrategy_Self_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (Self_rt) )) (relax_RelaxStrategy_Self_realization: (trait_spec_realization (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (Self_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (λ π, ((∃ (DropGlue_Self_lfts_inst : prod_vec lft DropGlue_Self_realization.(trait_ctx_lfts)) (DropGlue_Self_tys_inst : plist type DropGlue_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_Self_realization.(trait_ctx_spec) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ DropGlue_Self_realization.(trait_ctx_wf) DropGlue_Self_lfts_inst DropGlue_Self_tys_inst π)
      ∗ (∃ (relax_RelaxStrategy_Self_lfts_inst : prod_vec lft relax_RelaxStrategy_Self_realization.(trait_ctx_lfts)) (relax_RelaxStrategy_Self_tys_inst : plist type relax_RelaxStrategy_Self_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl (relax_RelaxStrategy_Self_realization.(trait_ctx_spec) relax_RelaxStrategy_Self_lfts_inst relax_RelaxStrategy_Self_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (Self_rt) Self_st DropGlue_Self_spec_attrs relax_RelaxStrategy_Self_spec_attrs-[] -[Self_ty]))⌝ ∗ relax_RelaxStrategy_Self_realization.(trait_ctx_wf) relax_RelaxStrategy_Self_lfts_inst relax_RelaxStrategy_Self_tys_inst π))%I).
End relax_RelaxStrategy_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_drop_glue_rwlock_RwLock (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_drop_glue_rwlock_RwLock (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; R_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((rwlock_RwLock_inv_t_rt ((T_rt)) ((R_rt))))) ((rwlock_RwLock_st (T_st) (R_st))) ((drop_glue_rwlock_RwLock_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))))
    -[] -[(rwlock_RwLock_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.

Definition trait_incl_of_drop_glue_rwlock_RwLockWriteGuard (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_drop_glue_rwlock_RwLockWriteGuard (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; R_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_a)] ++ ty_outlives_E (T_ty) ulft_a) (((DropGlue_base_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((rwlock_RwLockWriteGuard_st (T_st) (R_st))) ((drop_glue_rwlock_RwLockWriteGuard_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))))
    -[] -[(rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_a] -[T_ty; R_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.


Definition trait_incl_of_relax_Spinasrelax_RelaxStrategy_relax  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_relax_Spinasrelax_RelaxStrategy_relax  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ unit_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_deref (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_rwlock; ulft_2]) : 2 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_deref (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; R_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_rwlock)]) (((Deref_base_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuard_st (T_st) (R_st))) (T_st) ((drop_glue_rwlock_RwLockWriteGuard_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))) (DropGlue_T_spec_attrs) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))))
    -[] -[(rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_rwlock] -[T_ty; R_ty]); T_ty]).(Deref_deref_spec)   a b))) <MERGE!>.

Definition trait_incl_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_deref_mut (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_rwlock; ulft_2]) : 2 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_deref_mut (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; R_ty] (scope_add_elctx (λ ϝ, [(ϝ, ulft_rwlock)]) (((DerefMut_base_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuard_st (T_st) (R_st))) (T_st) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))) ((drop_glue_rwlock_RwLockWriteGuard_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))) (DropGlue_T_spec_attrs) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))))
    -[] -[(rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_rwlock] -[T_ty; R_ty]); T_ty]).(DerefMut_deref_mut_spec)   a b))) <MERGE!>.

Definition trait_incl_of_once_Once_TR_call_once (T_rt: RT) (R_rt: RT) (F_rt: RT) (T_st: syn_type) (R_st: syn_type) (F_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_realization: (trait_spec_realization (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (R_rt))))) (FnOnce_F_unit_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) unit (T_rt) )) (FnOnce_F_unit_realization: (trait_spec_realization (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) unit (T_rt))))) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) (DropGlue_F_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (F_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty; F_ty]) : ([T_rt; R_rt; F_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π)
    ∗ (∃ (relax_RelaxStrategy_R_lfts_inst : prod_vec lft relax_RelaxStrategy_R_realization.(trait_ctx_lfts)) (relax_RelaxStrategy_R_tys_inst : plist type relax_RelaxStrategy_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl (relax_RelaxStrategy_R_realization.(trait_ctx_spec) relax_RelaxStrategy_R_lfts_inst relax_RelaxStrategy_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (R_rt) R_st DropGlue_R_spec_attrs relax_RelaxStrategy_R_spec_attrs-[] -[R_ty]))⌝ ∗ relax_RelaxStrategy_R_realization.(trait_ctx_wf) relax_RelaxStrategy_R_lfts_inst relax_RelaxStrategy_R_tys_inst π)
    ∗ (∃ (FnOnce_F_unit_lfts_inst : prod_vec lft FnOnce_F_unit_realization.(trait_ctx_lfts)) (FnOnce_F_unit_tys_inst : plist type FnOnce_F_unit_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl FnOnce_spec_incl (FnOnce_F_unit_realization.(trait_ctx_spec) FnOnce_F_unit_lfts_inst FnOnce_F_unit_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) unit (T_rt) F_st UnitSynType T_st DropGlue_F_spec_attrs (drop_glue_trivial_spec_attrs (unit)) DropGlue_T_spec_attrs FnOnce_F_unit_spec_attrs-[] -[F_ty; unit_t; T_ty]))⌝ ∗ FnOnce_F_unit_realization.(trait_ctx_wf) FnOnce_F_unit_lfts_inst FnOnce_F_unit_tys_inst π)
    ∗ (∃ (DropGlue_F_lfts_inst : prod_vec lft DropGlue_F_realization.(trait_ctx_lfts)) (DropGlue_F_tys_inst : plist type DropGlue_F_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_F_realization.(trait_ctx_spec) DropGlue_F_lfts_inst DropGlue_F_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (F_rt) F_st DropGlue_F_spec_attrs-[] -[F_ty]))⌝ ∗ DropGlue_F_realization.(trait_ctx_wf) DropGlue_F_lfts_inst DropGlue_F_tys_inst π))%I).

Definition type_of_once_Once_TR_call_once (T_rt: RT) (R_rt: RT) (F_rt: RT) (T_st: syn_type) (R_st: syn_type) (F_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (FnOnce_F_unit_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) unit (T_rt) )) (DropGlue_F_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (F_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty; F_ty]) : ([(T_rt, T_st); (R_rt, R_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, f) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (once_Once_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty])), f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_unit_spec_attrs.(FnOnce_Pre) π p f ())
        ∗ (once_status_tok self None)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (x) : ((_)), x @ (shr_ref ulft_1 T_ty);
      (* postcondition *) (λ π : thread_id, (FnOnce_F_unit_spec_attrs.(FnOnce_Post) π p f () x)
      ∗ (once_status_tok self (Some x))) |
      (* unwind cond... *) FnOnce_F_unit_spec_attrs.(FnOnce_UnwindCondition) f p tt |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_once_Once_TR_get (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_once_Once_TR_get (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (o, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (once_Once_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]));
      (* precondition. *) (λ π : thread_id, (once_status_tok self o)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, o @ (Option_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_1 T_ty)]);
      (* postcondition *) (λ π : thread_id, (once_status_tok self o)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_once_Once_TR_initialized (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_once_Once_TR_initialized (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (data) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) data :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (η) : ((_)), η @ (once_Once_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]);
      (* postcondition *) (λ π : thread_id, (once_status_tok η (Some data))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_once_Once_TR_is_completed (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_once_Once_TR_is_completed (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (o, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (once_Once_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]));
      (* precondition. *) (λ π : thread_id, (once_status_tok self o)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_Some o) @ bool_t;
      (* postcondition *) (λ π : thread_id, (once_status_tok self o)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_once_Once_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_once_Once_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (once_Once_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]);
      (* postcondition *) (λ π : thread_id, (once_status_tok ret None)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLock_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I).

Definition type_of_rwlock_RwLock_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (t) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) t :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ (rwlock_RwLock_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLock_TR_read (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_realization: (trait_spec_realization (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π)
    ∗ (∃ (relax_RelaxStrategy_R_lfts_inst : prod_vec lft relax_RelaxStrategy_R_realization.(trait_ctx_lfts)) (relax_RelaxStrategy_R_tys_inst : plist type relax_RelaxStrategy_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl (relax_RelaxStrategy_R_realization.(trait_ctx_spec) relax_RelaxStrategy_R_lfts_inst relax_RelaxStrategy_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (R_rt) R_st DropGlue_R_spec_attrs relax_RelaxStrategy_R_spec_attrs-[] -[R_ty]))⌝ ∗ relax_RelaxStrategy_R_realization.(trait_ctx_wf) relax_RelaxStrategy_R_lfts_inst relax_RelaxStrategy_R_tys_inst π))%I).

Definition type_of_rwlock_RwLock_TR_read (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (rwlock_RwLock_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (rwlock_RwLockReadGuard_inv_t ((T_rt))  -[ulft_1] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLock_TR_write (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_realization: (trait_spec_realization (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (R_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π)
    ∗ (∃ (relax_RelaxStrategy_R_lfts_inst : prod_vec lft relax_RelaxStrategy_R_realization.(trait_ctx_lfts)) (relax_RelaxStrategy_R_tys_inst : plist type relax_RelaxStrategy_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl (relax_RelaxStrategy_R_realization.(trait_ctx_spec) relax_RelaxStrategy_R_lfts_inst relax_RelaxStrategy_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (R_rt) R_st DropGlue_R_spec_attrs relax_RelaxStrategy_R_spec_attrs-[] -[R_ty]))⌝ ∗ relax_RelaxStrategy_R_realization.(trait_ctx_wf) relax_RelaxStrategy_R_lfts_inst relax_RelaxStrategy_R_tys_inst π))%I).

Definition type_of_rwlock_RwLock_TR_write (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (rwlock_RwLock_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_1] -[T_ty; R_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
Section relax_Spinasrelax_RelaxStrategy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition relax_Spinasrelax_RelaxStrategy_spec  : (spec_with _ _ (relax_RelaxStrategy_spec ((relax_Spin_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        relax_RelaxStrategy_relax_spec  :=
          type_of_relax_Spinasrelax_RelaxStrategy_relax 
             : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments relax_Spinasrelax_RelaxStrategy_spec : simpl never.

  Program Definition relax_Spinasrelax_RelaxStrategy_realization  : trait_spec_realization (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (relax_Spin_rt))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, relax_Spinasrelax_RelaxStrategy_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition relax_Spinasrelax_RelaxStrategy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_Spinasrelax_RelaxStrategy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((relax_RelaxStrategy_base_spec (relax_Spin_rt) relax_Spin_st (drop_glue_trivial_spec_attrs ((relax_Spin_rt))) relax_Spinasrelax_RelaxStrategy_spec_attrs-[] -[(relax_Spin_ty   -[] -[])])))).
End relax_Spinasrelax_RelaxStrategy_spec.

Section rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : (spec_with _ _ (Deref_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)))) :=
    spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), let Target_rt := (T_rt) in {|
        Deref_deref_spec  :=
          (type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_deref ((T_rt)) ((R_rt)) (T_st) (R_st)) DropGlue_T_spec_attrs DropGlue_R_spec_attrs 
             <TY> T_ty <TY> R_ty <LFT> ulft_rwlock : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec : simpl never.

  Program Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_realization (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : trait_spec_realization (spec_with 0 [] (Deref_spec (RRGS:=RRGS) ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (T_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [T_rt; R_rt];
    trait_ctx_wf := λ '( *[ulft_rwlock]) '( *[T_ty; R_ty]) π, (((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf R_rt R_st R_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
  ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_rwlock]) '( *[T_ty; R_ty]) _ _, (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[ulft_rwlock] -[T_ty; R_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(R_rt : !RT) `(T_st : !syn_type) `(R_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_R_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )), trait_incl_marker (lift_trait_incl Deref_spec_incl (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[ulft_rwlock] -[T_ty; R_ty]) (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), scope_add_typarams _ -[T_ty; R_ty] ((Deref_base_spec ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (T_rt) (rwlock_RwLockWriteGuard_st (T_st) (R_st)) T_st (drop_glue_rwlock_RwLockWriteGuard_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs)) DropGlue_T_spec_attrs (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[] -[(rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_rwlock] -[T_ty; R_ty]); T_ty])))).
End rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec.

Section rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : (spec_with _ _ (DerefMut_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)))) :=
    spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), {|
        DerefMut_deref_mut_spec  :=
          (type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_deref_mut ((T_rt)) ((R_rt)) (T_st) (R_st)) DropGlue_T_spec_attrs DropGlue_R_spec_attrs 
             <TY> T_ty <TY> R_ty <LFT> ulft_rwlock : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec : simpl never.

  Program Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_realization (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : trait_spec_realization (spec_with 0 [] (DerefMut_spec (RRGS:=RRGS) ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (T_rt))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [T_rt; R_rt];
    trait_ctx_wf := λ '( *[ulft_rwlock]) '( *[T_ty; R_ty]) π, (((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf R_rt R_st R_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
  ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_rwlock]) '( *[T_ty; R_ty]) _ _, (rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[ulft_rwlock] -[T_ty; R_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(R_rt : !RT) `(T_st : !syn_type) `(R_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_R_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )), trait_incl_marker (lift_trait_incl DerefMut_spec_incl (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[ulft_rwlock] -[T_ty; R_ty]) (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), scope_add_typarams _ -[T_ty; R_ty] ((DerefMut_base_spec ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (T_rt) (rwlock_RwLockWriteGuard_st (T_st) (R_st)) T_st (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs)) (drop_glue_rwlock_RwLockWriteGuard_spec_attrs ((T_rt)) ((R_rt)) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs)) DropGlue_T_spec_attrs (rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[] -[(rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_rwlock] -[T_ty; R_ty]); T_ty])))).
End rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec.

Section drop_glue_rwlock_RwLock_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_rwlock_RwLock_spec (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : (spec_with _ _ (DropGlue_spec (((rwlock_RwLock_inv_t_rt ((T_rt)) ((R_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_rwlock_RwLock ((T_rt)) ((R_rt)) (T_st) (R_st)) DropGlue_T_spec_attrs DropGlue_R_spec_attrs 
             <TY> T_ty <TY> R_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments drop_glue_rwlock_RwLock_spec : simpl never.

  Program Definition drop_glue_rwlock_RwLock_realization (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) ((rwlock_RwLock_inv_t_rt ((T_rt)) ((R_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt; R_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty; R_ty]) π, (((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf R_rt R_st R_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
  ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty; R_ty]) _ _, (drop_glue_rwlock_RwLock_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[] -[T_ty; R_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition drop_glue_rwlock_RwLock_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(R_rt : !RT) `(T_st : !syn_type) `(R_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_R_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (drop_glue_rwlock_RwLock_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[] -[T_ty; R_ty]) (spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), scope_add_typarams _ -[T_ty; R_ty] ((DropGlue_base_spec ((rwlock_RwLock_inv_t_rt ((T_rt)) ((R_rt)))) (rwlock_RwLock_st (T_st) (R_st)) (drop_glue_rwlock_RwLock_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[] -[(rwlock_RwLock_inv_t ((T_rt)) ((R_rt))  -[] -[T_ty; R_ty])])))).
End drop_glue_rwlock_RwLock_spec.

Section drop_glue_rwlock_RwLockWriteGuard_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_rwlock_RwLockWriteGuard_spec (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) : (spec_with _ _ (DropGlue_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_rwlock_RwLockWriteGuard ((T_rt)) ((R_rt)) (T_st) (R_st)) DropGlue_T_spec_attrs DropGlue_R_spec_attrs 
             <TY> T_ty <TY> R_ty <LFT> ulft_a : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments drop_glue_rwlock_RwLockWriteGuard_spec : simpl never.

  Program Definition drop_glue_rwlock_RwLockWriteGuard_realization (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_R_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )) (DropGlue_R_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (R_rt))))) : trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [T_rt; R_rt];
    trait_ctx_wf := λ '( *[ulft_a]) '( *[T_ty; R_ty]) π, (((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf R_rt R_st R_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
  ∗ (∃ (DropGlue_R_lfts_inst : prod_vec lft DropGlue_R_realization.(trait_ctx_lfts)) (DropGlue_R_tys_inst : plist type DropGlue_R_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_R_realization.(trait_ctx_spec) DropGlue_R_lfts_inst DropGlue_R_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (R_rt) R_st DropGlue_R_spec_attrs-[] -[R_ty]))⌝ ∗ DropGlue_R_realization.(trait_ctx_wf) DropGlue_R_lfts_inst DropGlue_R_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_a]) '( *[T_ty; R_ty]) _ _, (drop_glue_rwlock_RwLockWriteGuard_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[ulft_a] -[T_ty; R_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition drop_glue_rwlock_RwLockWriteGuard_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(R_rt : !RT) `(T_st : !syn_type) `(R_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_R_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (R_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (drop_glue_rwlock_RwLockWriteGuard_spec (T_rt) (R_rt) (T_st) (R_st) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[ulft_a] -[T_ty; R_ty]) (spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), scope_add_typarams _ -[T_ty; R_ty] ((DropGlue_base_spec ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (rwlock_RwLockWriteGuard_st (T_st) (R_st)) (drop_glue_rwlock_RwLockWriteGuard_spec_attrs (T_rt) (R_rt) (DropGlue_T_spec_attrs) (DropGlue_R_spec_attrs))-[] -[(rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))  -[ulft_a] -[T_ty; R_ty])])))).
End drop_glue_rwlock_RwLockWriteGuard_spec.

