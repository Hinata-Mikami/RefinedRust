From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.spin.theories.once Require Export once_ghost_state.
From rrstd.spin.spin Require Export generated_code_spin.

Record relax_RelaxStrategy_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_relax_RelaxStrategy_spec_attrs {
}.
#[global] Arguments relax_RelaxStrategy_spec_attrs : clear implicits.

#[global] Arguments relax_RelaxStrategy_spec_attrs {_ _}.

#[global] Arguments mk_relax_RelaxStrategy_spec_attrs  {_} {_} {_}.


Section once_Once_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (R_rt : RT).

   (* Additional parameters *)
  Context `{_CTX0 : !(onceG Σ ((RT_xt (T_rt))))}.

Definition once_Once_ty  : (spec_with 0 [(T_rt); (R_rt)] ((type (plist place_rfnRT [(R_rt) : RT; (T_rt) : RT])))).
Proof using _CTX0.
  exact (spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ((struct_t (once_Once_sls ((T_ty.(ty_syn_type) (MetaNone))) ((R_ty.(ty_syn_type) (MetaNone)))) +[(R_ty); (T_ty)]))).
Defined.

Definition once_Once_rt  : RT.
Proof using T_rt R_rt .
  let __a := (normalized_rt_of_spec_ty (once_Once_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent once_Once_ty.
#[global] Typeclasses Transparent once_Once_rt.
End once_Once_ty.
Global Arguments once_Once_rt : clear implicits.
Section once_Once_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (R_rt : RT).
   (* Additional parameters *)
  Context `{_CTX0 : !(onceG Σ ((RT_xt (T_rt))))}.

  Program Definition once_Once_inv_t_inv_spec  : spec_with 0 [T_rt; R_rt] (ex_inv_def ((once_Once_rt (T_rt) (R_rt)))%type ((gname))%type) := spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((gname)%type : RT)),
            let 'η := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z) (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(x); #(y)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition once_Once_inv_t  : spec_with 0 [T_rt; R_rt] (type ((gname))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ex_plain_t _ _ (once_Once_inv_t_inv_spec   <TY> T_ty <TY> R_ty <INST!>) ((once_Once_ty (T_rt) (R_rt))  <TY> T_ty <TY> R_ty <INST!>).
  Global Typeclasses Transparent once_Once_inv_t.
  Definition once_Once_inv_t_rt : RT.
  Proof using T_rt R_rt . let __a := normalized_rt_of_spec_ty once_Once_inv_t in exact __a. Defined.
  Global Typeclasses Transparent once_Once_inv_t_rt.
End once_Once_inv_t.
Global Arguments once_Once_inv_t_rt : clear implicits.

Section relax_Spin_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition relax_Spin_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t relax_Spin_sls +[]))).
Defined.

Definition relax_Spin_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (relax_Spin_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent relax_Spin_ty.
#[global] Typeclasses Transparent relax_Spin_rt.
End relax_Spin_ty.
Global Arguments relax_Spin_rt : clear implicits.

Section rwlock_RwLockReadGuard_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition rwlock_RwLockReadGuard_ty  : (spec_with 1 [(T_rt)] ((type (plist place_rfnRT [(place_rfnRT (T_rt)) : RT])))).
Proof.
  exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (rwlock_RwLockReadGuard_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[((shr_ref ulft_a T_ty))]))).
Defined.

Definition rwlock_RwLockReadGuard_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (rwlock_RwLockReadGuard_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent rwlock_RwLockReadGuard_ty.
#[global] Typeclasses Transparent rwlock_RwLockReadGuard_rt.
End rwlock_RwLockReadGuard_ty.
Global Arguments rwlock_RwLockReadGuard_rt : clear implicits.
Section rwlock_RwLockReadGuard_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition rwlock_RwLockReadGuard_inv_t_inv_spec  : spec_with 1 [T_rt] (ex_inv_def ((rwlock_RwLockReadGuard_rt (T_rt)))%type (((T_rt)))%type) := spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((T_rt))%type : RT)),
            let 'x := _ty_rfn in ⌜inner_rfn = -[#(#x)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition rwlock_RwLockReadGuard_inv_t  : spec_with 1 [T_rt] (type (((T_rt)))%type) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (rwlock_RwLockReadGuard_inv_t_inv_spec   <TY> T_ty <LFT> ulft_a <INST!>) ((rwlock_RwLockReadGuard_ty (T_rt))  <TY> T_ty <LFT> ulft_a <INST!>).
  Global Typeclasses Transparent rwlock_RwLockReadGuard_inv_t.
  Definition rwlock_RwLockReadGuard_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty rwlock_RwLockReadGuard_inv_t in exact __a. Defined.
  Global Typeclasses Transparent rwlock_RwLockReadGuard_inv_t_rt.
End rwlock_RwLockReadGuard_inv_t.
Global Arguments rwlock_RwLockReadGuard_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition relax_Spinasrelax_RelaxStrategy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((relax_RelaxStrategy_spec_attrs ((relax_Spin_rt)))) :=
  mk_relax_RelaxStrategy_spec_attrs.


End attrs.

Section rwlock_RwLock_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (R_rt : RT).


Definition rwlock_RwLock_ty  : (spec_with 0 [(T_rt); (R_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((R_rt)))) : RT; (((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ((struct_t (rwlock_RwLock_sls ((T_ty.(ty_syn_type) (MetaNone))) ((R_ty.(ty_syn_type) (MetaNone)))) +[((core_marker_PhantomData_ty ((R_rt))  <TY> R_ty <INST!>)); ((core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>))]))).
Defined.

Definition rwlock_RwLock_rt  : RT.
Proof using T_rt R_rt .
  let __a := (normalized_rt_of_spec_ty (rwlock_RwLock_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent rwlock_RwLock_ty.
#[global] Typeclasses Transparent rwlock_RwLock_rt.
End rwlock_RwLock_ty.
Global Arguments rwlock_RwLock_rt : clear implicits.
Section rwlock_RwLock_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (R_rt : RT).

  Program Definition rwlock_RwLock_inv_t_inv_spec  : spec_with 0 [T_rt; R_rt] (ex_inv_def ((rwlock_RwLock_rt (T_rt) (R_rt)))%type ((unit))%type) := spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((unit)%type : RT)),
            let '() := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z) (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(y); #(x)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition rwlock_RwLock_inv_t  : spec_with 0 [T_rt; R_rt] (type ((unit))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ex_plain_t _ _ (rwlock_RwLock_inv_t_inv_spec   <TY> T_ty <TY> R_ty <INST!>) ((rwlock_RwLock_ty (T_rt) (R_rt))  <TY> T_ty <TY> R_ty <INST!>).
  Global Typeclasses Transparent rwlock_RwLock_inv_t.
  Definition rwlock_RwLock_inv_t_rt : RT.
  Proof using T_rt R_rt . let __a := normalized_rt_of_spec_ty rwlock_RwLock_inv_t in exact __a. Defined.
  Global Typeclasses Transparent rwlock_RwLock_inv_t_rt.
End rwlock_RwLock_inv_t.
Global Arguments rwlock_RwLock_inv_t_rt : clear implicits.

Section rwlock_RwLockWriteGuard_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (R_rt : RT).


Definition rwlock_RwLockWriteGuard_ty  : (spec_with 1 [(T_rt); (R_rt)] ((type (plist place_rfnRT [(place_rfnRT ((rwlock_RwLock_inv_t_rt ((T_rt)) ((relax_Spin_rt))))) : RT; (R_rt) : RT])))).
Proof.
  exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ((struct_t (rwlock_RwLockWriteGuard_sls ((T_ty.(ty_syn_type) (MetaNone))) ((R_ty.(ty_syn_type) (MetaNone)))) +[((shr_ref ulft_a (rwlock_RwLock_inv_t ((T_rt)) ((relax_Spin_rt))   <TY> T_ty <TY> (relax_Spin_ty   <INST!>) <INST!>))); (R_ty)]))).
Defined.

Definition rwlock_RwLockWriteGuard_rt  : RT.
Proof using T_rt R_rt .
  let __a := (normalized_rt_of_spec_ty (rwlock_RwLockWriteGuard_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent rwlock_RwLockWriteGuard_ty.
#[global] Typeclasses Transparent rwlock_RwLockWriteGuard_rt.
End rwlock_RwLockWriteGuard_ty.
Global Arguments rwlock_RwLockWriteGuard_rt : clear implicits.
Section rwlock_RwLockWriteGuard_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (R_rt : RT).

  Program Definition rwlock_RwLockWriteGuard_inv_t_inv_spec  : spec_with 1 [T_rt; R_rt] (ex_inv_def ((rwlock_RwLockWriteGuard_rt (T_rt) (R_rt)))%type ((place_rfn (T_rt)))%type) := spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((place_rfn (T_rt))%type : RT)),
            let 'x := _ty_rfn in ∃ (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(#tt); #(y)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition rwlock_RwLockWriteGuard_inv_t  : spec_with 1 [T_rt; R_rt] (type ((place_rfn (T_rt)))%type) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ex_plain_t _ _ (rwlock_RwLockWriteGuard_inv_t_inv_spec   <TY> T_ty <TY> R_ty <LFT> ulft_a <INST!>) ((rwlock_RwLockWriteGuard_ty (T_rt) (R_rt))  <TY> T_ty <TY> R_ty <LFT> ulft_a <INST!>).
  Global Typeclasses Transparent rwlock_RwLockWriteGuard_inv_t.
  Definition rwlock_RwLockWriteGuard_inv_t_rt : RT.
  Proof using T_rt R_rt . let __a := normalized_rt_of_spec_ty rwlock_RwLockWriteGuard_inv_t in exact __a. Defined.
  Global Typeclasses Transparent rwlock_RwLockWriteGuard_inv_t_rt.
End rwlock_RwLockWriteGuard_inv_t.
Global Arguments rwlock_RwLockWriteGuard_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (R_rt: RT) : ((Deref_spec_attrs (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)))) :=
  {|
    Deref_DerefInto  :=
      (id) : ((Deref_DerefInto_sig (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (R_rt: RT) : ((DerefMut_spec_attrs (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt)))))) :=
  {|
    DerefMut_DerefMutInject  :=
      (λ old γ, 👻 γ) : ((DerefMut_DerefMutInject_sig (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt))))));
  |}
.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

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

Definition relax_RelaxStrategy_relax_base_spec (Self_rt: RT) (Self_st: syn_type) (relax_RelaxStrategy_Self_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ unit_t;
      (* postcondition *) (λ π : thread_id, True).

Definition relax_RelaxStrategy_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((relax_RelaxStrategy_spec_attrs ((Self_rt))))) : (spec_with _ _ (relax_RelaxStrategy_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      relax_RelaxStrategy_relax_spec  :=
        (relax_RelaxStrategy_relax_base_spec ((Self_rt)) (Self_st)) _ATTRS 
           <TY> Self_ty : (spec_with 0 [] fn_spec);
    |}
.

End relax_RelaxStrategy.

Section relax_RelaxStrategy_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_relax_RelaxStrategy_relax (Self_rt: RT) (Self_st: syn_type) (relax_RelaxStrategy_Self_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (Self_rt) )) (relax_RelaxStrategy_Self_spec: (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl relax_RelaxStrategy_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (Self_rt) Self_st relax_RelaxStrategy_Self_spec_attrs<TY> Self_ty <INST!>)))).
End relax_RelaxStrategy_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.


Definition trait_incl_of_relax_Spinasrelax_RelaxStrategy_relax  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_relax_Spinasrelax_RelaxStrategy_relax  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ unit_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_deref (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_rwlock; ulft_2]) : 2 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_deref (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) :=
  spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT),((Deref_base_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuard_st (T_st) (R_st))) (T_st) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs (T_rt) (R_rt))))
     <TY> (rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <LFT> ulft_rwlock <INST!>) <TY> T_ty <INST!>).(Deref_deref_spec)   <MERGE!>.

Definition trait_incl_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_deref_mut (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_rwlock; ulft_2]) : 2 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_deref_mut (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) :=
  spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT),((DerefMut_base_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)) ((rwlock_RwLockWriteGuard_st (T_st) (R_st))) (T_st) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt)))) ((rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_attrs (T_rt) (R_rt))))
     <TY> (rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <LFT> ulft_rwlock <INST!>) <TY> T_ty <INST!>).(DerefMut_deref_mut_spec)   <MERGE!>.

Definition trait_incl_of_once_Once_TR_call_once (T_rt: RT) (R_rt: RT) (F_rt: RT) (T_st: syn_type) (R_st: syn_type) (F_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_spec: (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (R_rt)))) (FnOnce_F_unit_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) unit (T_rt) )) (FnOnce_F_unit_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) unit (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty; F_ty]) : ([T_rt; R_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl relax_RelaxStrategy_R_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (R_rt) R_st relax_RelaxStrategy_R_spec_attrs<TY> R_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_unit_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) unit (T_rt) F_st UnitSynType T_st FnOnce_F_unit_spec_attrs<TY> F_ty <TY> unit_t <TY> T_ty <INST!>)))).

Definition type_of_once_Once_TR_call_once (T_rt: RT) (R_rt: RT) (F_rt: RT) (T_st: syn_type) (R_st: syn_type) (F_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (FnOnce_F_unit_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) unit (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty; F_ty]) : ([(T_rt, T_st); (R_rt, R_st); (F_rt, F_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (p, self, f) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (once_Once_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>)), f :@: F_ty;
      (* precondition. *) (λ π : thread_id, (FnOnce_F_unit_spec_attrs.(FnOnce_Pre) π p f ())
        ∗ (once_status_tok self None)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (x) : ((_)), x @ (shr_ref ulft_1 T_ty);
      (* postcondition *) (λ π : thread_id, (FnOnce_F_unit_spec_attrs.(FnOnce_Post) π p f () x)
      ∗ (once_status_tok self (Some x))).

Definition trait_incl_of_once_Once_TR_get (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_once_Once_TR_get (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (o, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (once_Once_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>));
      (* precondition. *) (λ π : thread_id, (once_status_tok self o)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, o @ (Option_ty ((place_rfnRT (T_rt)))  <TY> (shr_ref ulft_1 T_ty) <INST!>);
      (* postcondition *) (λ π : thread_id, (once_status_tok self o)).

Definition trait_incl_of_once_Once_TR_initialized (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_once_Once_TR_initialized (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (data) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) data :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (η) : ((_)), η @ (once_Once_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (once_status_tok η (Some data))).

Definition trait_incl_of_once_Once_TR_is_completed (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_once_Once_TR_is_completed (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (o, self) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (once_Once_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>));
      (* precondition. *) (λ π : thread_id, (once_status_tok self o)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_Some o) @ bool_t;
      (* postcondition *) (λ π : thread_id, (once_status_tok self o)).

Definition trait_incl_of_once_Once_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_once_Once_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) `{!(onceG Σ ((RT_xt (T_rt))))} :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (once_Once_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (once_status_tok ret None)).

Definition trait_incl_of_rwlock_RwLock_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (True).

Definition type_of_rwlock_RwLock_TR_new (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (t) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) t :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ (rwlock_RwLock_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLock_TR_read (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_spec: (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (R_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ((trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl relax_RelaxStrategy_R_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (R_rt) R_st relax_RelaxStrategy_R_spec_attrs<TY> R_ty <INST!>)))).

Definition type_of_rwlock_RwLock_TR_read (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (rwlock_RwLock_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (rwlock_RwLockReadGuard_inv_t ((T_rt))   <TY> T_ty <LFT> ulft_1 <INST!>);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_rwlock_RwLock_TR_write (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) (relax_RelaxStrategy_R_spec: (spec_with 0 [] (relax_RelaxStrategy_spec (RRGS:=RRGS) (R_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), ((trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl relax_RelaxStrategy_R_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_RelaxStrategy_base_spec (R_rt) R_st relax_RelaxStrategy_R_spec_attrs<TY> R_ty <INST!>)))).

Definition type_of_rwlock_RwLock_TR_write (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) (relax_RelaxStrategy_R_spec_attrs: (relax_RelaxStrategy_spec_attrs (RRGS:=RRGS) (R_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; R_ty]) : ([(T_rt, T_st); (R_rt, R_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (rwlock_RwLock_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <INST!>));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <LFT> ulft_1 <INST!>);
      (* postcondition *) (λ π : thread_id, True).



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
  Definition relax_Spinasrelax_RelaxStrategy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl relax_RelaxStrategy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), relax_Spinasrelax_RelaxStrategy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (relax_RelaxStrategy_base_spec (relax_Spin_rt) relax_Spin_st relax_Spinasrelax_RelaxStrategy_spec_attrs<TY> (relax_Spin_ty   <INST!>) <INST!>))).
End relax_Spinasrelax_RelaxStrategy_spec.

Section rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) : (spec_with _ _ (Deref_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)))) :=
    spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), let Target_rt := (T_rt) in {|
        Deref_deref_spec  :=
          (type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_deref ((T_rt)) ((R_rt)) (T_st) (R_st)) 
             <TY> T_ty <TY> R_ty <LFT> ulft_rwlock : (spec_with 1 [] fn_spec);
      |}
  .
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(R_rt : !RT) `(T_st : !syn_type) `(R_st : !syn_type), trait_incl_marker (lift_trait_incl Deref_spec_incl (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec (T_rt) (R_rt) (T_st) (R_st)) <TY> T_ty <TY> R_ty <LFT> ulft_rwlock <INST!>) (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (Deref_base_spec ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (T_rt) (rwlock_RwLockWriteGuard_st (T_st) (R_st)) T_st (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs (T_rt) (R_rt))<TY> (rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <LFT> ulft_rwlock <INST!>) <TY> T_ty <INST!>))).
End rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec.

Section rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec (T_rt: RT) (R_rt: RT) (T_st: syn_type) (R_st: syn_type) : (spec_with _ _ (DerefMut_spec (((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt))))) ((T_rt)))) :=
    spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), {|
        DerefMut_deref_mut_spec  :=
          (type_of_rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_deref_mut ((T_rt)) ((R_rt)) (T_st) (R_st)) 
             <TY> T_ty <TY> R_ty <LFT> ulft_rwlock : (spec_with 1 [] fn_spec);
      |}
  .
  Definition rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(R_rt : !RT) `(T_st : !syn_type) `(R_st : !syn_type), trait_incl_marker (lift_trait_incl DerefMut_spec_incl (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec (T_rt) (R_rt) (T_st) (R_st)) <TY> T_ty <TY> R_ty <LFT> ulft_rwlock <INST!>) (spec! ( *[ulft_rwlock]) : 1 | ( *[T_ty; R_ty]) : ([T_rt; R_rt] : list RT), (DerefMut_base_spec ((rwlock_RwLockWriteGuard_inv_t_rt ((T_rt)) ((R_rt)))) (T_rt) (rwlock_RwLockWriteGuard_st (T_st) (R_st)) T_st (rwlock_RwLockWriteGuardrwlockTRasstd_ops_Deref_spec_attrs ((T_rt)) ((R_rt))) (rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec_attrs (T_rt) (R_rt))<TY> (rwlock_RwLockWriteGuard_inv_t ((T_rt)) ((R_rt))   <TY> T_ty <TY> R_ty <LFT> ulft_rwlock <INST!>) <TY> T_ty <INST!>))).
End rwlock_RwLockWriteGuardrwlockTRasstd_ops_DerefMut_spec.

