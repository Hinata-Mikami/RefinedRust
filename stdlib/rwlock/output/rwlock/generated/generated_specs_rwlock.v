From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.rwlock.rwlock Require Export generated_code_rwlock.

Section RwLock_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition RwLock_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (RwLock_sls ((ty_syn_type T_ty MetaNone))) +[((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))])).
  Defined.

  Definition RwLock_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (RwLock_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent RwLock_rt.
  #[global] Typeclasses Transparent RwLock_ty.
End RwLock_ty.
#[global] Arguments RwLock_rt : clear implicits.

#[global] Arguments RwLock_ty : clear implicits.

#[global] Arguments RwLock_ty {_ _} _  .

Section RwLock_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition RwLock_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def ((RwLock_rt (T_rt)))%type ((unit))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π inner_rfn (_ty_rfn : RT_rt ((unit)%type : RT)),
                  let '() := _ty_rfn in ⌜inner_rfn = -[#(tt)]⌝ ∗ True)%I
          (true)
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition RwLock_inv_t  : (spec_with 0 [(T_rt)] ((type (((unit))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (RwLock_inv_t_inv_spec  -[] -[T_ty]) ((RwLock_ty (T_rt)) -[] -[T_ty]).
  #[global] Arguments RwLock_inv_t_inv_spec : simpl never.

  #[global] Arguments RwLock_inv_t : simpl never.

  #[global] Typeclasses Transparent RwLock_inv_t.
  Definition RwLock_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (RwLock_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent RwLock_inv_t_rt.
End RwLock_inv_t.
#[global] Arguments RwLock_inv_t_rt : clear implicits.

#[global] Arguments RwLock_inv_t : clear implicits.

#[global] Arguments RwLock_inv_t {_ _} _  .

#[global] Arguments RwLock_inv_t_inv_spec : clear implicits.

#[global] Arguments RwLock_inv_t_inv_spec {_ _} _  .


Section RwLockReadGuard_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition RwLockReadGuard_ty  : (spec_with 1 [(T_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((place_rfnRT (T_rt))))) : RT])))).
  Proof.
    exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (RwLockReadGuard_sls ((ty_syn_type T_ty MetaNone))) +[((core_marker_PhantomData_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_a T_ty)]))])).
  Defined.

  Definition RwLockReadGuard_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (RwLockReadGuard_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent RwLockReadGuard_rt.
  #[global] Typeclasses Transparent RwLockReadGuard_ty.
End RwLockReadGuard_ty.
#[global] Arguments RwLockReadGuard_rt : clear implicits.

#[global] Arguments RwLockReadGuard_ty : clear implicits.

#[global] Arguments RwLockReadGuard_ty {_ _} _  .

Section RwLockReadGuard_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition RwLockReadGuard_inv_t_inv_spec  : (spec_with 1 [(T_rt)] ((ex_inv_def ((RwLockReadGuard_rt (T_rt)))%type (((T_rt)))%type))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π inner_rfn (_ty_rfn : RT_rt (((T_rt))%type : RT)),
                  let 'x := _ty_rfn in ⌜inner_rfn = -[#(tt)]⌝ ∗ True)%I
          (true)
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition RwLockReadGuard_inv_t  : (spec_with 1 [(T_rt)] ((type ((((T_rt)))%type)))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (RwLockReadGuard_inv_t_inv_spec  -[ulft_a] -[T_ty]) ((RwLockReadGuard_ty (T_rt)) -[ulft_a] -[T_ty]).
  #[global] Arguments RwLockReadGuard_inv_t_inv_spec : simpl never.

  #[global] Arguments RwLockReadGuard_inv_t : simpl never.

  #[global] Typeclasses Transparent RwLockReadGuard_inv_t.
  Definition RwLockReadGuard_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (RwLockReadGuard_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent RwLockReadGuard_inv_t_rt.
End RwLockReadGuard_inv_t.
#[global] Arguments RwLockReadGuard_inv_t_rt : clear implicits.

#[global] Arguments RwLockReadGuard_inv_t : clear implicits.

#[global] Arguments RwLockReadGuard_inv_t {_ _} _  .

#[global] Arguments RwLockReadGuard_inv_t_inv_spec : clear implicits.

#[global] Arguments RwLockReadGuard_inv_t_inv_spec {_ _} _  .


Section PoisonError_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition PoisonError_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (PoisonError_sls ((ty_syn_type T_ty MetaNone))) +[((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))])).
  Defined.

  Definition PoisonError_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (PoisonError_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent PoisonError_rt.
  #[global] Typeclasses Transparent PoisonError_ty.
End PoisonError_ty.
#[global] Arguments PoisonError_rt : clear implicits.

#[global] Arguments PoisonError_ty : clear implicits.

#[global] Arguments PoisonError_ty {_ _} _  .

Section PoisonError_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition PoisonError_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def ((PoisonError_rt (T_rt)))%type ((unit))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π inner_rfn (_ty_rfn : RT_rt ((unit)%type : RT)),
                  let '() := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z), ⌜inner_rfn = -[#(x)]⌝ ∗ True)%I
          (true)
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition PoisonError_inv_t  : (spec_with 0 [(T_rt)] ((type (((unit))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (PoisonError_inv_t_inv_spec  -[] -[T_ty]) ((PoisonError_ty (T_rt)) -[] -[T_ty]).
  #[global] Arguments PoisonError_inv_t_inv_spec : simpl never.

  #[global] Arguments PoisonError_inv_t : simpl never.

  #[global] Typeclasses Transparent PoisonError_inv_t.
  Definition PoisonError_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (PoisonError_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent PoisonError_inv_t_rt.
End PoisonError_inv_t.
#[global] Arguments PoisonError_inv_t_rt : clear implicits.

#[global] Arguments PoisonError_inv_t : clear implicits.

#[global] Arguments PoisonError_inv_t {_ _} _  .

#[global] Arguments PoisonError_inv_t_inv_spec : clear implicits.

#[global] Arguments PoisonError_inv_t_inv_spec {_ _} _  .


Section RwLockWriteGuard_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition RwLockWriteGuard_ty  : (spec_with 1 [(T_rt)] ((type (plist place_rfnRT [(place_rfnRT ((RwLock_inv_t_rt ((T_rt))))) : RT])))).
  Proof.
    exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (RwLockWriteGuard_sls ((ty_syn_type T_ty MetaNone))) +[((shr_ref ulft_a (RwLock_inv_t ((T_rt))  -[] -[T_ty])))])).
  Defined.

  Definition RwLockWriteGuard_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (RwLockWriteGuard_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent RwLockWriteGuard_rt.
  #[global] Typeclasses Transparent RwLockWriteGuard_ty.
End RwLockWriteGuard_ty.
#[global] Arguments RwLockWriteGuard_rt : clear implicits.

#[global] Arguments RwLockWriteGuard_ty : clear implicits.

#[global] Arguments RwLockWriteGuard_ty {_ _} _  .

Section RwLockWriteGuard_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition RwLockWriteGuard_inv_t_inv_spec  : (spec_with 1 [(T_rt)] ((ex_inv_def ((RwLockWriteGuard_rt (T_rt)))%type ((place_rfn (T_rt)))%type))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π inner_rfn (_ty_rfn : RT_rt ((place_rfn (T_rt))%type : RT)),
                  let 'x := _ty_rfn in ⌜inner_rfn = -[#(#tt)]⌝ ∗ True)%I
          (true)
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition RwLockWriteGuard_inv_t  : (spec_with 1 [(T_rt)] ((type (((place_rfn (T_rt)))%type)))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (RwLockWriteGuard_inv_t_inv_spec  -[ulft_a] -[T_ty]) ((RwLockWriteGuard_ty (T_rt)) -[ulft_a] -[T_ty]).
  #[global] Arguments RwLockWriteGuard_inv_t_inv_spec : simpl never.

  #[global] Arguments RwLockWriteGuard_inv_t : simpl never.

  #[global] Typeclasses Transparent RwLockWriteGuard_inv_t.
  Definition RwLockWriteGuard_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (RwLockWriteGuard_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent RwLockWriteGuard_inv_t_rt.
End RwLockWriteGuard_inv_t.
#[global] Arguments RwLockWriteGuard_inv_t_rt : clear implicits.

#[global] Arguments RwLockWriteGuard_inv_t : clear implicits.

#[global] Arguments RwLockWriteGuard_inv_t {_ _} _  .

#[global] Arguments RwLockWriteGuard_inv_t_inv_spec : clear implicits.

#[global] Arguments RwLockWriteGuard_inv_t_inv_spec {_ _} _  .


Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.


Definition trait_incl_of_RwLock_T_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st-[] -[T_ty])))).

Definition type_of_RwLock_T_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ (RwLock_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.



End specs.
