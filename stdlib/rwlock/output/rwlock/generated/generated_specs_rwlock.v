From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.rwlock.rwlock Require Export generated_code_rwlock.

Section RwLock_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition RwLock_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (RwLock_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))]))).
Defined.

Definition RwLock_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (RwLock_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent RwLock_ty.
#[global] Typeclasses Transparent RwLock_rt.
End RwLock_ty.
Global Arguments RwLock_rt : clear implicits.
Section RwLock_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition RwLock_inv_t_inv_spec  : spec_with 0 [T_rt] (ex_inv_def ((RwLock_rt (T_rt)))%type ((unit))%type) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((unit)%type : RT)),
            let '() := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z), ⌜inner_rfn = -[#(x)]⌝ ∗ True)%I
    (true)
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition RwLock_inv_t  : spec_with 0 [T_rt] (type ((unit))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (RwLock_inv_t_inv_spec  -[] -[T_ty]) ((RwLock_ty (T_rt)) -[] -[T_ty]).
Global Arguments RwLock_inv_t_inv_spec : simpl never.
Global Arguments RwLock_inv_t : simpl never.
  Global Typeclasses Transparent RwLock_inv_t.
  Definition RwLock_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty RwLock_inv_t in exact __a. Defined.
  Global Typeclasses Transparent RwLock_inv_t_rt.
End RwLock_inv_t.
Global Arguments RwLock_inv_t_rt : clear implicits.

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
      (* postcondition *) (λ π : thread_id, True).



End specs.
