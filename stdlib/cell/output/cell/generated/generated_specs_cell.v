From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.cell.cell Require Export generated_code_cell.

Section UnsafeCell_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition UnsafeCell_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [(T_rt) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (UnsafeCell_sls ((ty_syn_type T_ty MetaNone))) +[(T_ty)])).
  Defined.

  Definition UnsafeCell_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (UnsafeCell_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent UnsafeCell_rt.
  #[global] Typeclasses Transparent UnsafeCell_ty.
End UnsafeCell_ty.
#[global] Arguments UnsafeCell_rt : clear implicits.

#[global] Arguments UnsafeCell_ty : clear implicits.

#[global] Arguments UnsafeCell_ty {_ _} _  .

Section UnsafeCell_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition UnsafeCell_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def ((UnsafeCell_rt (T_rt)))%type (((T_rt)))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π inner_rfn (_ty_rfn : RT_rt (((T_rt))%type : RT)),
                  let 'x := _ty_rfn in ⌜inner_rfn = -[#(x)]⌝ ∗ True)%I
          (false)
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

  Definition UnsafeCell_inv_t  : (spec_with 0 [(T_rt)] ((type ((((T_rt)))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (UnsafeCell_inv_t_inv_spec  -[] -[T_ty]) ((UnsafeCell_ty (T_rt)) -[] -[T_ty]).
  #[global] Arguments UnsafeCell_inv_t_inv_spec : simpl never.

  #[global] Arguments UnsafeCell_inv_t : simpl never.

  #[global] Typeclasses Transparent UnsafeCell_inv_t.
  Definition UnsafeCell_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (UnsafeCell_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent UnsafeCell_inv_t_rt.
End UnsafeCell_inv_t.
#[global] Arguments UnsafeCell_inv_t_rt : clear implicits.

#[global] Arguments UnsafeCell_inv_t : clear implicits.

#[global] Arguments UnsafeCell_inv_t {_ _} _  .

#[global] Arguments UnsafeCell_inv_t_inv_spec : clear implicits.

#[global] Arguments UnsafeCell_inv_t_inv_spec {_ _} _  .


Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition drop_glue_UnsafeCell_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((DropGlue_spec_attrs (((UnsafeCell_inv_t_rt ((T_rt))))))) :=
  {|
    DropGlue_DropGlueUnwind  :=
      (DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind)) : ((DropGlue_DropGlueUnwind_sig (((UnsafeCell_inv_t_rt ((T_rt)))))));
  |}
.


End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_drop_glue_UnsafeCell (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_drop_glue_UnsafeCell (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((UnsafeCell_inv_t_rt ((T_rt))))) ((UnsafeCell_st (T_st))) ((drop_glue_UnsafeCell_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(UnsafeCell_inv_t ((T_rt))  -[] -[T_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.




End specs.
Section drop_glue_UnsafeCell_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_UnsafeCell_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (DropGlue_spec (((UnsafeCell_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_UnsafeCell ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition drop_glue_UnsafeCell_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (drop_glue_UnsafeCell_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((DropGlue_base_spec ((UnsafeCell_inv_t_rt ((T_rt)))) (UnsafeCell_st (T_st)) (drop_glue_UnsafeCell_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(UnsafeCell_inv_t ((T_rt))  -[] -[T_ty])])))).
End drop_glue_UnsafeCell_spec.

