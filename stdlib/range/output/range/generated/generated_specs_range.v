From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range Require Export generated_code_range.

Section Range_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {Idx_rt : RT}.
  Definition Range_ty  : (spec_with 0 [(Idx_rt)] ((type (plist place_rfnRT [(Idx_rt) : RT; (Idx_rt) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), (struct_t (Range_sls ((ty_syn_type Idx_ty MetaNone))) +[(Idx_ty); (Idx_ty)])).
  Defined.

  Definition Range_rt  : RT.
  Proof using Idx_rt .
    let __a := (normalized_rt_of_spec_ty (Range_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Range_rt.
  #[global] Typeclasses Transparent Range_ty.
End Range_ty.
#[global] Arguments Range_rt : clear implicits.

#[global] Arguments Range_ty : clear implicits.

#[global] Arguments Range_ty {_ _} _  .

Section Range_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {Idx_rt : RT}.
  Program Definition Range_inv_t_inv_spec  : (spec_with 0 [(Idx_rt)] ((ex_inv_def ((Range_rt (Idx_rt)))%type (((Idx_rt) * (Idx_rt)))%type))) :=
    spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), mk_auto_ex_inv_def
          (λ π inner_rfn (_ty_rfn : RT_rt (((Idx_rt) * (Idx_rt))%type : RT)),
                  let '(rstart, rend) := _ty_rfn in ⌜inner_rfn = -[#(rstart); #(rend)]⌝ ∗ True)%I
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

  Definition Range_inv_t  : (spec_with 0 [(Idx_rt)] ((type ((((Idx_rt) * (Idx_rt)))%type)))) :=
    spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), ex_plain_t _ _ (Range_inv_t_inv_spec  -[] -[Idx_ty]) ((Range_ty (Idx_rt)) -[] -[Idx_ty]).
  #[global] Arguments Range_inv_t_inv_spec : simpl never.

  #[global] Arguments Range_inv_t : simpl never.

  #[global] Typeclasses Transparent Range_inv_t.
  Definition Range_inv_t_rt  : RT.
  Proof using Idx_rt .
    let __a := (normalized_rt_of_spec_ty (Range_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Range_inv_t_rt.
End Range_inv_t.
#[global] Arguments Range_inv_t_rt : clear implicits.

#[global] Arguments Range_inv_t : clear implicits.

#[global] Arguments Range_inv_t {_ _} _  .

#[global] Arguments Range_inv_t_inv_spec : clear implicits.

#[global] Arguments Range_inv_t_inv_spec {_ _} _  .


Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition drop_glue_Range_spec_attrs `{RRGS : !(refinedrustGS Σ)} (Idx_rt: RT) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) : ((DropGlue_spec_attrs (((Range_inv_t_rt ((Idx_rt))))))) :=
  {|
    DropGlue_DropGlueUnwind  :=
      (DropGlue_Idx_spec_attrs.(DropGlue_DropGlueUnwind)) : ((DropGlue_DropGlueUnwind_sig (((Range_inv_t_rt ((Idx_rt)))))));
  |}
.


End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_Range_Idx_is_empty (Idx_rt: RT) (Idx_st: syn_type) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_Idx_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Idx_rt)))) (PartialEq_Idx_Idx_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) )) (PartialEq_Idx_Idx_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Idx_rt) (Idx_rt)))) (PartialOrd_Idx_Idx_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) PartialEq_Idx_Idx_spec_attrs)) (PartialOrd_Idx_Idx_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Idx_rt) (Idx_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[Idx_ty]) : ([Idx_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Idx_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Idx_rt) Idx_st DropGlue_Idx_spec_attrs-[] -[Idx_ty]))) ∧ (trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Idx_Idx_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Idx_rt) (Idx_rt) Idx_st Idx_st DropGlue_Idx_spec_attrs DropGlue_Idx_spec_attrs PartialEq_Idx_Idx_spec_attrs-[] -[Idx_ty; Idx_ty]))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Idx_Idx_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Idx_rt) (Idx_rt) Idx_st Idx_st PartialEq_Idx_Idx_spec_attrs DropGlue_Idx_spec_attrs DropGlue_Idx_spec_attrs PartialOrd_Idx_Idx_spec_attrs-[] -[Idx_ty; Idx_ty])))).

Definition type_of_Range_Idx_is_empty (Idx_rt: RT) (Idx_st: syn_type) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (PartialEq_Idx_Idx_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) )) (PartialOrd_Idx_Idx_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) PartialEq_Idx_Idx_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Idx_ty]) : ([(Idx_rt, Idx_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (Range_inv_t ((Idx_rt))  -[] -[Idx_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (¬ PartialOrd_Idx_Idx_spec_attrs.(PartialOrd_POrd) self.1 self.2 = Some Less) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_drop_glue_Range (Idx_rt: RT) (Idx_st: syn_type) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) (DropGlue_Idx_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (Idx_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_Idx_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (Idx_rt) Idx_st DropGlue_Idx_spec_attrs-[] -[Idx_ty])))).

Definition type_of_drop_glue_Range (Idx_rt: RT) (Idx_st: syn_type) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) :=
  spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT),(λ a b, scope_add_typarams _ -[Idx_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((Range_inv_t_rt ((Idx_rt))))) ((Range_st (Idx_st))) ((drop_glue_Range_spec_attrs (Idx_rt) (DropGlue_Idx_spec_attrs))))
    -[] -[(Range_inv_t ((Idx_rt))  -[] -[Idx_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.




End specs.
Section drop_glue_Range_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_Range_spec (Idx_rt: RT) (Idx_st: syn_type) (DropGlue_Idx_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )) : (spec_with _ _ (DropGlue_spec (((Range_inv_t_rt ((Idx_rt))))))) :=
    spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_Range ((Idx_rt)) (Idx_st)) DropGlue_Idx_spec_attrs 
             <TY> Idx_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition drop_glue_Range_spec_subsumption  :=
    ∀ `(Idx_rt : !RT) `(Idx_st : !syn_type) `(DropGlue_Idx_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (Idx_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), (drop_glue_Range_spec (Idx_rt) (Idx_st) (DropGlue_Idx_spec_attrs))-[] -[Idx_ty]) (spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), scope_add_typarams _ -[Idx_ty] ((DropGlue_base_spec ((Range_inv_t_rt ((Idx_rt)))) (Range_st (Idx_st)) (drop_glue_Range_spec_attrs (Idx_rt) (DropGlue_Idx_spec_attrs))-[] -[(Range_inv_t ((Idx_rt))  -[] -[Idx_ty])])))).
End drop_glue_Range_spec.

