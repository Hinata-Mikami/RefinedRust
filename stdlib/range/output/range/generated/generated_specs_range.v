From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range Require Export generated_code_range.

Section Range_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (Idx_rt : RT).


Definition Range_ty  : (spec_with 0 [(Idx_rt)] ((type (plist place_rfnRT [(Idx_rt) : RT; (Idx_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), ((struct_t (Range_sls ((Idx_ty.(ty_syn_type) (MetaNone)))) +[(Idx_ty); (Idx_ty)]))).
Defined.

Definition Range_rt  : RT.
Proof using Idx_rt .
  let __a := (normalized_rt_of_spec_ty (Range_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Range_ty.
#[global] Typeclasses Transparent Range_rt.
End Range_ty.
Global Arguments Range_rt : clear implicits.
Section Range_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (Idx_rt : RT).

  Program Definition Range_inv_t_inv_spec  : spec_with 0 [Idx_rt] (ex_inv_def ((Range_rt (Idx_rt)))%type (((Idx_rt) * (Idx_rt)))%type) := spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((Idx_rt) * (Idx_rt))%type : RT)),
            let '(rstart, rend) := _ty_rfn in ⌜inner_rfn = -[#(rstart); #(rend)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition Range_inv_t  : spec_with 0 [Idx_rt] (type (((Idx_rt) * (Idx_rt)))%type) :=
    spec! ( *[]) : 0 | ( *[Idx_ty]) : ([Idx_rt] : list RT), ex_plain_t _ _ (Range_inv_t_inv_spec   <TY> Idx_ty <INST!>) ((Range_ty (Idx_rt))  <TY> Idx_ty <INST!>).
  Global Typeclasses Transparent Range_inv_t.
  Definition Range_inv_t_rt : RT.
  Proof using Idx_rt . let __a := normalized_rt_of_spec_ty Range_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Range_inv_t_rt.
End Range_inv_t.
Global Arguments Range_inv_t_rt : clear implicits.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_Range_Idx_is_empty (Idx_rt: RT) (Idx_st: syn_type) (PartialEq_Idx_Idx_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) )) (PartialEq_Idx_Idx_spec: (spec_with 0 [] (PartialEq_spec (RRGS:=RRGS) (Idx_rt) (Idx_rt)))) (PartialOrd_Idx_Idx_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) PartialEq_Idx_Idx_spec_attrs)) (PartialOrd_Idx_Idx_spec: (spec_with 0 [] (PartialOrd_spec (RRGS:=RRGS) (Idx_rt) (Idx_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[Idx_ty]) : ([Idx_rt] : list RT), ((trait_incl_marker (lift_trait_incl PartialEq_spec_incl PartialEq_Idx_Idx_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialEq_base_spec (Idx_rt) (Idx_rt) Idx_st Idx_st PartialEq_Idx_Idx_spec_attrs<TY> Idx_ty <TY> Idx_ty <INST!>))) ∧ (trait_incl_marker (lift_trait_incl PartialOrd_spec_incl PartialOrd_Idx_Idx_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), PartialOrd_base_spec (Idx_rt) (Idx_rt) Idx_st Idx_st PartialEq_Idx_Idx_spec_attrs PartialOrd_Idx_Idx_spec_attrs<TY> Idx_ty <TY> Idx_ty <INST!>)))).

Definition type_of_Range_Idx_is_empty (Idx_rt: RT) (Idx_st: syn_type) (PartialEq_Idx_Idx_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) )) (PartialOrd_Idx_Idx_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Idx_rt) (Idx_rt) PartialEq_Idx_Idx_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Idx_ty]) : ([(Idx_rt, Idx_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (Range_inv_t ((Idx_rt))   <TY> Idx_ty <INST!>));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (¬ PartialOrd_Idx_Idx_spec_attrs.(PartialOrd_POrd) self.1 self.2 = Some Less) @ bool_t;
      (* postcondition *) (λ π : thread_id, True).




End specs.
