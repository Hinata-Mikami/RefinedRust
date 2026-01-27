From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tst2 Require Export generated_code_tst2.

Section Data_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition Data_ty  : (spec_with 0 [] ((type (plist place_rfnRT [Z : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t Data_sls +[((int I32))]))).
Defined.

Definition Data_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (Data_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Data_ty.
#[global] Typeclasses Transparent Data_rt.
End Data_ty.
Global Arguments Data_rt : clear implicits.
Section Data_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.

  Program Definition Data_inv_t_inv_spec  : spec_with 0 [] (ex_inv_def (Data_rt)%type ((Z))%type) := spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((Z)%type : RT)), 
            let 'x := _ty_rfn in ⌜inner_rfn = -[#(x)]⌝ ∗ True)%I
    (λ π κ inner_rfn (_ty_rfn : RT_rt ((Z)%type : RT)), 
            let 'x := _ty_rfn in ⌜inner_rfn = -[#(x)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition Data_inv_t  : spec_with 0 [] (type ((Z))%type) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (Data_inv_t_inv_spec   <INST!>) (Data_ty  <INST!>).
  Global Typeclasses Transparent Data_inv_t.
  Definition Data_inv_t_rt : RT.
  Proof using  . let __a := normalized_rt_of_spec_ty Data_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Data_inv_t_rt.
End Data_inv_t.
Global Arguments Data_inv_t_rt : clear implicits.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_main  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_main  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) _ : (unit),
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), () @ unit_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_id_data  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_id_data  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (d) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) d :@: (Data_inv_t    <INST!>);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), d @ (Data_inv_t    <INST!>);
      (* postcondition *) (λ π : thread_id, True).




End specs.
