From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.raw_ptr_tst Require Export generated_code_raw_ptr_tst.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.alloc.vec.generated Require Export generated_specs_vec.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.boxed.boxed.generated Require Export generated_specs_boxed.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.stdlib.stdlib.generated Require Export generated_specs_stdlib.

Section Node_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition Node_ty  : (spec_with 0 [] ((type (plist place_rfnRT [Z : RT; loc : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t Node_sls +[((int I32)); (alias_ptr_t)]))).
Defined.

Definition Node_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (Node_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Node_ty.
#[global] Typeclasses Transparent Node_rt.
End Node_ty.
Global Arguments Node_rt : clear implicits.
Section Node_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.

  Program Definition Node_inv_t_inv_spec  : spec_with 0 [] (ex_inv_def (Node_rt)%type (((Z * loc)))%type) := spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((Z * loc))%type : RT)),
            let '(v, l) := _ty_rfn in ⌜inner_rfn = -[#(v); #(l)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition Node_inv_t  : spec_with 0 [] (type (((Z * loc)))%type) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (Node_inv_t_inv_spec   <INST!>) (Node_ty  <INST!>).
  Global Typeclasses Transparent Node_inv_t.
  Definition Node_inv_t_rt : RT.
  Proof using  . let __a := normalized_rt_of_spec_ty Node_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Node_inv_t_rt.
End Node_inv_t.
Global Arguments Node_inv_t_rt : clear implicits.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_id  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_id  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v) : ((_ * (Z))),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) p :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (p ◁ₗ[π, Owned] #(v) @ (◁ int i32))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, p @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (p ◁ₗ[π, Owned] #(v) @ (◁ int i32))).

Definition trait_incl_of_Node_set_next  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_Node_set_next  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v, l, n) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) p :@: alias_ptr_t, n :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (p ◁ₗ[π, Owned] #((v, l)) @ (◁ (Node_inv_t <INST!>)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ unit_t;
      (* postcondition *) (λ π : thread_id, (⌜(p ◁ₗ[π, Owned] # -[# v; # n] @ StructLtype +[◁ int i32; ◁ alias_ptr_t] Node_sls)%Z⌝)).

Definition trait_incl_of_id_Cell  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_id_Cell  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) p :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (p ◁ₗ[π, Owned] #(v) @ (◁ int i32))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, p @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (p ◁ₗ[π, Owned] #(v) @ (◁ int i32))).

Definition trait_incl_of_Node_id_Node  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_Node_id_Node  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v, l) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) p :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (p ◁ₗ[π, Owned] #((v, l)) @ (◁ (Node_inv_t <INST!>)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, p @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (p ◁ₗ[π, Owned] #((v, l)) @ (◁ (Node_inv_t <INST!>)))).




End specs.
