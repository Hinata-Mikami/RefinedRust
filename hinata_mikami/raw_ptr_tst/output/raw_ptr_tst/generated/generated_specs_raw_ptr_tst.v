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

Definition trait_incl_of_id_Node  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_id_Node  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (p, v, l) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) p :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (p ◁ₗ[π, Owned] #((v, l)) @ (◁ (Node_inv_t <INST!>)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, p @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (p ◁ₗ[π, Owned] #((v, l)) @ (◁ (Node_inv_t <INST!>)))).




End specs.
