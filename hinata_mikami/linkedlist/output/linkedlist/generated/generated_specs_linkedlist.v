From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist Require Export generated_code_linkedlist.
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


Definition Node_ty  : (spec_with 0 [] ((type (plist place_rfnRT [Z : RT; loc : RT; bool : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t Node_sls +[((int I32)); (alias_ptr_t); (bool_t)]))).
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

  Program Definition Node_inv_t_inv_spec  : spec_with 0 [] (ex_inv_def (Node_rt)%type (((Z * loc * bool)))%type) := spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((Z * loc * bool))%type : RT)),
            let '(v, n, m) := _ty_rfn in ⌜inner_rfn = -[#(v); #(n); #(m)]⌝ ∗ 
  (
    ⌜n = (Loc ProvNone 0)⌝
    ∨
    ∃ (v' : Z) (n' : loc) (m' : bool),
        n ◁ₗ[ π, Owned] # -[# v'; # n'; # m'] @
         (◁ (Node_ty <INST!>))
  )
 ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition Node_inv_t  : spec_with 0 [] (type (((Z * loc * bool)))%type) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (Node_inv_t_inv_spec   <INST!>) (Node_ty  <INST!>).
  Global Typeclasses Transparent Node_inv_t.
  Definition Node_inv_t_rt : RT.
  Proof using  . let __a := normalized_rt_of_spec_ty Node_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Node_inv_t_rt.
End Node_inv_t.
Global Arguments Node_inv_t_rt : clear implicits.

Section Heap_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition Heap_ty  : (spec_with 0 [] ((type (plist place_rfnRT [((((Vec_inv_t_rt)) (loc) ((((Global_rt)))))) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t Heap_sls +[((Vec_inv_t (loc) ((((Global_rt)))) GlobalasAllocator_spec_attrs  <TY> alias_ptr_t <TY> (Global_ty   <INST!>) <INST!>))]))).
Defined.

Definition Heap_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (Heap_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Heap_ty.
#[global] Typeclasses Transparent Heap_rt.
End Heap_ty.
Global Arguments Heap_rt : clear implicits.
Section Heap_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.

  Program Definition Heap_inv_t_inv_spec  : spec_with 0 [] (ex_inv_def (Heap_rt)%type (_)%type) := spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (_%type : RT)),
            let 'all_nodes := _ty_rfn in ⌜inner_rfn = -[#(all_nodes)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition Heap_inv_t  : spec_with 0 [] (type (_)%type) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (Heap_inv_t_inv_spec   <INST!>) (Heap_ty  <INST!>).
  Global Typeclasses Transparent Heap_inv_t.
  Definition Heap_inv_t_rt : RT.
  Proof using  . let __a := normalized_rt_of_spec_ty Heap_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Heap_inv_t_rt.
End Heap_inv_t.
Global Arguments Heap_inv_t_rt : clear implicits.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_Heap_alloc  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_Heap_alloc  :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (l, v) : ((_ * (Z))),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) l :@: (mut_ref ulft_1 (Heap_inv_t    <INST!>)), v :@: (int I32);
      (* precondition. *) (λ π : thread_id, (⌜(length l.cur < MaxInt usize)%Z⌝)
        ∗ (⌜(size_of_array_in_bytes (PtrSynType) (2 * length l.cur) ≤ MaxInt isize)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ptr) : (((loc))), ptr @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs l.ghost (<$#>(l.cur ++ [ptr])))
      ∗ (ptr ◁ₗ[π, Owned] #((v, (Loc ProvNone 0), false)) @ (◁ (Node_inv_t <INST!>)))).

Definition trait_incl_of_Node_set_next  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_Node_set_next  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (node, next, v, old_next, m) : (((loc) * (loc) * (Z) * (loc) * (bool))),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) node :@: alias_ptr_t, next :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (node ◁ₗ[π, Owned] #((v, old_next, m)) @ (◁ (Node_inv_t <INST!>)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, () @ unit_t;
      (* postcondition *) (λ π : thread_id, (
            node ◁ₗ[π, Owned] # -[# v; # next; # m] @
              (◁ struct_t Node_sls +[◁ int i32; alias_ptr_t; ◁ bool_t])
          )).

Definition trait_incl_of_Heap_new  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_Heap_new  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, [] @ (Heap_inv_t    <INST!>);
      (* postcondition *) (λ π : thread_id, True).




End specs.
