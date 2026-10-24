From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* Avoid the admitted Vec ghost resolvers in the upstream specifications.
   These functions carry concrete element refinements and need no resolution. *)
#[local] Remove Hints
  generated_specs_vec.resolve_ghost_Vec_T_owned_inst
  generated_specs_vec.resolve_ghost_Vec_T_uniq_inst : typeclass_instances.

Local Lemma resolve_ghost_Vec_concrete
    {T_rt : RT} (T_ty : type T_rt) {A_rt : RT} (A_ty : type A_rt)
    A_attrs π E L rm lb l bk rs T :
  T L (#rs) True false ⊢
  resolve_ghost π E L rm lb l
    (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>)) bk (#rs) T.
Proof. apply resolve_ghost_ofty_default. Qed.
Local Definition resolve_ghost_Vec_concrete_inst :=
  [instance @resolve_ghost_Vec_concrete].
Local Existing Instance resolve_ghost_Vec_concrete_inst | 1.

Lemma Heap_new_proof (π : thread_id) :
  Heap_new_lemma π.
Proof.
  Heap_new_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  apply NoDup_nil_2.
  
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
