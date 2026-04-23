From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.mem.theories Require Export shims.
From rrstd.mem.mem Require Export generated_code_mem.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_mem_align_log_of (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_mem_align_log_of (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ly_align_log (use_layout_alg' (ty_syn_type T_ty MetaNone)) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_mem_align_of (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_mem_align_of (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_mem_size_of (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_mem_size_of (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone)) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).




End specs.
