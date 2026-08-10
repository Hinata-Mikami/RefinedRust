From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num Require Export generated_code_num.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_i128_is_negative  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i128_is_positive  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i16_is_negative  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i16_is_positive  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i32_is_negative  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i32_is_positive  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i64_is_negative  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i64_is_positive  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i8_is_negative  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i8_is_positive  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_isize_is_negative  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isize_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_isize_is_positive  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isize_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u128_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), other :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u16_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), other :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u32_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), other :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u64_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), other :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u8_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), other :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_usize_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usize_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), other :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.


Definition trait_incl_of_i128_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I128), other :@: (int I128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i16_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I16), other :@: (int I16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i32_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I32), other :@: (int I32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i64_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I64), other :@: (int I64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_i8_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I8), other :@: (int I8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_isize_abs_diff  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_isize_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int ISize), other :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u128_is_power_of_two  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u16_is_power_of_two  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u32_is_power_of_two  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u64_is_power_of_two  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_u8_is_power_of_two  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.

Definition trait_incl_of_usize_is_power_of_two  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_usize_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind post... *) False.



End specs.
