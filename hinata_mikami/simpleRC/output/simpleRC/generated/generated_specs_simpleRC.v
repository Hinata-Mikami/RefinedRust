From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.simpleRC Require Export generated_code_simpleRC.

Section RcInner_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition RcInner_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [Z : RT; (T_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (RcInner_sls (T_ty.(ty_syn_type))) +[((int USize)); (T_ty)]))).
Defined.

Definition RcInner_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (RcInner_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent RcInner_ty.
#[global] Typeclasses Transparent RcInner_rt.
End RcInner_ty.
Global Arguments RcInner_rt : clear implicits.
Section RcInner_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition RcInner_inv_t_inv_spec  : spec_with 0 [T_rt] (ex_inv_def ((RcInner_rt (T_rt)))%type ((Z * T_rt))%type) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((Z * T_rt)%type : RT)), 
            let '(c, x) := _ty_rfn in ⌜inner_rfn = -[#(c); #(x)]⌝ ∗ ⌜(1 <= c)%Z⌝ ∗ True)%I
    (λ π κ inner_rfn (_ty_rfn : RT_rt ((Z * T_rt)%type : RT)), 
            let '(c, x) := _ty_rfn in ⌜inner_rfn = -[#(c); #(x)]⌝ ∗ ⌜(1 <= c)%Z⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition RcInner_inv_t  : spec_with 0 [T_rt] (type ((Z * T_rt))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (RcInner_inv_t_inv_spec   <TY> T_ty <INST!>) ((RcInner_ty (T_rt))  <TY> T_ty <INST!>).
  Global Typeclasses Transparent RcInner_inv_t.
  Definition RcInner_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty RcInner_inv_t in exact __a. Defined.
  Global Typeclasses Transparent RcInner_inv_t_rt.
End RcInner_inv_t.
Global Arguments RcInner_inv_t_rt : clear implicits.

Section SimpleRC_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition SimpleRC_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [loc : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (SimpleRC_sls (T_ty.(ty_syn_type))) +[(alias_ptr_t)]))).
Defined.

Definition SimpleRC_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (SimpleRC_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent SimpleRC_ty.
#[global] Typeclasses Transparent SimpleRC_rt.
End SimpleRC_ty.
Global Arguments SimpleRC_rt : clear implicits.
Section SimpleRC_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition SimpleRC_inv_t_inv_spec  : spec_with 0 [T_rt] (ex_inv_def ((SimpleRC_rt (T_rt)))%type (_)%type) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (_%type : RT)), 
            let 'l := _ty_rfn in ∃ (c: _) (x: _), ⌜inner_rfn = -[#(l)]⌝ ∗ l ◁ₗ[π, Owned true] #((c, x)) @ (◁ (int i32) * T_rt) ∗ True)%I
    (λ π κ inner_rfn (_ty_rfn : RT_rt (_%type : RT)), 
            let 'l := _ty_rfn in ∃ (c: _) (x: _), ⌜inner_rfn = -[#(l)]⌝ ∗ guarded (l ◁ₗ[π, Shared κ] #((c, x)) @ (◁ (int i32) * T_rt)) ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition SimpleRC_inv_t  : spec_with 0 [T_rt] (type (_)%type) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (SimpleRC_inv_t_inv_spec   <TY> T_ty <INST!>) ((SimpleRC_ty (T_rt))  <TY> T_ty <INST!>).
  Global Typeclasses Transparent SimpleRC_inv_t.
  Definition SimpleRC_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty SimpleRC_inv_t in exact __a. Defined.
  Global Typeclasses Transparent SimpleRC_inv_t_rt.
End SimpleRC_inv_t.
Global Arguments SimpleRC_inv_t_rt : clear implicits.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_SimpleRC_T_new (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_SimpleRC_T_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: T;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ (SimpleRC_inv_t ((T_rt))   <TY> T_ty <INST!>);
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned false] #((1, x)) @ (◁ (int i32) * T_rt))).


Definition trait_incl_of_box_new (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_box_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: T;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), x @ (box T);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_box_into_raw (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_box_into_raw (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (box T);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned false] #(x) @ (◁ T))).

Definition trait_incl_of_box_from_raw (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_box_from_raw (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, x) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (l ◁ₗ[π, Owned false] #(x) @ (◁ T))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), x @ (box T);
      (* postcondition *) (λ π : thread_id, True).



End specs.
