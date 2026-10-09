From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.theories Require Export layout shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.alloc.alloc Require Export generated_code_alloc.

Definition Allocator_FreeablePerm_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) :=
  ((RT_xt (Self_rt)) → loc → nat → iProp Σ).
Record Allocator_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Allocator_spec_attrs {
  Allocator_FreeablePerm  : (Allocator_FreeablePerm_sig (Self_rt));
}.
#[global] Arguments Allocator_spec_attrs : clear implicits.

#[global] Arguments Allocator_spec_attrs {_ _}.

#[global] Arguments mk_Allocator_spec_attrs  {_} {_} {_}.


Record AllocatorClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Allocator_Self_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (Self_rt) )} `{Clone_Self_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )} : Type := mk_AllocatorClone_spec_attrs {
}.
#[global] Arguments AllocatorClone_spec_attrs : clear implicits.

#[global] Arguments AllocatorClone_spec_attrs {_ _}.

#[global] Arguments mk_AllocatorClone_spec_attrs  {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasAllocator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((Allocator_spec_attrs ((place_rfnRT (A_rt))))) :=
  {|
    Allocator_FreeablePerm  :=
      (Allocator_A_spec_attrs.(Allocator_FreeablePerm)) : ((Allocator_FreeablePerm_sig ((place_rfnRT (A_rt)))));
  |}
.


End attrs.

Section Global_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition Global_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t Global_sls +[])).
  Defined.

  Definition Global_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (Global_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Global_rt.
  #[global] Typeclasses Transparent Global_ty.
End Global_ty.
#[global] Arguments Global_rt : clear implicits.

#[global] Arguments Global_ty : clear implicits.

#[global] Arguments Global_ty {_ _}  .

Section Global_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Program Definition Global_inv_t_inv_spec  : (spec_with 0 [] ((ex_inv_def (Global_rt)%type ((unit))%type))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : Global_rt) (_ty_rfn : RT_rt ((unit)%type : RT)),
                  let '() := _ty_rfn in ⌜inner_rfn = -[]⌝ ∗ True)%I
          (true)
          _
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Final Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition Global_inv_t  : (spec_with 0 [] ((type (((unit))%type)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (Global_inv_t_inv_spec  -[] -[]) (Global_ty -[] -[]).
  #[global] Arguments Global_inv_t_inv_spec : simpl never.

  #[global] Arguments Global_inv_t : simpl never.

  #[global] Typeclasses Transparent Global_inv_t.
  Definition Global_inv_t_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (Global_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Global_inv_t_rt.
End Global_inv_t.
#[global] Arguments Global_inv_t_rt : clear implicits.

#[global] Arguments Global_inv_t : clear implicits.

#[global] Arguments Global_inv_t {_ _}  .

#[global] Arguments Global_inv_t_inv_spec : clear implicits.

#[global] Arguments Global_inv_t_inv_spec {_ _}  .


Section layout_LayoutError_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition layout_LayoutError_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t layout_LayoutError_sls +[])).
  Defined.

  Definition layout_LayoutError_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (layout_LayoutError_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent layout_LayoutError_rt.
  #[global] Typeclasses Transparent layout_LayoutError_ty.
End layout_LayoutError_ty.
#[global] Arguments layout_LayoutError_rt : clear implicits.

#[global] Arguments layout_LayoutError_ty : clear implicits.

#[global] Arguments layout_LayoutError_ty {_ _}  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition REFAasAllocatorClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((AllocatorClone_spec_attrs ((place_rfnRT (A_rt))) ((REFAasAllocator_spec_attrs ((A_rt)) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))) ((REFTasClone_spec_attrs ((A_rt)) (DropGlue_A_spec_attrs))))) :=
  mk_AllocatorClone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition GlobalasAllocator_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Allocator_spec_attrs ((Global_inv_t_rt)))) :=
  {|
    Allocator_FreeablePerm  :=
      (λ _ l sz, freeable_nz l sz 1 HeapAlloc) : ((Allocator_FreeablePerm_sig ((Global_inv_t_rt))));
  |}
.


End attrs.

Section layout_Layout_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition layout_Layout_ty  : (spec_with 0 [] ((type (plist place_rfnRT [Z : RT; (((alignment_Alignment_inv_t_rt))) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t layout_Layout_sls +[((int USize)); ((alignment_Alignment_inv_t  -[] -[]))])).
  Defined.

  Definition layout_Layout_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (layout_Layout_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent layout_Layout_rt.
  #[global] Typeclasses Transparent layout_Layout_ty.
End layout_Layout_ty.
#[global] Arguments layout_Layout_rt : clear implicits.

#[global] Arguments layout_Layout_ty : clear implicits.

#[global] Arguments layout_Layout_ty {_ _}  .

Section layout_Layout_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Program Definition layout_Layout_inv_t_inv_spec  : (spec_with 0 [] ((ex_inv_def (layout_Layout_rt)%type ((rust_layout))%type))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : layout_Layout_rt) (_ty_rfn : RT_rt ((rust_layout)%type : RT)),
                  let 'l := _ty_rfn in ⌜inner_rfn = -[#(Z.of_nat l.(layout_sz)); #(l.(layout_alignment))]⌝ ∗ ⌜(layout_wf l)%Z⌝ ∗ ⌜(Z.of_nat l.(layout_sz) ∈ isize)%Z⌝ ∗ True)%I
          (true)
          _
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Final Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition layout_Layout_inv_t  : (spec_with 0 [] ((type (((rust_layout))%type)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (layout_Layout_inv_t_inv_spec  -[] -[]) (layout_Layout_ty -[] -[]).
  #[global] Arguments layout_Layout_inv_t_inv_spec : simpl never.

  #[global] Arguments layout_Layout_inv_t : simpl never.

  #[global] Typeclasses Transparent layout_Layout_inv_t.
  Definition layout_Layout_inv_t_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (layout_Layout_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent layout_Layout_inv_t_rt.
End layout_Layout_inv_t.
#[global] Arguments layout_Layout_inv_t_rt : clear implicits.

#[global] Arguments layout_Layout_inv_t : clear implicits.

#[global] Arguments layout_Layout_inv_t {_ _}  .

#[global] Arguments layout_Layout_inv_t_inv_spec : clear implicits.

#[global] Arguments layout_Layout_inv_t_inv_spec {_ _}  .


Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)

Section extra_specs.
Context `{!refinedrustGS Σ}.

Global Instance shareable_discard_freeable {rt Self_rt : RT} (A : Allocator_spec_attrs Self_rt) π κ κs a l n (r : rt) :
  Shareable π κ κs r (A.(Allocator_FreeablePerm) a l n) := shareable_discard _ _ _ _ _.
Global Instance ghost_droppable_discard_freeable {Self_rt : RT} (A : Allocator_spec_attrs Self_rt) a l n :
  GhostDroppable (A.(Allocator_FreeablePerm) a l n) := ghost_droppable_discard _.

Definition FindAllocatorFreeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) (x : RT_xt Self_rt) (l : loc) :=
  {| fic_A := (nat); fic_Prop size := Allocator_FreeablePerm A_attr x l size |}.
Global Typeclasses Opaque FindAllocatorFreeable.

Global Instance related_to_allocator_freeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) x l n : RelatedTo (Allocator_FreeablePerm A_attr x l n) | 100 :=
  {| rt_fic := FindAllocatorFreeable A_attr x l |}.

Lemma subsume_allocator_freeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) x1 x2 l1 l2 n1 n2 T :
  ⌜l1 = l2⌝ ∗ ⌜n1 = n2⌝ ∗ ⌜x1 = x2⌝ ∗ T
  ⊢ subsume (Allocator_FreeablePerm A_attr x1 l1 n1) (Allocator_FreeablePerm A_attr x2 l2 n2) T.
Proof.
  iIntros "(-> & -> & -> & $)". eauto.
Qed.
Definition subsume_allocator_freeable_inst := [instance @subsume_allocator_freeable].
Global Existing Instance subsume_allocator_freeable_inst.

Lemma find_in_context_allocator_freeable {Self_rt : RT} (A_attr : Allocator_spec_attrs Self_rt) x l T :
  (∃ n, Allocator_FreeablePerm A_attr x l n ∗ T n)
  ⊢ find_in_context (FindAllocatorFreeable A_attr x l) T.
Proof.
  iDestruct 1 as (n) "(Ha & HT)".
  iExists n. by iFrame.
Qed.
Definition find_in_context_allocator_freeable_inst := [instance @find_in_context_allocator_freeable with FICSyntactic].
Global Existing Instance find_in_context_allocator_freeable_inst | 1.

End extra_specs.
Record Allocator_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Allocator_spec {
}.
#[global] Arguments Allocator_spec : clear implicits.

#[global] Arguments Allocator_spec {_ _}.


Record AllocatorClone_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_AllocatorClone_spec {
}.
#[global] Arguments AllocatorClone_spec : clear implicits.

#[global] Arguments AllocatorClone_spec {_ _}.


Section Allocator.
Context `{RRGS : !refinedrustGS Σ}.
Definition Allocator_spec_incl `{Self_rt : !RT} (spec1: ((Allocator_spec (Self_rt)))) (spec2: ((Allocator_spec (Self_rt)))) : Prop :=
  True.
Instance Allocator_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Allocator_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_Allocator_spec `{Self_rt : !RT} : (ScopeBindable ((Allocator_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((Allocator_spec (Self_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((Allocator_spec (Self_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_Allocator_spec.

Definition Allocator_base_spec (Self_rt: RT) (Self_st: syn_type) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Allocator_spec_attrs ((Self_rt))))) : (spec_with _ _ (Allocator_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Allocator_spec _ _ ((Self_rt))).
Arguments Allocator_base_spec : simpl never.


End Allocator.

Section AllocatorClone.
Context `{RRGS : !refinedrustGS Σ}.
Definition AllocatorClone_spec_incl `{Self_rt : !RT} (spec1: ((AllocatorClone_spec (Self_rt)))) (spec2: ((AllocatorClone_spec (Self_rt)))) : Prop :=
  True.
Instance AllocatorClone_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (AllocatorClone_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_AllocatorClone_spec `{Self_rt : !RT} : (ScopeBindable ((AllocatorClone_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((AllocatorClone_spec (Self_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((AllocatorClone_spec (Self_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_AllocatorClone_spec.

Definition AllocatorClone_base_spec (Self_rt: RT) (Self_st: syn_type) (Allocator_Self_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (DropGlue_Self_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((AllocatorClone_spec_attrs ((Self_rt)) (Allocator_Self_spec_attrs) (Clone_Self_spec_attrs)))) : (spec_with _ _ (AllocatorClone_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_AllocatorClone_spec _ _ ((Self_rt))).
Arguments AllocatorClone_base_spec : simpl never.


End AllocatorClone.

Section Allocator_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Allocator_trait_req_incls.

Section AllocatorClone_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End AllocatorClone_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_layout_Layout_align  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_layout_Layout_align  :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (layout_Layout_inv_t   -[] -[]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.of_nat (layout_alignment_nat self) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_from_size_align  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_layout_Layout_from_size_align  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (size, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) size :@: (int USize), align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)
        ∗ (⌜(size ∈ isize)%Z⌝)
        ∗ (⌜(Z.divide align size)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ok (mk_rust_layout (Z.to_nat size) (alignment_of_align align)) @ (Result_ty ((layout_Layout_inv_t_rt)) ((layout_LayoutError_rt)) -[] -[(layout_Layout_inv_t   -[] -[]); (layout_LayoutError_ty   -[] -[])]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_from_size_align_unchecked  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_layout_Layout_from_size_align_unchecked  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (size, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) size :@: (int USize), align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)
        ∗ (⌜(size ∈ isize)%Z⌝)
        ∗ (⌜(Z.divide align size)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, mk_rust_layout (Z.to_nat size) (alignment_of_align align) @ (layout_Layout_inv_t   -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_layout_Layout_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, mk_rust_layout (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) (alignment_of_align (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)))) @ (layout_Layout_inv_t   -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_size  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_layout_Layout_size  :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (layout_Layout_inv_t   -[] -[]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.of_nat self.(layout_sz) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_alloc_alloc_internal  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_alloc_alloc_internal  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (size, align_log2) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) size :@: (int USize), align_log2 :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(size ∈ ISize)%Z⌝)
        ∗ (⌜((size > 0)%Z)%Z⌝)
        ∗ (⌜(layout_wf (Layout (Z.to_nat size) (Z.to_nat align_log2)))%Z⌝)
        ∗ (⌜(ly_align_in_bounds (Layout (Z.to_nat size) (Z.to_nat align_log2)))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz l (Z.to_nat size) 1 HeapAlloc)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit (LiteralSynType (Layout (Z.to_nat size) (Z.to_nat align_log2)))))
      ∗ (⌜(min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_alloc_dealloc_internal  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_alloc_dealloc_internal  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (size, align_log2, ptr) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) size :@: (int USize), align_log2 :@: (int USize), ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (freeable_nz ptr (Z.to_nat size) 1 HeapAlloc)
        ∗ (⌜((0 < size)%Z)%Z⌝)
        ∗ (ptr ◁ₗ[π, Owned] #(()) @ (◁ uninit (LiteralSynType (Layout (Z.to_nat size) (Z.to_nat align_log2)))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).


Definition trait_incl_of_alloc_alloc  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_alloc_alloc  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (ly) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ly :@: (layout_Layout_inv_t   -[] -[]);
      (* precondition. *) (λ π : thread_id, (⌜(ly.(layout_sz) > 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz l ly.(layout_sz) 1 HeapAlloc)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit (LiteralSynType ly)))
      ∗ (⌜(min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_alloc_dealloc  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_alloc_dealloc  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr, ly) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t, ly :@: (layout_Layout_inv_t   -[] -[]);
      (* precondition. *) (λ π : thread_id, (freeable_nz ptr ly.(layout_sz) 1 HeapAlloc)
        ∗ (⌜(0 < ly.(layout_sz))%Z⌝)
        ∗ (ptr ◁ₗ[π, Owned] #(()) @ (◁ uninit (LiteralSynType ly)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_realloc  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_realloc  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (v, ptr, ly, new_size) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t, ly :@: (layout_Layout_inv_t   -[] -[]), new_size :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜((ly.(layout_sz) ≤ new_size)%Z)%Z⌝)
        ∗ (⌜((0 < ly.(layout_sz))%Z)%Z⌝)
        ∗ (⌜(new_size ≤ MaxInt ISize)%Z⌝)
        ∗ (⌜(layout_wf (Layout (Z.to_nat new_size) (layout_alignment_log2_nat ly)))%Z⌝)
        ∗ (ptr ◁ₗ[π, Owned] #(v) @ (◁ value_t false (LiteralSynType ly)))
        ∗ (freeable_nz ptr ly.(layout_sz) 1 HeapAlloc)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ptr_new, v') : ((_ * _)), ptr_new @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc)
      ∗ (ptr_new ◁ₗ[π, Owned] #(v ++ v' : val) @ (◁ value_t false (LiteralSynType (Layout (Z.to_nat new_size) (layout_alignment_log2_nat ly)))))
      ∗ (⌜(v' `has_layout_val` (Layout (Z.to_nat new_size - ly.(layout_sz)) (layout_alignment_log2_nat ly)))%Z⌝)
      ∗ (⌜(min_alloc_start ≤ ptr_new.(loc_a) ≤ max_alloc_end)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_alloc_realloc_internal  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_alloc_realloc_internal  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (v, old_size, align_log2, new_size, ptr_old) : ((_ * _ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) old_size :@: (int USize), align_log2 :@: (int USize), new_size :@: (int USize), ptr_old :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜((old_size ≤ new_size)%Z)%Z⌝)
        ∗ (⌜((0 < old_size)%Z)%Z⌝)
        ∗ (⌜(new_size ≤ MaxInt ISize)%Z⌝)
        ∗ (⌜(layout_wf (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))%Z⌝)
        ∗ (ptr_old ◁ₗ[π, Owned] #(v) @ (◁ value_t false (LiteralSynType (Layout (Z.to_nat old_size) (Z.to_nat align_log2)))))
        ∗ (freeable_nz ptr_old (Z.to_nat old_size) 1 HeapAlloc)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ptr_new, v') : ((_ * _)), ptr_new @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc)
      ∗ (ptr_new ◁ₗ[π, Owned] #(v ++ v' : val) @ (◁ value_t false (LiteralSynType (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))))
      ∗ (⌜(v' `has_layout_val` (Layout (Z.to_nat (new_size - old_size)) (Z.to_nat align_log2)))%Z⌝)
      ∗ (⌜(min_alloc_start ≤ ptr_new.(loc_a) ≤ max_alloc_end)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
Section REFAasAllocator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasAllocator_spec (A_rt: RT) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (Allocator_spec ((place_rfnRT (A_rt))))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), (@mk_Allocator_spec _ _ ((place_rfnRT (A_rt)))).
  Arguments REFAasAllocator_spec : simpl never.

  Program Definition REFAasAllocator_realization (A_rt: RT) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (place_rfnRT (A_rt)))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty]) π, (((typaram_wf A_rt A_st A_ty))
  ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty]) _ _, (REFAasAllocator_spec (A_rt) (A_st) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasAllocator_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl Allocator_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), (REFAasAllocator_spec (A_rt) (A_st) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), scope_add_typarams _ -[A_ty] ((Allocator_base_spec (place_rfnRT (A_rt)) RefSynType (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasAllocator_spec_attrs (A_rt) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))-[] -[(shr_ref ulft_0 A_ty)])))).
End REFAasAllocator_spec.

Section REFAasAllocatorClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition REFAasAllocatorClone_spec (A_rt: RT) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (AllocatorClone_spec ((place_rfnRT (A_rt))))) :=
    spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), (@mk_AllocatorClone_spec _ _ ((place_rfnRT (A_rt)))).
  Arguments REFAasAllocatorClone_spec : simpl never.

  Program Definition REFAasAllocatorClone_realization (A_rt: RT) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : trait_spec_realization (spec_with 0 [] (AllocatorClone_spec (RRGS:=RRGS) (place_rfnRT (A_rt)))) :=
  {|
    trait_ctx_lfts := 1;
    trait_ctx_tys := [A_rt];
    trait_ctx_wf := λ '( *[ulft_0]) '( *[A_ty]) π, (((typaram_wf A_rt A_st A_ty))
  ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I;
    trait_ctx_spec := λ '( *[ulft_0]) '( *[A_ty]) _ _, (REFAasAllocatorClone_spec (A_rt) (A_st) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition REFAasAllocatorClone_spec_subsumption  :=
    ∀ `(A_rt : !RT) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl AllocatorClone_spec_incl (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), (REFAasAllocatorClone_spec (A_rt) (A_st) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))-[ulft_0] -[A_ty]) (spec! ( *[ulft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), scope_add_typarams _ -[A_ty] ((AllocatorClone_base_spec (place_rfnRT (A_rt)) RefSynType (REFAasAllocator_spec_attrs ((A_rt)) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs)) (REFTasClone_spec_attrs ((A_rt)) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((place_rfnRT (A_rt)))) (REFAasAllocatorClone_spec_attrs (A_rt) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs))-[] -[(shr_ref ulft_0 A_ty)])))).
End REFAasAllocatorClone_spec.

Section GlobalasAllocator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition GlobalasAllocator_spec  : (spec_with _ _ (Allocator_spec ((Global_inv_t_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Allocator_spec _ _ ((Global_inv_t_rt))).
  Arguments GlobalasAllocator_spec : simpl never.

  Program Definition GlobalasAllocator_realization  : trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (Global_inv_t_rt))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];
    trait_ctx_wf := λ '( *[]) '( *[]) π, ((True))%I;
    trait_ctx_spec := λ '( *[]) '( *[]) _ _, GlobalasAllocator_spec-[] -[];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition GlobalasAllocator_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Allocator_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), GlobalasAllocator_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Allocator_base_spec (Global_inv_t_rt) Global_st (drop_glue_trivial_spec_attrs ((Global_inv_t_rt))) GlobalasAllocator_spec_attrs-[] -[(Global_inv_t   -[] -[])])))).
End GlobalasAllocator_spec.

