From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.theories Require Export layout shims.
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


Section Global_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition Global_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t Global_sls +[]))).
Defined.

Definition Global_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (Global_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Global_ty.
#[global] Typeclasses Transparent Global_rt.
End Global_ty.
Global Arguments Global_rt : clear implicits.

Section layout_LayoutError_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition layout_LayoutError_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t layout_LayoutError_sls +[]))).
Defined.

Definition layout_LayoutError_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (layout_LayoutError_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent layout_LayoutError_ty.
#[global] Typeclasses Transparent layout_LayoutError_rt.
End layout_LayoutError_ty.
Global Arguments layout_LayoutError_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition GlobalasAllocator_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Allocator_spec_attrs ((Global_rt)))) :=
  {|
    Allocator_FreeablePerm  :=
      (λ _ l sz, freeable_nz l sz 1 HeapAlloc) : ((Allocator_FreeablePerm_sig ((Global_rt))));
  |}
.


End attrs.

Section layout_Layout_ty.
  Context `{RRGS : !refinedrustGS Σ}.


Definition layout_Layout_ty  : (spec_with 0 [] ((type (plist place_rfnRT [Z : RT; (((alignment_Alignment_inv_t_rt))) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ((struct_t layout_Layout_sls +[((int USize)); ((alignment_Alignment_inv_t  -[] -[]))]))).
Defined.

Definition layout_Layout_rt  : RT.
Proof using  .
  let __a := (normalized_rt_of_spec_ty (layout_Layout_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent layout_Layout_ty.
#[global] Typeclasses Transparent layout_Layout_rt.
End layout_Layout_ty.
Global Arguments layout_Layout_rt : clear implicits.
Section layout_Layout_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.

  Program Definition layout_Layout_inv_t_inv_spec  : spec_with 0 [] (ex_inv_def (layout_Layout_rt)%type ((rust_layout))%type) := spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((rust_layout)%type : RT)),
            let 'l := _ty_rfn in ⌜inner_rfn = -[#(Z.of_nat l.(layout_sz)); #(l.(layout_alignment))]⌝ ∗ ⌜(layout_wf l)%Z⌝ ∗ ⌜(Z.of_nat l.(layout_sz) ∈ isize)%Z⌝ ∗ True)%I
    (false)
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition layout_Layout_inv_t  : spec_with 0 [] (type ((rust_layout))%type) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (layout_Layout_inv_t_inv_spec  -[] -[]) (layout_Layout_ty -[] -[]).
Global Arguments layout_Layout_inv_t_inv_spec : simpl never.
Global Arguments layout_Layout_inv_t : simpl never.
  Global Typeclasses Transparent layout_Layout_inv_t.
  Definition layout_Layout_inv_t_rt : RT.
  Proof using  . let __a := normalized_rt_of_spec_ty layout_Layout_inv_t in exact __a. Defined.
  Global Typeclasses Transparent layout_Layout_inv_t_rt.
End layout_Layout_inv_t.
Global Arguments layout_Layout_inv_t_rt : clear implicits.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Global Instance shareable_discard_freeable `{!refinedrustGS Σ} {Self_rt : RT} (A : Allocator_spec_attrs Self_rt) π κ κs a l n :
  Shareable π κ κs (A.(Allocator_FreeablePerm) a l n) := shareable_discard _ _ _ _.
Global Instance ghost_droppable_discard_freeable `{!refinedrustGS Σ} {Self_rt : RT} (A : Allocator_spec_attrs Self_rt) a l n :
  GhostDroppable (A.(Allocator_FreeablePerm) a l n) := ghost_droppable_discard _.
Record Allocator_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Allocator_spec {
}.
#[global] Arguments Allocator_spec : clear implicits.

#[global] Arguments Allocator_spec {_ _}.


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

Definition Allocator_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((Allocator_spec_attrs ((Self_rt))))) : (spec_with _ _ (Allocator_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Allocator_spec _ _ ((Self_rt))).

End Allocator.

Section Allocator_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Allocator_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_layout_Layout_align  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_layout_Layout_align  :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (layout_Layout_inv_t   -[] -[]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.of_nat (layout_alignment_nat self) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_from_size_align  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_layout_Layout_from_size_align  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (size, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) size :@: (int USize), align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)
        ∗ (⌜(size ∈ isize)%Z⌝)
        ∗ (⌜(Z.divide align size)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Ok (mk_rust_layout (Z.to_nat size) (alignment_of_align align)) @ (Result_ty ((layout_Layout_inv_t_rt)) ((layout_LayoutError_rt)) -[] -[(layout_Layout_inv_t   -[] -[]); (layout_LayoutError_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_from_size_align_unchecked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

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
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_new (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_layout_Layout_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, mk_rust_layout (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) (alignment_of_align (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)))) @ (layout_Layout_inv_t   -[] -[]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_layout_Layout_size  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_layout_Layout_size  :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (layout_Layout_inv_t   -[] -[]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.of_nat self.(layout_sz) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_alloc_alloc_internal  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

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
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2)))))
      ∗ (⌜(min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end)%Z⌝)).

Definition trait_incl_of_alloc_dealloc_internal  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alloc_dealloc_internal  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (size, align_log2, ptr) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) size :@: (int USize), align_log2 :@: (int USize), ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (freeable_nz ptr (Z.to_nat size) 1 HeapAlloc)
        ∗ (⌜((0 < size)%Z)%Z⌝)
        ∗ (ptr ◁ₗ[π, Owned] #(()) @ (◁ uninit (UntypedSynType (Layout (Z.to_nat size) (Z.to_nat align_log2)))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, True).


Definition trait_incl_of_alloc_alloc  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alloc_alloc  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (ly) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ly :@: (layout_Layout_inv_t   -[] -[]);
      (* precondition. *) (λ π : thread_id, (⌜(ly.(layout_sz) > 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz l ly.(layout_sz) 1 HeapAlloc)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit (UntypedSynType ly)))
      ∗ (⌜(min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end)%Z⌝)).

Definition trait_incl_of_alloc_dealloc  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alloc_dealloc  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr, ly) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t, ly :@: (layout_Layout_inv_t   -[] -[]);
      (* precondition. *) (λ π : thread_id, (freeable_nz ptr ly.(layout_sz) 1 HeapAlloc)
        ∗ (⌜(0 < ly.(layout_sz))%Z⌝)
        ∗ (ptr ◁ₗ[π, Owned] #(()) @ (◁ uninit (UntypedSynType ly)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_realloc  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_realloc  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (v, ptr, ly, new_size) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) ptr :@: alias_ptr_t, ly :@: (layout_Layout_inv_t   -[] -[]), new_size :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜((ly.(layout_sz) ≤ new_size)%Z)%Z⌝)
        ∗ (⌜((0 < ly.(layout_sz))%Z)%Z⌝)
        ∗ (⌜(new_size ≤ MaxInt ISize)%Z⌝)
        ∗ (⌜(layout_wf (Layout (Z.to_nat new_size) (layout_alignment_log2_nat ly)))%Z⌝)
        ∗ (ptr ◁ₗ[π, Owned] #(v) @ (◁ value_t (UntypedSynType ly)))
        ∗ (freeable_nz ptr ly.(layout_sz) 1 HeapAlloc)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ptr_new, v') : ((_ * _)), ptr_new @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc)
      ∗ (ptr_new ◁ₗ[π, Owned] #(v ++ v' : val) @ (◁ value_t (UntypedSynType (Layout (Z.to_nat new_size) (layout_alignment_log2_nat ly)))))
      ∗ (⌜(v' `has_layout_val` (Layout (Z.to_nat new_size - ly.(layout_sz)) (layout_alignment_log2_nat ly)))%Z⌝)
      ∗ (⌜(min_alloc_start ≤ ptr_new.(loc_a) ≤ max_alloc_end)%Z⌝)).

Definition trait_incl_of_alloc_realloc_internal  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alloc_realloc_internal  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (v, old_size, align_log2, new_size, ptr_old) : ((_ * _ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) old_size :@: (int USize), align_log2 :@: (int USize), new_size :@: (int USize), ptr_old :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜((old_size ≤ new_size)%Z)%Z⌝)
        ∗ (⌜((0 < old_size)%Z)%Z⌝)
        ∗ (⌜(new_size ≤ MaxInt ISize)%Z⌝)
        ∗ (⌜(layout_wf (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))%Z⌝)
        ∗ (ptr_old ◁ₗ[π, Owned] #(v) @ (◁ value_t (UntypedSynType (Layout (Z.to_nat old_size) (Z.to_nat align_log2)))))
        ∗ (freeable_nz ptr_old (Z.to_nat old_size) 1 HeapAlloc)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ptr_new, v') : ((_ * _)), ptr_new @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc)
      ∗ (ptr_new ◁ₗ[π, Owned] #(v ++ v' : val) @ (◁ value_t (UntypedSynType (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))))
      ∗ (⌜(v' `has_layout_val` (Layout (Z.to_nat (new_size - old_size)) (Z.to_nat align_log2)))%Z⌝)
      ∗ (⌜(min_alloc_start ≤ ptr_new.(loc_a) ≤ max_alloc_end)%Z⌝)).



End specs.
Section GlobalasAllocator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition GlobalasAllocator_spec  : (spec_with _ _ (Allocator_spec ((Global_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Allocator_spec _ _ ((Global_rt))).
  Definition GlobalasAllocator_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Allocator_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), GlobalasAllocator_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Allocator_base_spec (Global_rt) Global_st GlobalasAllocator_spec_attrs-[] -[(Global_ty  -[] -[])])))).
End GlobalasAllocator_spec.

