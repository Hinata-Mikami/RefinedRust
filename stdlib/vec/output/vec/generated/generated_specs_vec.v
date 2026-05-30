From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.vec.theories Require Export vec.
From rrstd.alloc.vec Require Export generated_code_vec.

Record private_slice_index_Sealed_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_private_slice_index_Sealed_spec_attrs {
}.
#[global] Arguments private_slice_index_Sealed_spec_attrs : clear implicits.

#[global] Arguments private_slice_index_Sealed_spec_attrs {_ _}.

#[global] Arguments mk_private_slice_index_Sealed_spec_attrs  {_} {_} {_}.


Definition SliceIndex_SliceIndexProj_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  ((RT_xt (T_rt)) → (RT_xt (Self_rt)) → option (RT_xt (Output_rt))).
Definition SliceIndex_SliceIndexInj_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (SliceIndex_SliceIndexProj: (SliceIndex_SliceIndexProj_sig (Self_rt) (T_rt) (Output_rt) (private_slice_index_Sealed_Self_spec_attrs))) :=
  ((RT_xt (T_rt)) → (RT_xt (Self_rt)) → gname → (T_rt)).
Record SliceIndex_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} `{Output_rt : !RT} `{private_slice_index_Sealed_Self_spec_attrs : !(private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )} : Type := mk_SliceIndex_spec_attrs {
  SliceIndex_SliceIndexProj  : (SliceIndex_SliceIndexProj_sig (Self_rt) (T_rt) (Output_rt) (private_slice_index_Sealed_Self_spec_attrs));
  SliceIndex_SliceIndexInj  : (SliceIndex_SliceIndexInj_sig (Self_rt) (T_rt) (Output_rt) (private_slice_index_Sealed_Self_spec_attrs) (SliceIndex_SliceIndexProj));
}.
#[global] Arguments SliceIndex_spec_attrs : clear implicits.

#[global] Arguments SliceIndex_spec_attrs {_ _}.

#[global] Arguments mk_SliceIndex_spec_attrs  {_} {_} {_} {_} {_} {_}.


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasprivate_slice_index_Sealed_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((private_slice_index_Sealed_spec_attrs (Z))) :=
  mk_private_slice_index_Sealed_spec_attrs.


End attrs.

Section Iter_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition Iter_ty  : (spec_with 1 [(T_rt)] ((type (plist place_rfnRT [loc : RT; (((core_marker_PhantomData_rt) ((place_rfnRT (T_rt))))) : RT])))).
Proof.
  exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (Iter_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[(alias_ptr_t); ((core_marker_PhantomData_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_a T_ty)]))]))).
Defined.

Definition Iter_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (Iter_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Iter_ty.
#[global] Typeclasses Transparent Iter_rt.
End Iter_ty.
Global Arguments Iter_rt : clear implicits.
Section Iter_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition Iter_inv_t_inv_spec  : spec_with 1 [T_rt] (ex_inv_def ((Iter_rt (T_rt)))%type ((list ((T_rt))))%type) := spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((list ((T_rt)))%type : RT)),
            let 'xs := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z) (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(x); #(y)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition Iter_inv_t  : spec_with 1 [T_rt] (type ((list ((T_rt))))%type) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (Iter_inv_t_inv_spec  -[ulft_a] -[T_ty]) ((Iter_ty (T_rt)) -[ulft_a] -[T_ty]).
Global Arguments Iter_inv_t_inv_spec : simpl never.
Global Arguments Iter_inv_t : simpl never.
  Global Typeclasses Transparent Iter_inv_t.
  Definition Iter_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty Iter_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Iter_inv_t_rt.
End Iter_inv_t.
Global Arguments Iter_inv_t_rt : clear implicits.

Section IterMut_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).


Definition IterMut_ty  : (spec_with 1 [(T_rt)] ((type (plist place_rfnRT [((((nonnull_NonNull_inv_t_rt)) ((T_rt)))) : RT; loc : RT; (((core_marker_PhantomData_rt) (((place_rfnRT (T_rt)) * gname)%type))) : RT])))).
Proof.
  exact (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (IterMut_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[((nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty])); (alias_ptr_t); ((core_marker_PhantomData_ty (((place_rfnRT (T_rt)) * gname)%type) -[] -[(mut_ref ulft_a T_ty)]))]))).
Defined.

Definition IterMut_rt  : RT.
Proof using T_rt .
  let __a := (normalized_rt_of_spec_ty (IterMut_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent IterMut_ty.
#[global] Typeclasses Transparent IterMut_rt.
End IterMut_ty.
Global Arguments IterMut_rt : clear implicits.
Section IterMut_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT).

  Program Definition IterMut_inv_t_inv_spec  : spec_with 1 [T_rt] (ex_inv_def ((IterMut_rt (T_rt)))%type (((list ((T_rt) * gname))%type))%type) := spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((list ((T_rt) * gname))%type)%type : RT)),
            let 'xs := _ty_rfn in ∃ (x: name_hint_ty "x" ((loc))%Z) (y: name_hint_ty "y" ((loc))%Z), ⌜inner_rfn = -[#(x); #(y); #(tt)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.

  Definition IterMut_inv_t  : spec_with 1 [T_rt] (type (((list ((T_rt) * gname))%type))%type) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (IterMut_inv_t_inv_spec  -[ulft_a] -[T_ty]) ((IterMut_ty (T_rt)) -[ulft_a] -[T_ty]).
Global Arguments IterMut_inv_t_inv_spec : simpl never.
Global Arguments IterMut_inv_t : simpl never.
  Global Typeclasses Transparent IterMut_inv_t.
  Definition IterMut_inv_t_rt : RT.
  Proof using T_rt . let __a := normalized_rt_of_spec_ty IterMut_inv_t in exact __a. Defined.
  Global Typeclasses Transparent IterMut_inv_t_rt.
End IterMut_inv_t.
Global Arguments IterMut_inv_t_rt : clear implicits.

Section IntoIter_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).


Definition IntoIter_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((type (plist place_rfnRT [(((core_marker_PhantomData_rt) ((T_rt)))) : RT; (A_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((struct_t (IntoIter_sls ((T_ty.(ty_syn_type) (MetaNone))) ((A_ty.(ty_syn_type) (MetaNone)))) +[((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty])); (A_ty)]))).
Defined.

Definition IntoIter_rt  : RT.
Proof using T_rt A_rt .
  let __a := (normalized_rt_of_spec_ty (IntoIter_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent IntoIter_ty.
#[global] Typeclasses Transparent IntoIter_rt.
End IntoIter_ty.
Global Arguments IntoIter_rt : clear implicits.
Section IntoIter_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).

  Program Definition IntoIter_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (ex_inv_def ((IntoIter_rt (T_rt) (A_rt)))%type ((list ((T_rt))))%type) := spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((list ((T_rt)))%type : RT)),
            let 'xs := _ty_rfn in ∃ (x: name_hint_ty "x" (_)%Z) (y: name_hint_ty "y" (_)%Z), ⌜inner_rfn = -[#(x); #(y)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. intros ?; ex_plain_t_solve_shr_mono. Qed.

  Definition IntoIter_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (type ((list ((T_rt))))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ex_plain_t _ _ (IntoIter_inv_t_inv_spec Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (((IntoIter_ty (T_rt) (A_rt)) (Allocator_A_spec_attrs)) -[] -[T_ty; A_ty]).
Global Arguments IntoIter_inv_t_inv_spec : simpl never.
Global Arguments IntoIter_inv_t : simpl never.
  Global Typeclasses Transparent IntoIter_inv_t.
  Definition IntoIter_inv_t_rt : RT.
  Proof using T_rt A_rt . let __a := normalized_rt_of_spec_ty IntoIter_inv_t in exact __a. Defined.
  Global Typeclasses Transparent IntoIter_inv_t_rt.
End IntoIter_inv_t.
Global Arguments IntoIter_inv_t_rt : clear implicits.

Section RawVecInner_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (A_rt : RT).


Definition RawVecInner_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(A_rt)] ((type (plist place_rfnRT [((((unique_Unique_inv_t_rt)) (Z))) : RT; Z : RT; (A_rt) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), ((struct_t (RawVecInner_sls ((A_ty.(ty_syn_type) (MetaNone)))) +[((unique_Unique_inv_t (Z) -[] -[(int U8)])); ((int USize)); (A_ty)]))).
Defined.

Definition RawVecInner_rt  : RT.
Proof using A_rt .
  let __a := (normalized_rt_of_spec_ty (RawVecInner_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent RawVecInner_ty.
#[global] Typeclasses Transparent RawVecInner_rt.
End RawVecInner_ty.
Global Arguments RawVecInner_rt : clear implicits.
Section RawVecInner_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (A_rt : RT).

  Program Definition RawVecInner_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [A_rt] (ex_inv_def ((RawVecInner_rt (A_rt)))%type (((loc * nat * (A_rt) : RT)%type))%type) := spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((loc * nat * (A_rt) : RT)%type)%type : RT)),
            let '(l, cap, alloc) := _ty_rfn in ⌜inner_rfn = -[#(l); #(Z.of_nat cap); #(alloc)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. intros ?; ex_plain_t_solve_shr_mono. Qed.

  Definition RawVecInner_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [A_rt] (type (((loc * nat * (A_rt) : RT)%type))%type) :=
    spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), ex_plain_t _ _ (RawVecInner_inv_t_inv_spec Allocator_A_spec_attrs -[] -[A_ty]) (((RawVecInner_ty (A_rt)) (Allocator_A_spec_attrs)) -[] -[A_ty]).
Global Arguments RawVecInner_inv_t_inv_spec : simpl never.
Global Arguments RawVecInner_inv_t : simpl never.
  Global Typeclasses Transparent RawVecInner_inv_t.
  Definition RawVecInner_inv_t_rt : RT.
  Proof using A_rt . let __a := normalized_rt_of_spec_ty RawVecInner_inv_t in exact __a. Defined.
  Global Typeclasses Transparent RawVecInner_inv_t_rt.
End RawVecInner_inv_t.
Global Arguments RawVecInner_inv_t_rt : clear implicits.

Section RawVec_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).


Definition RawVec_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((type (plist place_rfnRT [((RawVecInner_inv_t_rt ((A_rt)))) : RT; (((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((struct_t (RawVec_sls ((T_ty.(ty_syn_type) (MetaNone))) ((A_ty.(ty_syn_type) (MetaNone)))) +[((RawVecInner_inv_t ((A_rt)) Allocator_A_spec_attrs -[] -[A_ty])); ((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))]))).
Defined.

Definition RawVec_rt  : RT.
Proof using T_rt A_rt .
  let __a := (normalized_rt_of_spec_ty (RawVec_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent RawVec_ty.
#[global] Typeclasses Transparent RawVec_rt.
End RawVec_ty.
Global Arguments RawVec_rt : clear implicits.
Section RawVec_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).

  Program Definition RawVec_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (ex_inv_def ((RawVec_rt (T_rt) (A_rt)))%type (((loc * nat)))%type) := spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt (((loc * nat))%type : RT)),
            let '(l, cap) := _ty_rfn in ∃ (a: name_hint_ty "a" (_)%Z), ⌜inner_rfn = -[#((l, cap, a)); #(tt)]⌝ ∗ freeable_nz l (size_of_array_in_bytes (ty_syn_type T_ty MetaNone) cap) 1 HeapAlloc ∗ True)%I
    ([])
    ([])
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. intros ?; ex_plain_t_solve_shr_mono. Qed.

  Definition RawVec_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (type (((loc * nat)))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ex_plain_t _ _ (RawVec_inv_t_inv_spec Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (((RawVec_ty (T_rt) (A_rt)) (Allocator_A_spec_attrs)) -[] -[T_ty; A_ty]).
Global Arguments RawVec_inv_t_inv_spec : simpl never.
Global Arguments RawVec_inv_t : simpl never.
  Global Typeclasses Transparent RawVec_inv_t.
  Definition RawVec_inv_t_rt : RT.
  Proof using T_rt A_rt . let __a := normalized_rt_of_spec_ty RawVec_inv_t in exact __a. Defined.
  Global Typeclasses Transparent RawVec_inv_t_rt.
End RawVec_inv_t.
Global Arguments RawVec_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition IntoIterTAasstd_iter_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((traits_iterator_Iterator_spec_attrs (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)))) :=
  {|
    traits_iterator_Iterator_Params  :=
      (unit) : ((traits_iterator_Iterator_Params_sig (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt))));
    traits_iterator_Iterator_Inv  :=
      (λ π _ self, True%I) : ((traits_iterator_Iterator_Inv_sig (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) (_)));
    traits_iterator_Iterator_Next  :=
      (λ π _ l e l2, 
            (⌜if_None e (l = [] ∧ l2 = [])⌝∗
            ⌜if_Some e (λ e, l = e :: l2)⌝)%I) : ((traits_iterator_Iterator_Next_sig (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition IteraTasstd_iter_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((traits_iterator_Iterator_spec_attrs (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))))) :=
  {|
    traits_iterator_Iterator_Params  :=
      (unit) : ((traits_iterator_Iterator_Params_sig (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt)))));
    traits_iterator_Iterator_Inv  :=
      (λ π _ self, True%I) : ((traits_iterator_Iterator_Inv_sig (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) (_)));
    traits_iterator_Iterator_Next  :=
      (λ π _ l e l2, 
            (⌜if_None e (l = [] ∧ l2 = [])⌝∗
            ⌜if_Some e (λ e, l = e :: l2)⌝)%I) : ((traits_iterator_Iterator_Next_sig (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) (_) (_)));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition IterMutaTasstd_iter_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((traits_iterator_Iterator_spec_attrs (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type))) :=
  {|
    traits_iterator_Iterator_Params  :=
      (unit) : ((traits_iterator_Iterator_Params_sig (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type)));
    traits_iterator_Iterator_Inv  :=
      (λ π _ self, True%I) : ((traits_iterator_Iterator_Inv_sig (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) (_)));
    traits_iterator_Iterator_Next  :=
      (λ π _ l1 e l2, 
            (⌜if_None e (l1 = [] ∧ l2 = [])⌝ ∗
            ⌜if_Some e (λ e, l1 = e :: l2)⌝)%I) : ((traits_iterator_Iterator_Next_sig (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) (_) (_)));
  |}
.


End attrs.

Section Vec_ty.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).


Definition Vec_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((type (plist place_rfnRT [((RawVec_inv_t_rt ((T_rt)) ((A_rt)))) : RT; Z : RT])))).
Proof.
  exact (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((struct_t (Vec_sls ((T_ty.(ty_syn_type) (MetaNone))) ((A_ty.(ty_syn_type) (MetaNone)))) +[((RawVec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])); ((int USize))]))).
Defined.

Definition Vec_rt  : RT.
Proof using T_rt A_rt .
  let __a := (normalized_rt_of_spec_ty (Vec_ty)) in exact __a.
Defined.

#[global] Typeclasses Transparent Vec_ty.
#[global] Typeclasses Transparent Vec_rt.
End Vec_ty.
Global Arguments Vec_rt : clear implicits.
Section Vec_inv_t.
  Context `{RRGS : !refinedrustGS Σ}.
  Context (T_rt : RT) (A_rt : RT).

  Program Definition Vec_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (ex_inv_def ((Vec_rt (T_rt) (A_rt)))%type ((list (place_rfn (T_rt))))%type) := spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), mk_auto_ex_inv_def
    (λ π inner_rfn (_ty_rfn : RT_rt ((list (place_rfn (T_rt)))%type : RT)),
            let 'xs := _ty_rfn in ∃ (cap: name_hint_ty "cap" ((nat))%Z) (l: name_hint_ty "l" ((loc))%Z) (len: name_hint_ty "len" ((nat))%Z) (els: name_hint_ty "els" (_)%Z), ⌜inner_rfn = -[#((l, cap)); #(Z.of_nat len)]⌝ ∗ guarded true (l ◁ₗ[π, Owned] #(els) @ (◁ array_t cap (maybe_uninit T_ty))) ∗ ⌜(name_hint "Hxs" (xs = project_vec_els len els)%Z)%Z⌝ ∗ ⌜(name_hint "Hlook_1" (∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i))))%Z)%Z⌝ ∗ ⌜(name_hint "Hlook_2" (∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None))%Z)%Z⌝ ∗ ⌜(name_hint "Hlen_eq" (len = length xs)%Z)%Z⌝ ∗ ⌜(name_hint "Hcap" (len ≤ cap)%Z)%Z⌝ ∗ ⌜(name_hint "Hbound" (len ≤ MaxInt usize)%Z)%Z⌝ ∗ ⌜(if decide (size_of_st (ty_syn_type T_ty MetaNone) = 0%nat) then cap = Z.to_nat (MaxInt USize) else (size_of_array_in_bytes (ty_syn_type T_ty MetaNone) cap ≤ MaxInt ISize)%Z)%Z⌝ ∗ True)%I
    ([] ++ (ty_lfts (T_ty)))
    ([] ++ (ty_wf_E (T_ty)))
    _ _ _ _
  .
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. intros ?; ex_plain_t_solve_shr_mono. Qed.

  Definition Vec_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : spec_with 0 [T_rt; A_rt] (type ((list (place_rfn (T_rt))))%type) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ex_plain_t _ _ (Vec_inv_t_inv_spec Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (((Vec_ty (T_rt) (A_rt)) (Allocator_A_spec_attrs)) -[] -[T_ty; A_ty]).
Global Arguments Vec_inv_t_inv_spec : simpl never.
Global Arguments Vec_inv_t : simpl never.
  Global Typeclasses Transparent Vec_inv_t.
  Definition Vec_inv_t_rt : RT.
  Proof using T_rt A_rt . let __a := normalized_rt_of_spec_ty Vec_inv_t in exact __a. Defined.
  Global Typeclasses Transparent Vec_inv_t_rt.
End Vec_inv_t.
Global Arguments Vec_inv_t_rt : clear implicits.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition VecTAasstd_iter_IntoIterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((traits_iterator_IntoIterator_spec_attrs (((Vec_inv_t_rt ((T_rt)) ((A_rt))))) (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)))) :=
  {|
    traits_iterator_IntoIterator_IntoIter  :=
      (id) : ((traits_iterator_IntoIterator_IntoIter_sig (((Vec_inv_t_rt ((T_rt)) ((A_rt))))) (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt))));
  |}
.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition VecTasstd_iter_FromIteratorT_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((traits_iterator_FromIterator_spec_attrs (((Vec_inv_t_rt ((T_rt)) ((((Global_rt))))))) ((T_rt)))) :=
  {|
    traits_iterator_FromIterator_FromSequence  :=
      (λ x, x) : ((traits_iterator_FromIterator_FromSequence_sig (((Vec_inv_t_rt ((T_rt)) ((((Global_rt))))))) ((T_rt))));
  |}
.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.

Section Vec_inv_t_ne.
  Context `{!refinedrustGS Σ}.

  Global Instance Vec_inv_t_contr {rt1 T_rt A_rt} Alloc (T : type rt1 → type T_rt) (A : type A_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, Vec_inv_t T_rt A_rt Alloc <TY> (T ty) <TY> A <INST!>).
  Proof.
  Admitted.
  Global Instance Vec_inv_t_ne {rt1 T_rt A_rt} Alloc (T : type rt1 → type T_rt) (A : type A_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, Vec_inv_t T_rt A_rt Alloc <TY> (T ty) <TY> A <INST!>).
  Proof. Admitted.
End Vec_inv_t_ne.


(* NOTE Resolution of ghost variables over the invariant -- not currently automatically generated by the frontend. *)
Lemma resolve_ghost_Vec_T_owned {T_rt : RT} (T_ty : type (T_rt)) {A_rt : RT} (A_ty : type (A_rt)) A_attrs π E L rm l rs T :
  (∀ li, resolve_ghost_iter π E L rm true li (ty_syn_type T_ty MetaNone) (replicate (length rs) (◁ T_ty))%I (Owned ) rs [] 0%nat (λ L2 rs' R progress,
    T L2 (#rs') R progress)) ⊢
  resolve_ghost π E L rm true l (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>)) (Owned ) (#rs) T.
Proof.
Admitted.
Definition resolve_ghost_Vec_T_owned_inst := [instance @resolve_ghost_Vec_T_owned].
Global Existing Instance resolve_ghost_Vec_T_owned_inst.

Lemma resolve_ghost_Vec_T_uniq {T_rt : RT} (T_ty : type (T_rt)) {A_rt : RT} (A_ty : type (A_rt)) A_attrs π E L rm l rs κ γ T :
  ⌜lctx_lft_alive E L κ⌝ ∗
  (∀ li, resolve_ghost_iter π E L rm true li (ty_syn_type T_ty MetaNone) (replicate (length rs) (◁ T_ty))%I (Owned ) rs [] 0%nat (λ L2 rs' R progress,
    T L2 (#rs') R progress)) ⊢
  resolve_ghost π E L rm true l (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>)) (Uniq κ γ) (#rs) T.
Proof.
Admitted.
Definition resolve_ghost_Vec_T_uniq_inst := [instance @resolve_ghost_Vec_T_uniq].
Global Existing Instance resolve_ghost_Vec_T_uniq_inst.

(** Learning instance overriding the default ones: we don't want all the unnecessary facts from Vec's internal representation *)
Global Program Instance learn_from_hyp_val_vec T_rt A_rt A_attrs (T_ty : type T_rt) (A_ty : type A_rt) r :
  LearnFromHypVal (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>) r :=
  {| learn_from_hyp_val_Q := ⌜length r ≤ MaxInt usize⌝ |}.
Next Obligation.
  iIntros (?????).
  iIntros (r ?? v m ?) "Hv".
  iMod (learn_from_hyp_val_proof with "[] Hv") as "(Hv & Hp)"; first done.
  iFrame "Hv".
  unfold learn_from_hyp_val_Q; simpl.
  iDestruct "Hp" as "(% & Hp)".
  repeat setoid_rewrite boringly_exists.
  repeat setoid_rewrite boringly_sep.
  iDestruct "Hp" as "(% & % & % & % & % & Hp)".
  rewrite !boringly_persistent_elim.
  unfold name_hint.
  iDestruct "Hp" as "(-> & _ & ? & _ & _ & %Hlen & _ & % & _)".
  subst. iModIntro. done.
Qed.

(** Accessors that can be used by unsafe code doing funky stuff *)
Lemma vec_access_elems {T_rt A_rt} (T_ty : type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) π rs l F :
  lftE ⊆ F →
  £ 1 -∗
  l ◁ₗ[π, Owned] #(<#> rs) @ (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>)) ={F}=∗
  ∃ (l' : loc),
    (l' ◁ₗ[π, Owned] # (<#> rs) @ ◁ (array_t (length rs) T_ty)) ∗
    (∀ T_rt' (T_ty' : type T_rt') rs',
      ⌜length rs = length rs'⌝ -∗
      ⌜ty_syn_type T_ty' MetaNone = ty_syn_type T_ty MetaNone⌝ -∗
      (l' ◁ₗ[π, Owned] #(<#> rs') @ ◁ (array_t (length rs) T_ty')) ={F}=∗
      l ◁ₗ[π, Owned] #(<#> rs') @ (◁ (Vec_inv_t T_rt' A_rt A_attrs *[] *[T_ty'; A_ty]))).
Proof.
  iIntros (?) "Hc1".
  rewrite ltype_own_ofty_unfold /lty_of_ty_own/=.
  iIntros "(%ly & %Hst & % & _ & #Hlb & %r' & <- & Hl)".
  iMod (fupd_mask_mono with "Hl") as "Hl"; first done.
  iDestruct "Hl" as "(%v & Hl & Hv)".
  rewrite {1}ex_plain_t_unfold_val/=.
  iDestruct "Hv" as "(%fields & (%cap & %l' & %len & %els & -> & Hls & %Heq1 & %Hlook1 & %Hlook2 & %Hlen_eq & %Hcap & % & %Hbound & _) & Hv)".
  unfold name_hint, name_hint_ty in *.
  simpl in *.
  rewrite /guarded.
  iDestruct "Hls" as "(Hcred & Hls)".
  iApply (lc_fupd_add_later with "Hc1"). iNext.
  iMod (ltype_own_ofty_array_length with "Hls") as "(%Hcap_eq & Hls)"; first done.
  iMod (array_t_ofty_split _ _ _ len (cap - len) with "Hls") as "(Hls & Huninit)".
  { done. }
  { lia. }
  assert (take len els = <#> (Some <$> project_vec_els len els)) as Hels_eq.
  { apply list_eq. intros i.
    do 2 rewrite list_lookup_fmap.
    rewrite lookup_take.
    destruct (decide (i < len)%nat) as [Hlt | Hnlt].
    - opose proof (Hlook1 i _) as Hlook1'; first lia.
      rewrite Hlook1'. rewrite Heq1.
      rewrite list_lookup_lookup_total_lt; first done.
      apply lookup_lt_Some in Hlook1'.
      rewrite project_vec_els_length. lia.
    - rewrite /project_vec_els.
      rewrite list_lookup_fmap.
      rewrite lookup_ge_None_2; first done.
      rewrite length_take. lia. }
  assert (drop len els = <#> replicate (cap - len) None) as Heq'.
  { apply list_eq. intros i.
    rewrite list_lookup_fmap.
    rewrite lookup_drop.
    destruct (replicate (cap - len) (None) !! i) eqn:Heq'.
    { apply lookup_replicate in Heq' as [-> Hlt].
      rewrite Hlook2; first done. lia. }
    apply lookup_replicate_None in Heq'.
    apply lookup_ge_None_2. rewrite Hcap_eq. lia. }
  rewrite Heq'. clear Heq'.
  iEval (rewrite Hels_eq) in "Hls".
  iExists l'.
  rewrite length_fmap in Hlen_eq.
  iPoseProof (ltype_own_has_layout with "Hls") as "(%ly' & %Hst' & %Hlyl)".
  apply syn_type_has_layout_array_inv in Hst' as (ly_T & Hst' & -> & ?).
  iSplitL "Hls".
  { set (R := λ r1 (r2 : T_rt), ⌜r1 = Some (#r2)⌝%I : iProp Σ).
    iMod (ltype_own_array_subtype_strong _ _ _ _ (T_ty) _ _ _ R with "[] Hls") as "(%rs' & HR & Hls)".
    { done. }
    { simpl. apply syn_type_size_eq_refl. }
    { done. }
    { done. }
    { iModIntro. iIntros (??? Heq). revert Heq.
      rewrite list_lookup_fmap.
      destruct (project_vec_els len els !! i) eqn:Hlook; last done.
      intros [=<-].
      apply project_vec_els_lookup_Some in Hlook as (x' & Hlook1' & -> & ?).
      rewrite Hlook1 in Hlook1'; last lia.
      injection Hlook1' as <-. simpl.
      rewrite list_lookup_total_fmap; last lia.
      iIntros "Hv". iPoseProof (ty_own_val_Some_maybe_uninit with "Hv") as "Hv".
      iFrame. done. }
    iPoseProof (big_sepL2_Forall2 with "HR") as "%HR".
    rewrite Hlen_eq.
    enough (rs = rs') as -> by by iFrame.
    move: HR. unfold R. rewrite -Heq1.
    rewrite !Forall2_fmap_l.
    intros Hf. eapply Forall2_eq.
    eapply Forall2_impl; first apply Hf.
    intros ??. simpl. congruence. }
  iModIntro. iIntros (T_rt' T_ty' rs' Hlen' Hst'') "Hls".

  iPoseProof (ltype_own_has_layout with "Hls") as "(%ly' & %Hst3 & %Hlyl')".
  apply syn_type_has_layout_array_inv in Hst3 as (ly_T' & Hst3 & -> & ?).
  rewrite Hst'' in Hst3. assert (ly_T' = ly_T) as -> by by eapply syn_type_has_layout_inj.
  iAssert (|={F}=> l' ◁ₗ[π, Owned] # (<#> (Some <$> (<#> rs'))) @ ◁ array_t (length rs) (maybe_uninit T_ty'))%I with "[Hls]" as ">Hls".
  { set (R := λ (r1 : T_rt') r2, ⌜r2 = Some (#r1)⌝%I : iProp Σ).
    iMod (ltype_own_array_subtype_strong _ _ _ _ (maybe_uninit T_ty') _ _ _ R with "[] Hls") as "(%rs'' & HR & Hls)".
    { done. }
    { simpl. apply syn_type_size_eq_refl. }
    { simpl. rewrite Hst''. done. }
    { done. }
    { iModIntro. iIntros (??? Heq).
      iIntros "Hv". iPoseProof (ty_own_val_maybe_uninit_Some with "Hv") as "Hv".
      iFrame. done. }
    iPoseProof (big_sepL2_Forall2 with "HR") as "%HR".
    apply Forall2_functional in HR as ->.
    eassert ((Some <$> <#> rs') = _) as Heq.
    2: { rewrite Heq. by iFrame. }
    rewrite -list_fmap_compose. solve_goal. }
  simpl.

  iPoseProof (ltype_own_has_layout with "Huninit") as "(%ly4 & %Hst4 & %Hlyl2)".
  apply syn_type_has_layout_array_inv in Hst4 as (ly_T2 & Hst4 & -> & ?).
  simpl in Hst4. assert (ly_T2 = ly_T) as -> by by eapply syn_type_has_layout_inj.
  iMod (ltype_own_array_subtype_strong _ _ _ _ (maybe_uninit T_ty') _ _ _ (λ _ r2, ⌜r2 = None⌝%I : iProp Σ) with "[] Huninit") as "(%rs'' & HR & Huninit)".
  { done. }
  { simpl. rewrite Hst''. apply syn_type_size_eq_refl. }
  { simpl. rewrite Hst''. done. }
  { done. }
  { iModIntro. iIntros (??? Heq). apply lookup_replicate in Heq as (-> & ?).
    iIntros "Hv". iExists None. iR.
    rewrite !maybe_uninit_None_unfold.
    rewrite Hst''. by iFrame. }
  iPoseProof (big_sepL2_Forall2 with "HR") as "%HR".
  apply Forall2_functional in HR as ->.
  simpl.
  rewrite fmap_replicate.

  rewrite Hlen_eq.
  iEval (rewrite -Hst'') in "Huninit".
  iMod (array_t_ofty_merge with "Hls Huninit") as "Hls".
  { done. }
  { simpl. rewrite Hst''.
    move: Hbound. case_decide; first lia.
    unfold size_of_array_in_bytes. rewrite /size_of_st/use_layout_alg' Hst'.
    simpl. nia.  }

  iModIntro. iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own).
  simpl. iExists _. iR. iR. iR. iR.
  iExists _. iR. iModIntro.
  iExists _. iFrame.
  rewrite ex_plain_t_unfold_val/=.
  iExists *[_;_].
  iSplitR "Hv".
  { rewrite /inv_P/=/name_hint_ty/name_hint/=.
    replace (length rs + (cap - length rs))%nat with cap by lia.
    iExists _, _, len, _. iR.
    rewrite /guarded. iFrame. iPureIntro.
    split_and!.
    - rewrite /project_vec_els. normalize_and_simpl_goal.
      rewrite -!list_fmap_compose. solve_goal.
    - intros. rewrite lookup_app_l; last solve_goal.
      opose proof (lookup_lt_is_Some_2 rs' i _) as [? Hlook]; first lia.
      normalize_and_simpl_goal.
      eexists.
      split. { rewrite Hlook. solve_goal. }
      solve_goal.
    - normalize_and_simpl_goal.
      setoid_rewrite lookup_replicate.
      exists None. solve_goal.
    - solve_goal.
    - solve_goal.
    - done.
    - rewrite Hst''. solve_goal.
    - done. }
  rewrite Hlen_eq.
  iApply (struct_t_own_val_mono _ false); last iApply "Hv".
  unfold struct_t_incl_precond. simpl.
  iSplitR; first last.
  { iL. iR. iApply owned_type_incl_refl. }
  iR. rewrite /owned_type_incl/=.
  iSplitR. { iPureIntro. apply syn_type_size_eq_refl. }
  iR.
  iIntros (?) "Hv".
  rewrite !ex_plain_t_unfold_val/=.
  rewrite /inv_P/=.
  iDestruct "Hv" as "(%x & (%a & %Heq & Hfree & _) & Hv)".
  iExists x.
  rewrite Hst''. iFrame.
  iSplitR. { eauto. }
  subst.
  iApply (struct_t_own_val_mono _ false); last iApply "Hv".
  unfold struct_t_incl_precond. simpl.
  iSplitR. { iR. iApply owned_type_incl_refl. }
  iL. iR.
  rewrite /owned_type_incl/=.
  iSplitR. { iPureIntro. apply syn_type_size_eq_refl. }
  iR.
  iIntros (?) "Hv".
  rewrite !ex_plain_t_unfold_val/=.
  iDestruct "Hv" as "(%x & _ & Hv)".
  iExists x. iR.
  iApply (struct_t_own_val_mono _ false); last iApply "Hv".
  unfold struct_t_incl_precond. done.
Qed.

Lemma vec_extract_invariant {T_inner_rt T_rt A_rt} (P : ex_inv_def T_inner_rt T_rt) (T_ty : type T_inner_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) π xs l F :
  lftE ⊆ F →
  £ 1 -∗
  l ◁ₗ[π, Owned] #(<#> xs) @ (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> (∃; P, T_ty) <TY> A_ty <INST!>)) ={F}=∗
  ∃ (xs' : list (RT_rt T_inner_rt)),
  ([∗ list] x1; x2 ∈ xs'; xs, P.(inv_P) π x1 x2) ∗
  (l ◁ₗ[π, Owned] #(<#> xs') @ (◁ (Vec_inv_t T_inner_rt A_rt A_attrs *[] *[T_ty; A_ty]))).
Proof.
  iIntros (?) "Hcred Hl".
  iMod (vec_access_elems with "Hcred Hl") as "(%l' & Hl & Hcl)"; first done.
  iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst & %)".
  apply syn_type_has_layout_array_inv in Hst as (ly_T & ? & -> & ?).
  iMod (ltype_own_array_subtype_strong _ _ _ _ T_ty _ _ _ (λ r1 r2, P.(inv_P) π r2 r1) with "[] Hl") as "(%rs' & Hinv & Hl)".
  { done. }
  { apply syn_type_size_eq_refl. }
  { done. }
  { done. }
  { iModIntro. iIntros (????). rewrite ex_plain_t_unfold_val. eauto. }
  iPoseProof (big_sepL2_length with "Hinv") as "%Hlen'".
  iMod ("Hcl" with "[//] [//] Hl") as "Hl".
  iFrame. rewrite big_sepL2_flip. done.
Qed.

Global Program Instance iterator_learn_vec_intoiter_it T_rt A_rt A_attrs p :
  IteratorLearnInductive (IntoIterTAasstd_iter_Iterator_spec_attrs T_rt A_rt A_attrs) p :=
  {| iterator_learn_inductive_Q s1 hist s2 := s1 = hist ++ s2 |}.
Next Obligation.
  iIntros (??? [] ????) "Hx".
  iPoseProof (boringly_persistent_elim with "Hx") as "Hx".
  iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
  { iDestruct "Hx" as "->". iPureIntro. done. }
  iDestruct "Hx" as "(%s1' & (_ & ->) & Hx)".
  iPoseProof ("IH" with "Hx") as "->".
  done.
Qed.

Global Program Instance iterator_learn_learn_slice_iter T_rt p :
  IteratorLearnInductive (IteraTasstd_iter_Iterator_spec_attrs T_rt) p :=
  {| iterator_learn_inductive_Q s1 hist s2 := s1 = hist ++ s2 |}.
Next Obligation.
  iIntros (? [] ????) "Hx".
  iPoseProof (boringly_persistent_elim with "Hx") as "Hx".
  iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
  { iDestruct "Hx" as "->". iPureIntro. done. }
  iDestruct "Hx" as "(%s1' & (_ & ->) & Hx)".
  iPoseProof ("IH" with "Hx") as "->".
  done.
Qed.

Global Program Instance iterator_learn_learn_slice_iter_mut T_rt p :
  IteratorLearnInductive (IterMutaTasstd_iter_Iterator_spec_attrs T_rt) p :=
  {| iterator_learn_inductive_Q s1 hist s2 := s1 = hist ++ s2 |}.
Next Obligation.
  iIntros (? [] ????) "Hx".
  iPoseProof (boringly_persistent_elim with "Hx") as "Hx".
  iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
  { iDestruct "Hx" as "->". iPureIntro. done. }
  iDestruct "Hx" as "(%s1' & (_ & ->) & Hx)".
  iPoseProof ("IH" with "Hx") as "->".
  done.
Qed.

Lemma simplify_goal_slice_iter_inv T_rt π b p T :
  T
  ⊢ simplify_goal (traits_iterator_Iterator_Inv (IteraTasstd_iter_Iterator_spec_attrs T_rt) π p b) T.
Proof.
  unfold traits_iterator_Iterator_Inv; simpl.
  iIntros "$".
Qed.
Definition simplify_goal_slice_iter_inv_inst := [instance @simplify_goal_slice_iter_inv with 0%N].
Global Existing Instance simplify_goal_slice_iter_inv_inst.

Lemma simplify_goal_vec_intoiter_inv T_rt A_rt A_attrs π b p T :
  T
  ⊢ simplify_goal (traits_iterator_Iterator_Inv (IntoIterTAasstd_iter_Iterator_spec_attrs T_rt A_rt A_attrs) π p b) T.
Proof.
  unfold traits_iterator_Iterator_Inv; simpl.
  iIntros "$".
Qed.
Definition simplify_goal_vec_intoiter_inv_inst := [instance @simplify_goal_vec_intoiter_inv with 0%N].
Global Existing Instance simplify_goal_vec_intoiter_inv_inst.

(* We don't want this to unfold *)
Global Arguments Vec_inv_t : simpl never.
End extra_specs.
Record private_slice_index_Sealed_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_private_slice_index_Sealed_spec {
}.
#[global] Arguments private_slice_index_Sealed_spec : clear implicits.

#[global] Arguments private_slice_index_Sealed_spec {_ _}.


Record SliceIndex_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{T_rt : !RT} `{Output_rt : !RT} : Type := mk_SliceIndex_spec {
  SliceIndex_get_spec  : (spec_with 1 [] fn_spec);
  SliceIndex_get_mut_spec  : (spec_with 1 [] fn_spec);
  SliceIndex_index_spec  : (spec_with 1 [] fn_spec);
  SliceIndex_index_mut_spec  : (spec_with 1 [] fn_spec);
}.
#[global] Arguments SliceIndex_spec : clear implicits.

#[global] Arguments SliceIndex_spec {_ _}.


Section private_slice_index_Sealed.
Context `{RRGS : !refinedrustGS Σ}.
Definition private_slice_index_Sealed_spec_incl `{Self_rt : !RT} (spec1: ((private_slice_index_Sealed_spec (Self_rt)))) (spec2: ((private_slice_index_Sealed_spec (Self_rt)))) : Prop :=
  True.
Instance private_slice_index_Sealed_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (private_slice_index_Sealed_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_private_slice_index_Sealed_spec `{Self_rt : !RT} : (ScopeBindable ((private_slice_index_Sealed_spec (Self_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((private_slice_index_Sealed_spec (Self_rt)))) :=
      s;
    scope_add_elctx (E: (lft → elctx)) (s: ((private_slice_index_Sealed_spec (Self_rt)))) :=
      s;
  |}
.
#[global] Existing Instance scope_bindable_private_slice_index_Sealed_spec.

Definition private_slice_index_Sealed_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((private_slice_index_Sealed_spec_attrs ((Self_rt))))) : (spec_with _ _ (private_slice_index_Sealed_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_private_slice_index_Sealed_spec _ _ ((Self_rt))).

End private_slice_index_Sealed.

Section SliceIndex.
Context `{RRGS : !refinedrustGS Σ}.
Definition SliceIndex_spec_incl `{Self_rt : !RT} `{T_rt : !RT} `{Output_rt : !RT} (spec1: ((SliceIndex_spec (Self_rt) (T_rt) (Output_rt)))) (spec2: ((SliceIndex_spec (Self_rt) (T_rt) (Output_rt)))) : Prop :=
  ((function_subtype (spec1.(SliceIndex_get_spec)) (spec2.(SliceIndex_get_spec)))) ∧ ((function_subtype (spec1.(SliceIndex_get_mut_spec)) (spec2.(SliceIndex_get_mut_spec)))) ∧ ((function_subtype (spec1.(SliceIndex_index_spec)) (spec2.(SliceIndex_index_spec)))) ∧ ((function_subtype (spec1.(SliceIndex_index_mut_spec)) (spec2.(SliceIndex_index_mut_spec)))).
Instance SliceIndex_spec_incl_preorder `{Self_rt : !RT} `{T_rt : !RT} `{Output_rt : !RT} : (PreOrder (SliceIndex_spec_incl (Self_rt := Self_rt) (T_rt := T_rt) (Output_rt := Output_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition scope_bindable_SliceIndex_spec `{Self_rt : !RT} `{T_rt : !RT} `{Output_rt : !RT} : (ScopeBindable ((SliceIndex_spec (Self_rt) (T_rt) (Output_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((SliceIndex_spec (Self_rt) (T_rt) (Output_rt)))) :=
      {|
        SliceIndex_get_spec  :=
          (scope_add_typarams (rts) (tys) (s.(SliceIndex_get_spec)));
        SliceIndex_get_mut_spec  :=
          (scope_add_typarams (rts) (tys) (s.(SliceIndex_get_mut_spec)));
        SliceIndex_index_spec  :=
          (scope_add_typarams (rts) (tys) (s.(SliceIndex_index_spec)));
        SliceIndex_index_mut_spec  :=
          (scope_add_typarams (rts) (tys) (s.(SliceIndex_index_mut_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((SliceIndex_spec (Self_rt) (T_rt) (Output_rt)))) :=
      {|
        SliceIndex_get_spec  :=
          (scope_add_elctx (E) (s.(SliceIndex_get_spec)));
        SliceIndex_get_mut_spec  :=
          (scope_add_elctx (E) (s.(SliceIndex_get_mut_spec)));
        SliceIndex_index_spec  :=
          (scope_add_elctx (E) (s.(SliceIndex_index_spec)));
        SliceIndex_index_mut_spec  :=
          (scope_add_elctx (E) (s.(SliceIndex_index_mut_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_SliceIndex_spec.

Definition SliceIndex_get_base_spec (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([(Self_rt, Self_st); (T_rt, T_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, slice) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: Self_ty, slice :@: (shr_ref ulft_1 T_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexProj) slice self @ (Option_ty ((place_rfnRT (Output_rt))) -[] -[(shr_ref ulft_1 Output_ty)]);
      (* postcondition *) (λ π : thread_id, True).

Definition SliceIndex_get_mut_base_spec (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([(Self_rt, Self_st); (T_rt, T_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, slice) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: Self_ty, slice :@: (mut_ref ulft_1 T_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γi) : ((_)), fmap (λ x, (x, γi)) (SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexProj) slice.cur self) @ (Option_ty (((place_rfnRT (Output_rt)) * gname)%type) -[] -[(mut_ref ulft_1 Output_ty)]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs slice.ghost (if SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexProj) slice.cur self then SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexInj) slice.cur self γi else $#@{ (T_rt) } slice.cur))).

Definition SliceIndex_index_base_spec (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([(Self_rt, Self_st); (T_rt, T_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, slice) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: Self_ty, slice :@: (shr_ref ulft_1 T_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (shr_ref ulft_1 Output_ty);
      (* postcondition *) (λ π : thread_id, (⌜(Some ret = SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexProj) slice self)%Z⌝)).

Definition SliceIndex_index_mut_base_spec (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([(Self_rt, Self_st); (T_rt, T_st); (Output_rt, Output_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, slice) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: Self_ty, slice :@: (mut_ref ulft_1 T_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γi, ret) : ((_ * _)), (ret, γi) @ (mut_ref ulft_1 Output_ty);
      (* postcondition *) (λ π : thread_id, (⌜(Some ret = SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexProj) slice.cur self)%Z⌝)
      ∗ (gvar_pobs slice.ghost (SliceIndex_Self_T_spec_attrs.(SliceIndex_SliceIndexInj) slice.cur self γi))).

Definition SliceIndex_base_spec (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((SliceIndex_spec_attrs ((Self_rt)) ((T_rt)) ((Output_rt)) (private_slice_index_Sealed_Self_spec_attrs)))) : (spec_with _ _ (SliceIndex_spec ((Self_rt)) ((T_rt)) ((Output_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty; T_ty; Output_ty]) : ([Self_rt; T_rt; Output_rt] : list RT), {|
      SliceIndex_get_spec  :=
        (SliceIndex_get_base_spec ((Self_rt)) ((T_rt)) ((Output_rt)) (Self_st) (T_st) (Output_st)) private_slice_index_Sealed_Self_spec_attrs _ATTRS 
           <TY> Self_ty <TY> T_ty <TY> Output_ty : (spec_with 1 [] fn_spec);
      SliceIndex_get_mut_spec  :=
        (SliceIndex_get_mut_base_spec ((Self_rt)) ((T_rt)) ((Output_rt)) (Self_st) (T_st) (Output_st)) private_slice_index_Sealed_Self_spec_attrs _ATTRS 
           <TY> Self_ty <TY> T_ty <TY> Output_ty : (spec_with 1 [] fn_spec);
      SliceIndex_index_spec  :=
        (SliceIndex_index_base_spec ((Self_rt)) ((T_rt)) ((Output_rt)) (Self_st) (T_st) (Output_st)) private_slice_index_Sealed_Self_spec_attrs _ATTRS 
           <TY> Self_ty <TY> T_ty <TY> Output_ty : (spec_with 1 [] fn_spec);
      SliceIndex_index_mut_spec  :=
        (SliceIndex_index_mut_base_spec ((Self_rt)) ((T_rt)) ((Output_rt)) (Self_st) (T_st) (Output_st)) private_slice_index_Sealed_Self_spec_attrs _ATTRS 
           <TY> Self_ty <TY> T_ty <TY> Output_ty : (spec_with 1 [] fn_spec);
    |}
.

End SliceIndex.

Section private_slice_index_Sealed_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End private_slice_index_Sealed_trait_req_incls.

Section SliceIndex_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_SliceIndex_get (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (private_slice_index_Sealed_Self_spec: (spec_with 0 [] (private_slice_index_Sealed_spec (RRGS:=RRGS) (Self_rt)))) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) (SliceIndex_Self_T_spec: (spec_with 0 [] (SliceIndex_spec (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([Self_rt; T_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl private_slice_index_Sealed_spec_incl private_slice_index_Sealed_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), private_slice_index_Sealed_base_spec (Self_rt) Self_st private_slice_index_Sealed_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl SliceIndex_spec_incl SliceIndex_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), SliceIndex_base_spec (Self_rt) (T_rt) (Output_rt) Self_st T_st Output_st private_slice_index_Sealed_Self_spec_attrs SliceIndex_Self_T_spec_attrs-[] -[Self_ty; T_ty; Output_ty])))).
  Definition trait_incl_of_SliceIndex_get_mut (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (private_slice_index_Sealed_Self_spec: (spec_with 0 [] (private_slice_index_Sealed_spec (RRGS:=RRGS) (Self_rt)))) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) (SliceIndex_Self_T_spec: (spec_with 0 [] (SliceIndex_spec (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([Self_rt; T_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl private_slice_index_Sealed_spec_incl private_slice_index_Sealed_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), private_slice_index_Sealed_base_spec (Self_rt) Self_st private_slice_index_Sealed_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl SliceIndex_spec_incl SliceIndex_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), SliceIndex_base_spec (Self_rt) (T_rt) (Output_rt) Self_st T_st Output_st private_slice_index_Sealed_Self_spec_attrs SliceIndex_Self_T_spec_attrs-[] -[Self_ty; T_ty; Output_ty])))).
  Definition trait_incl_of_SliceIndex_index (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (private_slice_index_Sealed_Self_spec: (spec_with 0 [] (private_slice_index_Sealed_spec (RRGS:=RRGS) (Self_rt)))) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) (SliceIndex_Self_T_spec: (spec_with 0 [] (SliceIndex_spec (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([Self_rt; T_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl private_slice_index_Sealed_spec_incl private_slice_index_Sealed_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), private_slice_index_Sealed_base_spec (Self_rt) Self_st private_slice_index_Sealed_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl SliceIndex_spec_incl SliceIndex_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), SliceIndex_base_spec (Self_rt) (T_rt) (Output_rt) Self_st T_st Output_st private_slice_index_Sealed_Self_spec_attrs SliceIndex_Self_T_spec_attrs-[] -[Self_ty; T_ty; Output_ty])))).
  Definition trait_incl_of_SliceIndex_index_mut (Self_rt: RT) (T_rt: RT) (Output_rt: RT) (Self_st: syn_type) (T_st: syn_type) (Output_st: syn_type) (private_slice_index_Sealed_Self_spec_attrs: (private_slice_index_Sealed_spec_attrs (RRGS:=RRGS) (Self_rt) )) (private_slice_index_Sealed_Self_spec: (spec_with 0 [] (private_slice_index_Sealed_spec (RRGS:=RRGS) (Self_rt)))) (SliceIndex_Self_T_spec_attrs: (SliceIndex_spec_attrs (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt) private_slice_index_Sealed_Self_spec_attrs)) (SliceIndex_Self_T_spec: (spec_with 0 [] (SliceIndex_spec (RRGS:=RRGS) (Self_rt) (T_rt) (Output_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty; T_ty; Output_ty]) : ([Self_rt; T_rt; Output_rt] : list RT), ((trait_incl_marker (lift_trait_incl private_slice_index_Sealed_spec_incl private_slice_index_Sealed_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), private_slice_index_Sealed_base_spec (Self_rt) Self_st private_slice_index_Sealed_Self_spec_attrs-[] -[Self_ty]))) ∧ (trait_incl_marker (lift_trait_incl SliceIndex_spec_incl SliceIndex_Self_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), SliceIndex_base_spec (Self_rt) (T_rt) (Output_rt) Self_st T_st Output_st private_slice_index_Sealed_Self_spec_attrs SliceIndex_Self_T_spec_attrs-[] -[Self_ty; T_ty; Output_ty])))).
End SliceIndex_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_Vec_TA_is_empty (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_is_empty (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (self = []) @ bool_t;
      (* postcondition *) (λ π : thread_id, True).


Definition trait_incl_of_Vec_TA_insert (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_insert (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (xs, γ, i, x) : ((_ * _ * (nat) * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) (xs, γ) :@: (mut_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])), Z.of_nat i :@: (int USize), x :@: T_ty;
      (* precondition. *) (λ π : thread_id, (⌜(i ≤ length xs)%Z⌝)
        ∗ (⌜((length xs < MaxInt USize)%Z)%Z⌝)
        ∗ (⌜((size_of_array_in_bytes (ty_syn_type T_ty MetaNone) (2 * length xs) ≤ MaxInt ISize)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs γ (<$#> ((take i xs) ++ [x] ++ (drop i xs))))).

Definition trait_incl_of_Vec_TA_len (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_len (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (xs) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) xs :@: (shr_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, length xs @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Vec_T_new (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_Vec_T_new (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, [] @ (Vec_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_Vec_TA_pop (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_pop (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (xs, γ) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) (xs, γ) :@: (mut_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (last xs) @ (Option_ty ((T_rt)) -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (gvar_pobs γ (take (length xs - 1) (<$#> xs)))).

Definition trait_incl_of_Vec_TA_push (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_push (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (xs, γ, x) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) (xs, γ) :@: (mut_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])), x :@: T_ty;
      (* precondition. *) (λ π : thread_id, (⌜((length xs < MaxInt USize)%Z)%Z⌝)
        ∗ (⌜((size_of_array_in_bytes (ty_syn_type T_ty MetaNone) (2 * length xs) ≤ MaxInt ISize)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs γ (<$#> (xs ++ [ x])))).

Definition trait_incl_of_Vec_TA_remove (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_remove (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (xs, γ, i) : ((_ * _ * (nat))),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) (xs, γ) :@: (mut_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])), Z.of_nat i :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(i < length xs)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, xs !!! i @ T_ty;
      (* postcondition *) (λ π : thread_id, (gvar_pobs γ (delete i (<$#> xs)))).

Definition trait_incl_of_Vec_TA_swap_remove (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_Vec_TA_swap_remove (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, index) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (mut_ref ulft_1 (Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])), index :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(index < length self.cur)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (xs) : ((_)), self.cur !!! Z.to_nat index @ T_ty;
      (* postcondition *) (λ π : thread_id, (⌜(take (Z.to_nat index) self.cur = take (Z.to_nat index) xs)%Z⌝)
      ∗ (⌜(length xs = (length self.cur - 1)%nat)%Z⌝)
      ∗ (gvar_pobs self.ghost (<$#> xs))).

Definition trait_incl_of_Vec_T_with_capacity (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_Vec_T_with_capacity (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (cap) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) cap :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜((size_of_array_in_bytes (ty_syn_type T_ty MetaNone) (Z.to_nat cap) ≤ MaxInt ISize)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, [] @ (Vec_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_vec_from_elem (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) (Clone_T_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (T_rt) T_st Clone_T_spec_attrs-[] -[T_ty])))).

Definition type_of_vec_from_elem (T_rt: RT) (T_st: syn_type) (Clone_T_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (elem, n) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) elem :@: T_ty, n :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜((size_of_array_in_bytes (ty_syn_type T_ty MetaNone) (2 * (Z.to_nat n)) ≤ MaxInt ISize)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, replicate (Z.to_nat n) elem @ (Vec_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_IntoIterTAasstd_iter_Iterator_next (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_IntoIterTAasstd_iter_Iterator_next (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; A_ty] (scope_add_elctx (λ ϝ, []) (((traits_iterator_Iterator_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) ((IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs))))
    -[] -[(IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]); T_ty]).(traits_iterator_Iterator_next_spec)   a b))) <MERGE!>.

Definition trait_incl_of_IteraTasstd_iter_Iterator_all (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFaT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnOnce_F_REFaT_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool))) (FnMut_F_REFaT_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnMut_F_REFaT_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty; F_ty]) : ([T_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFaT_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool F_st ((tuple1_sls (PtrSynType)) : syn_type) BoolSynType FnOnce_F_REFaT_spec_attrs-[] -[F_ty; (tuple1_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_a T_ty)]); bool_t]))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFaT_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool F_st ((tuple1_sls (PtrSynType)) : syn_type) BoolSynType FnOnce_F_REFaT_spec_attrs FnMut_F_REFaT_spec_attrs-[] -[F_ty; (tuple1_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_a T_ty)]); bool_t])))).

Definition type_of_IteraTasstd_iter_Iterator_all (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFaT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnMut_F_REFaT_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) :=
  spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [] ++ ty_outlives_E (T_ty) ulft_a) (((traits_iterator_Iterator_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType) ((IteraTasstd_iter_Iterator_spec_attrs (T_rt))))
    -[] -[(Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]); (shr_ref ulft_a T_ty)]).(traits_iterator_Iterator_all_spec) F_rt F_st FnOnce_F_REFaT_spec_attrs FnMut_F_REFaT_spec_attrs a b))) <MERGE!>.

Definition trait_incl_of_IteraTasstd_iter_Iterator_next (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_IteraTasstd_iter_Iterator_next (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [] ++ ty_outlives_E (T_ty) ulft_a) (((traits_iterator_Iterator_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType) ((IteraTasstd_iter_Iterator_spec_attrs (T_rt))))
    -[] -[(Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]); (shr_ref ulft_a T_ty)]).(traits_iterator_Iterator_next_spec)   a b))) <MERGE!>.

Definition trait_incl_of_IteraTasstd_iter_Iterator_position (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFaT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnOnce_F_REFaT_spec: (spec_with 0 [] (FnOnce_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool))) (FnMut_F_REFaT_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnMut_F_REFaT_spec: (spec_with 0 [] (FnMut_spec (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty; F_ty]) : ([T_rt; F_rt] : list RT), ((trait_incl_marker (lift_trait_incl FnOnce_spec_incl FnOnce_F_REFaT_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnOnce_base_spec (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool F_st ((tuple1_sls (PtrSynType)) : syn_type) BoolSynType FnOnce_F_REFaT_spec_attrs-[] -[F_ty; (tuple1_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_a T_ty)]); bool_t]))) ∧ (trait_incl_marker (lift_trait_incl FnMut_spec_incl FnMut_F_REFaT_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), FnMut_base_spec (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool F_st ((tuple1_sls (PtrSynType)) : syn_type) BoolSynType FnOnce_F_REFaT_spec_attrs FnMut_F_REFaT_spec_attrs-[] -[F_ty; (tuple1_ty ((place_rfnRT (T_rt))) -[] -[(shr_ref ulft_a T_ty)]); bool_t])))).

Definition type_of_IteraTasstd_iter_Iterator_position (T_rt: RT) (F_rt: RT) (T_st: syn_type) (F_st: syn_type) (FnOnce_F_REFaT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnMut_F_REFaT_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) :=
  spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [] ++ ty_outlives_E (T_ty) ulft_a) (((traits_iterator_Iterator_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType) ((IteraTasstd_iter_Iterator_spec_attrs (T_rt))))
    -[] -[(Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]); (shr_ref ulft_a T_ty)]).(traits_iterator_Iterator_position_spec) F_rt F_st FnOnce_F_REFaT_spec_attrs FnMut_F_REFaT_spec_attrs a b))) <MERGE!>.

Definition trait_incl_of_IterMutaTasstd_iter_Iterator_next (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_a; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_IterMutaTasstd_iter_Iterator_next (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, [] ++ ty_outlives_E (T_ty) ulft_a) (((traits_iterator_Iterator_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((IterMut_st (T_st))) (PtrSynType) ((IterMutaTasstd_iter_Iterator_spec_attrs (T_rt))))
    -[] -[(IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]); (mut_ref ulft_a T_ty)]).(traits_iterator_Iterator_next_spec)   a b))) <MERGE!>.

Definition trait_incl_of_VecTAasstd_iter_IntoIterator_into_iter (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec: (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ((trait_incl_marker (lift_trait_incl Allocator_spec_incl Allocator_A_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st Allocator_A_spec_attrs-[] -[A_ty])))).

Definition type_of_VecTAasstd_iter_IntoIterator_into_iter (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty; A_ty] (scope_add_elctx (λ ϝ, []) (((traits_iterator_IntoIterator_base_spec (((Vec_inv_t_rt ((T_rt)) ((A_rt))))) (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((Vec_st (T_st) (A_st))) ((IntoIter_st (T_st) (A_st))) (T_st) ((VecTAasstd_iter_IntoIterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs))))
    -[] -[(Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]); (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]); T_ty]).(traits_iterator_IntoIterator_into_iter_spec)   a b))) <MERGE!>.

Definition trait_incl_of_VecTasstd_iter_FromIteratorT_from_iter (T_rt: RT) (I_rt: RT) (traits_iterator_IntoIterator_I_IntoIter_rt: RT) (T_st: syn_type) (I_st: syn_type) (traits_iterator_IntoIterator_I_IntoIter_st: syn_type) (traits_iterator_IntoIterator_I_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_IntoIterator_I_IntoIter_rt) (T_rt) )) (traits_iterator_IntoIterator_I_spec: (spec_with 0 [] (traits_iterator_IntoIterator_spec (RRGS:=RRGS) (I_rt) (traits_iterator_IntoIterator_I_IntoIter_rt) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; I_ty; traits_iterator_IntoIterator_I_IntoIter_ty]) : ([T_rt; I_rt; traits_iterator_IntoIterator_I_IntoIter_rt] : list RT), ((trait_incl_marker (lift_trait_incl traits_iterator_IntoIterator_spec_incl traits_iterator_IntoIterator_I_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), traits_iterator_IntoIterator_base_spec (I_rt) (traits_iterator_IntoIterator_I_IntoIter_rt) (T_rt) I_st traits_iterator_IntoIterator_I_IntoIter_st T_st traits_iterator_IntoIterator_I_spec_attrs-[] -[I_ty; traits_iterator_IntoIterator_I_IntoIter_ty; T_ty])))).

Definition type_of_VecTasstd_iter_FromIteratorT_from_iter (T_rt: RT) (I_rt: RT) (traits_iterator_IntoIterator_I_IntoIter_rt: RT) (T_st: syn_type) (I_st: syn_type) (traits_iterator_IntoIterator_I_IntoIter_st: syn_type) (traits_iterator_IntoIterator_I_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_IntoIterator_I_IntoIter_rt) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_typarams _ -[T_ty] (scope_add_elctx (λ ϝ, []) (((traits_iterator_FromIterator_base_spec (((Vec_inv_t_rt ((T_rt)) ((((Global_rt))))))) ((T_rt)) ((Vec_st (T_st) ((Global_sls : syn_type)))) (T_st) ((VecTasstd_iter_FromIteratorT_spec_attrs (T_rt))))
    -[] -[(Vec_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]); T_ty]).(traits_iterator_FromIterator_from_iter_spec) I_rt traits_iterator_IntoIterator_I_IntoIter_rt I_st traits_iterator_IntoIterator_I_IntoIter_st traits_iterator_IntoIterator_I_spec_attrs a b))) <MERGE!>.

Definition trait_incl_of_vec_iter_mut (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_vec_iter_mut (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) x :@: (mut_ref ulft_1 (Vec_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]));
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (γs) : ((_)), zip x.cur γs @ (IterMut_inv_t ((T_rt))  -[ulft_1] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (⌜(length γs = length x.cur)%Z⌝)
      ∗ (gvar_pobs x.ghost ((PlaceGhost <$> γs) : list (place_rfn (T_rt))))).



End specs.
Section IntoIterTAasstd_iter_Iterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition IntoIterTAasstd_iter_Iterator_spec (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (traits_iterator_Iterator_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), let Item_rt := (T_rt) in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_all_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((F_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (F_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfasstd_iter_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((B_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (B_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) traits_iterator_FromIterator_B_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((B_rt)) ((F_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (B_st) (F_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((B_rt)) ((F_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (B_st) (F_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfasstd_iter_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (Ord_Selfasstd_iter_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((IntoIter_st (T_st) (A_st))) (T_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Ord_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((F_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (F_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfasstd_iter_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (Ord_Selfasstd_iter_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((IntoIter_st (T_st) (A_st))) (T_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Ord_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((F_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (F_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_IntoIterTAasstd_iter_Iterator_next ((T_rt)) ((A_rt)) (T_st) (A_st)) Allocator_A_spec_attrs 
             <TY> T_ty <TY> A_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((IntoIter_st (T_st) (A_st))) (T_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) 
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (P_rt: RT) (P_st: syn_type) (FnOnce_P_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_P_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_position_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((P_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (P_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_P_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_P_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 1 [P_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((F_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (F_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((IntoIter_st (T_st) (A_st))) (T_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) 
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((IntoIter_st (T_st) (A_st))) (T_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) 
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) ((IntoIter_st (T_st) (A_st))) (T_st) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs)) FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]) <TY> T_ty : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition IntoIterTAasstd_iter_Iterator_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (IntoIterTAasstd_iter_Iterator_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs))-[] -[T_ty; A_ty]) (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), scope_add_typarams _ -[T_ty; A_ty] ((traits_iterator_Iterator_base_spec ((IntoIter_inv_t_rt ((T_rt)) ((A_rt)))) (T_rt) (IntoIter_st (T_st) (A_st)) T_st (IntoIterTAasstd_iter_Iterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs))-[] -[(IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]); T_ty])))).
End IntoIterTAasstd_iter_Iterator_spec.

Section IteraTasstd_iter_Iterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition IteraTasstd_iter_Iterator_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (traits_iterator_Iterator_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), let Item_rt := (place_rfnRT (T_rt)) in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFaT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnMut_F_REFaT_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) :=
          (type_of_IteraTasstd_iter_Iterator_all ((T_rt)) ((F_rt)) (T_st) (F_st)) FnOnce_F_REFaT_spec_attrs FnMut_F_REFaT_spec_attrs
             <TY> T_ty <LFT> ulft_a : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfasstd_iter_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((B_rt)) ((Iter_st (T_st))) (PtrSynType) (B_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) traits_iterator_FromIterator_B_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((B_rt)) ((F_rt)) ((Iter_st (T_st))) (PtrSynType) (B_st) (F_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((B_rt)) ((F_rt)) ((Iter_st (T_st))) (PtrSynType) (B_st) (F_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfasstd_iter_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (Ord_Selfasstd_iter_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Ord_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((F_rt)) ((Iter_st (T_st))) (PtrSynType) (F_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfasstd_iter_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (Ord_Selfasstd_iter_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Ord_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((F_rt)) ((Iter_st (T_st))) (PtrSynType) (F_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_IteraTasstd_iter_Iterator_next ((T_rt)) (T_st)) 
             <TY> T_ty <LFT> ulft_a : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) 
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFaT_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) (FnMut_F_REFaT_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((place_rfnRT (T_rt))))) bool )) :=
          (type_of_IteraTasstd_iter_Iterator_position ((T_rt)) ((F_rt)) (T_st) (F_st)) FnOnce_F_REFaT_spec_attrs FnMut_F_REFaT_spec_attrs
             <TY> T_ty <LFT> ulft_a : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((F_rt)) ((Iter_st (T_st))) (PtrSynType) (F_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) 
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((Iter_st (T_st))) (PtrSynType)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) 
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((Iter_inv_t_rt ((T_rt))))) ((place_rfnRT (T_rt))) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) ((Iter_st (T_st))) (PtrSynType) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (IteraTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (shr_ref ulft_a T_ty) : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition IteraTasstd_iter_Iterator_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (IteraTasstd_iter_Iterator_spec (T_rt) (T_st))-[ulft_a] -[T_ty]) (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((traits_iterator_Iterator_base_spec ((Iter_inv_t_rt ((T_rt)))) (place_rfnRT (T_rt)) (Iter_st (T_st)) PtrSynType (IteraTasstd_iter_Iterator_spec_attrs (T_rt))-[] -[(Iter_inv_t ((T_rt))  -[ulft_a] -[T_ty]); (shr_ref ulft_a T_ty)])))).
End IteraTasstd_iter_Iterator_spec.

Section IterMutaTasstd_iter_Iterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition IterMutaTasstd_iter_Iterator_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (traits_iterator_Iterator_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type))) :=
    spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), let Item_rt := ((place_rfnRT (T_rt)) * gname)%type in {|
        traits_iterator_Iterator_all_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_all_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((F_rt)) ((IterMut_st (T_st))) (PtrSynType) (F_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 1 [F_rt] fn_spec);
        traits_iterator_Iterator_collect_spec (B_rt: RT) (B_st: syn_type) (traits_iterator_FromIterator_B_Selfasstd_iter_Iterator_Item_spec_attrs: (traits_iterator_FromIterator_spec_attrs (RRGS:=RRGS) (B_rt) (Item_rt) )) :=
          (traits_iterator_Iterator_collect_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((B_rt)) ((IterMut_st (T_st))) (PtrSynType) (B_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) traits_iterator_FromIterator_B_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [B_rt] fn_spec);
        traits_iterator_Iterator_fold_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) (FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_fold_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((B_rt)) ((F_rt)) ((IterMut_st (T_st))) (PtrSynType) (B_st) (F_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_map_spec (B_rt: RT) (F_rt: RT) (B_st: syn_type) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) (FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple1_rt) ((Item_rt)))) (B_rt) )) :=
          (traits_iterator_Iterator_map_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((B_rt)) ((F_rt)) ((IterMut_st (T_st))) (PtrSynType) (B_st) (F_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [B_rt; F_rt] fn_spec);
        traits_iterator_Iterator_max_spec (PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfasstd_iter_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (Ord_Selfasstd_iter_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_max_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((IterMut_st (T_st))) (PtrSynType)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Ord_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_max_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_max_by_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((F_rt)) ((IterMut_st (T_st))) (PtrSynType) (F_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_min_spec (PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialEq_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) )) (Eq_Selfasstd_iter_Iterator_Item_spec_attrs: (Eq_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs: (PartialOrd_spec_attrs (RRGS:=RRGS) (Item_rt) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) (Ord_Selfasstd_iter_Iterator_Item_spec_attrs: (Ord_spec_attrs (RRGS:=RRGS) (Item_rt) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs)) :=
          (traits_iterator_Iterator_min_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((IterMut_st (T_st))) (PtrSynType)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) PartialEq_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Eq_Selfasstd_iter_Iterator_Item_spec_attrs PartialOrd_Selfasstd_iter_Iterator_Item_Selfasstd_iter_Iterator_Item_spec_attrs Ord_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_min_by_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) (FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((place_rfnRT (Item_rt))) ((place_rfnRT (Item_rt))))) (((Ordering_rt))) )) :=
          (traits_iterator_Iterator_min_by_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((F_rt)) ((IterMut_st (T_st))) (PtrSynType) (F_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_REFSelfasstd_iter_Iterator_ItemREFSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_next_spec  :=
          (type_of_IterMutaTasstd_iter_Iterator_next ((T_rt)) (T_st)) 
             <TY> T_ty <LFT> ulft_a : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_nth_spec  :=
          (traits_iterator_Iterator_nth_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((IterMut_st (T_st))) (PtrSynType)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) 
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 1 [] fn_spec);
        traits_iterator_Iterator_position_spec (P_rt: RT) (P_st: syn_type) (FnOnce_P_Selfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((Item_rt)))) bool )) (FnMut_P_Selfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (P_rt) (((tuple1_rt) ((Item_rt)))) bool )) :=
          (traits_iterator_Iterator_position_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((P_rt)) ((IterMut_st (T_st))) (PtrSynType) (P_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_P_Selfasstd_iter_Iterator_Item_spec_attrs FnMut_P_Selfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 1 [P_rt] fn_spec);
        traits_iterator_Iterator_reduce_spec (F_rt: RT) (F_st: syn_type) (FnOnce_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) (FnMut_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((Item_rt)) ((Item_rt)))) (Item_rt) )) :=
          (traits_iterator_Iterator_reduce_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((F_rt)) ((IterMut_st (T_st))) (PtrSynType) (F_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs FnMut_F_Selfasstd_iter_Iterator_ItemSelfasstd_iter_Iterator_Item_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [F_rt] fn_spec);
        traits_iterator_Iterator_skip_spec  :=
          (traits_iterator_Iterator_skip_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((IterMut_st (T_st))) (PtrSynType)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) 
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_take_spec  :=
          (traits_iterator_Iterator_take_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((IterMut_st (T_st))) (PtrSynType)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) 
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 0 [] fn_spec);
        traits_iterator_Iterator_try_fold_spec (B_rt: RT) (F_rt: RT) (R_rt: RT) (Try_R_Residual_rt: RT) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) (FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnOnce_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs: (FromResidual_spec_attrs (RRGS:=RRGS) (R_rt) (Try_R_Residual_rt) )) (FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs: (FnMut_spec_attrs (RRGS:=RRGS) (F_rt) (((tuple2_rt) ((B_rt)) ((Item_rt)))) (R_rt) )) (Try_R_spec_attrs: (Try_spec_attrs (RRGS:=RRGS) (R_rt) (B_rt) (Try_R_Residual_rt) FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs)) :=
          (traits_iterator_Iterator_try_fold_base_spec (((IterMut_inv_t_rt ((T_rt))))) (((place_rfnRT (T_rt)) * gname)%type) ((B_rt)) ((F_rt)) ((R_rt)) ((Try_R_Residual_rt)) ((IterMut_st (T_st))) (PtrSynType) (B_st) (F_st) (R_st) (Try_R_Residual_st)) (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt)) FnOnce_F_BSelfasstd_iter_Iterator_Item_spec_attrs FromResidual_R_Rasstd_ops_Try_Residual_spec_attrs FnMut_F_BSelfasstd_iter_Iterator_Item_spec_attrs Try_R_spec_attrs
             <TY> (IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]) <TY> (mut_ref ulft_a T_ty) : (spec_with 1 [B_rt; F_rt; R_rt; Try_R_Residual_rt] fn_spec);
      |}
  .
  Definition IterMutaTasstd_iter_Iterator_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl traits_iterator_Iterator_spec_incl (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (IterMutaTasstd_iter_Iterator_spec (T_rt) (T_st))-[ulft_a] -[T_ty]) (spec! ( *[ulft_a]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((traits_iterator_Iterator_base_spec ((IterMut_inv_t_rt ((T_rt)))) ((place_rfnRT (T_rt)) * gname)%type (IterMut_st (T_st)) PtrSynType (IterMutaTasstd_iter_Iterator_spec_attrs (T_rt))-[] -[(IterMut_inv_t ((T_rt))  -[ulft_a] -[T_ty]); (mut_ref ulft_a T_ty)])))).
End IterMutaTasstd_iter_Iterator_spec.

Section VecTAasstd_iter_IntoIterator_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition VecTAasstd_iter_IntoIterator_spec (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (traits_iterator_IntoIterator_spec (((Vec_inv_t_rt ((T_rt)) ((A_rt))))) (((IntoIter_inv_t_rt ((T_rt)) ((A_rt))))) ((T_rt)))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), let Item_rt := (T_rt) in let IntoIter_rt := ((IntoIter_inv_t_rt ((T_rt)) ((A_rt)))) in {|
        traits_iterator_IntoIterator_into_iter_spec  :=
          (type_of_VecTAasstd_iter_IntoIterator_into_iter ((T_rt)) ((A_rt)) (T_st) (A_st)) Allocator_A_spec_attrs 
             <TY> T_ty <TY> A_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Definition VecTAasstd_iter_IntoIterator_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl traits_iterator_IntoIterator_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (VecTAasstd_iter_IntoIterator_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs))-[] -[T_ty; A_ty]) (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), scope_add_typarams _ -[T_ty; A_ty] ((traits_iterator_IntoIterator_base_spec ((Vec_inv_t_rt ((T_rt)) ((A_rt)))) ((IntoIter_inv_t_rt ((T_rt)) ((A_rt)))) (T_rt) (Vec_st (T_st) (A_st)) (IntoIter_st (T_st) (A_st)) T_st (VecTAasstd_iter_IntoIterator_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs))-[] -[(Vec_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]); (IntoIter_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]); T_ty])))).
End VecTAasstd_iter_IntoIterator_spec.

Section VecTasstd_iter_FromIteratorT_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition VecTasstd_iter_FromIteratorT_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (traits_iterator_FromIterator_spec (((Vec_inv_t_rt ((T_rt)) ((((Global_rt))))))) ((T_rt)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        traits_iterator_FromIterator_from_iter_spec (I_rt: RT) (traits_iterator_IntoIterator_I_IntoIter_rt: RT) (I_st: syn_type) (traits_iterator_IntoIterator_I_IntoIter_st: syn_type) (traits_iterator_IntoIterator_I_spec_attrs: (traits_iterator_IntoIterator_spec_attrs (RRGS:=RRGS) (I_rt) (traits_iterator_IntoIterator_I_IntoIter_rt) (T_rt) )) :=
          (type_of_VecTasstd_iter_FromIteratorT_from_iter ((T_rt)) ((I_rt)) ((traits_iterator_IntoIterator_I_IntoIter_rt)) (T_st) (I_st) (traits_iterator_IntoIterator_I_IntoIter_st)) traits_iterator_IntoIterator_I_spec_attrs
             <TY> T_ty : (spec_with 0 [I_rt; traits_iterator_IntoIterator_I_IntoIter_rt] fn_spec);
      |}
  .
  Definition VecTasstd_iter_FromIteratorT_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl traits_iterator_FromIterator_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (VecTasstd_iter_FromIteratorT_spec (T_rt) (T_st))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_typarams _ -[T_ty] ((traits_iterator_FromIterator_base_spec ((Vec_inv_t_rt ((T_rt)) ((((Global_rt)))))) (T_rt) (Vec_st (T_st) ((Global_sls : syn_type))) T_st (VecTasstd_iter_FromIteratorT_spec_attrs (T_rt))-[] -[(Vec_inv_t ((T_rt)) ((((Global_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_ty  -[] -[])]); T_ty])))).
End VecTasstd_iter_FromIteratorT_spec.

Section usizeasprivate_slice_index_Sealed_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasprivate_slice_index_Sealed_spec  : (spec_with _ _ (private_slice_index_Sealed_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_private_slice_index_Sealed_spec _ _ (Z)).
  Definition usizeasprivate_slice_index_Sealed_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl private_slice_index_Sealed_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasprivate_slice_index_Sealed_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((private_slice_index_Sealed_base_spec Z (IntSynType USize) usizeasprivate_slice_index_Sealed_spec_attrs-[] -[(int USize)])))).
End usizeasprivate_slice_index_Sealed_spec.

