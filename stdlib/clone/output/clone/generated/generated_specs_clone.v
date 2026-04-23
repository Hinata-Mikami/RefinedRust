From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.clone.clone Require Export generated_code_clone.

Record Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Clone_spec_attrs {
}.
#[global] Arguments Clone_spec_attrs : clear implicits.

#[global] Arguments Clone_spec_attrs {_ _}.

#[global] Arguments mk_Clone_spec_attrs  {_} {_} {_}.


Record Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Clone_Self_spec_attrs : !(Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )} : Type := mk_Copy_spec_attrs {
}.
#[global] Arguments Copy_spec_attrs : clear implicits.

#[global] Arguments Copy_spec_attrs {_ _}.

#[global] Arguments mk_Copy_spec_attrs  {_} {_} {_} {_}.


Definition Copy_semantic_interp `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Self_ty: (type (Self_rt))) : Prop :=
  Copyable Self_ty.
Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition constTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Clone_spec_attrs (loc))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition mutTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Clone_spec_attrs (loc))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition boolasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (bool))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition charasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs (Z))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition constTasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Copy_spec_attrs (loc) ((constTasClone_spec_attrs ((T_rt)))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition mutTasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Copy_spec_attrs (loc) ((mutTasClone_spec_attrs ((T_rt)))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition boolasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (bool) (boolasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition charasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (charasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i128asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i128asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i16asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i16asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i32asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i32asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i64asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i64asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition i8asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (i8asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition isizeasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (isizeasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u128asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u128asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u16asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u16asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u32asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u32asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u64asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u64asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition u8asCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (u8asClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition usizeasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs (Z) (usizeasClone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_marker_PhantomDataTasClone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Clone_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition std_marker_PhantomDataTasCopy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) : ((Copy_spec_attrs ((((core_marker_PhantomData_rt) ((T_rt))))) ((std_marker_PhantomDataTasClone_spec_attrs ((T_rt)))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Existing Class Copy_semantic_interp. 
Global Instance Copy_semantic_Copyable `{!refinedrustGS Σ} {rt} (ty : type rt) : 
  Copy_semantic_interp rt ty →
  Copyable ty.
Proof. done. Qed.
End extra_specs.
Record Clone_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Clone_spec {
  Clone_clone_spec  : (spec_with 1 [] fn_spec);
  Clone_clone_from_spec  : (spec_with 2 [] fn_spec);
}.
#[global] Arguments Clone_spec : clear implicits.

#[global] Arguments Clone_spec {_ _}.


Record Copy_spec `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} : Type := mk_Copy_spec {
}.
#[global] Arguments Copy_spec : clear implicits.

#[global] Arguments Copy_spec {_ _}.


Section Clone.
Context `{RRGS : !refinedrustGS Σ}.
Definition Clone_spec_incl `{Self_rt : !RT} (spec1: ((Clone_spec (Self_rt)))) (spec2: ((Clone_spec (Self_rt)))) : Prop :=
  ((function_subtype (spec1.(Clone_clone_spec)) (spec2.(Clone_clone_spec)))) ∧ ((function_subtype (spec1.(Clone_clone_from_spec)) (spec2.(Clone_clone_from_spec)))).
Instance Clone_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Clone_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition Clone_clone_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) self :@: (shr_ref ulft_1 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ Self_ty;
      (* postcondition *) (λ π : thread_id, True).

Definition Clone_clone_from_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([(Self_rt, Self_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self, source) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) self :@: (mut_ref ulft_1 Self_ty), source :@: (shr_ref ulft_2 Self_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs self.ghost (($#@{ (Self_rt) } source)))).

Definition Clone_base_spec (Self_rt: RT) (Self_st: syn_type) (_ATTRS: ((Clone_spec_attrs ((Self_rt))))) : (spec_with _ _ (Clone_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), {|
      Clone_clone_spec  :=
        (Clone_clone_base_spec ((Self_rt)) (Self_st)) _ATTRS 
           <TY> Self_ty : (spec_with 1 [] fn_spec);
      Clone_clone_from_spec  :=
        (Clone_clone_from_base_spec ((Self_rt)) (Self_st)) _ATTRS 
           <TY> Self_ty : (spec_with 2 [] fn_spec);
    |}
.

End Clone.

Section Copy.
Context `{RRGS : !refinedrustGS Σ}.
Definition Copy_spec_incl `{Self_rt : !RT} (spec1: ((Copy_spec (Self_rt)))) (spec2: ((Copy_spec (Self_rt)))) : Prop :=
  True.
Instance Copy_spec_incl_preorder `{Self_rt : !RT} : (PreOrder (Copy_spec_incl (Self_rt := Self_rt))).
Proof.
  split.
  all: apply _.
Qed.

Definition Copy_base_spec (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (_ATTRS: ((Copy_spec_attrs ((Self_rt)) (Clone_Self_spec_attrs)))) : (spec_with _ _ (Copy_spec ((Self_rt)))) :=
  spec! ( *[]) : 0 | ( *[Self_ty]) : ([Self_rt] : list RT), (@mk_Copy_spec _ _ ((Self_rt))).

End Copy.

Section Clone_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_Clone_clone (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1]) : 1 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>)))).
  Definition trait_incl_of_Clone_clone_from (Self_rt: RT) (Self_st: syn_type) (Clone_Self_spec_attrs: (Clone_spec_attrs (RRGS:=RRGS) (Self_rt) )) (Clone_Self_spec: (spec_with 0 [] (Clone_spec (RRGS:=RRGS) (Self_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[ulft_1; ulft_2]) : 2 | ( *[Self_ty]) : ([Self_rt] : list RT), ((trait_incl_marker (lift_trait_incl Clone_spec_incl Clone_Self_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Clone_base_spec (Self_rt) Self_st Clone_Self_spec_attrs<TY> Self_ty <INST!>)))).
End Clone_trait_req_incls.

Section Copy_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
End Copy_trait_req_incls.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_constTasClone_clone (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_constTasClone_clone (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),((Clone_base_spec (loc) (PtrSynType) ((constTasClone_spec_attrs (T_rt))))
     <TY> alias_ptr_t <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_mutTasClone_clone (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_mutTasClone_clone (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),((Clone_base_spec (loc) (PtrSynType) ((mutTasClone_spec_attrs (T_rt))))
     <TY> alias_ptr_t <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_boolasClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_boolasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (bool) (BoolSynType) (boolasClone_spec_attrs))
     <TY> bool_t <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_charasClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_charasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) (CharSynType) (charasClone_spec_attrs))
     <TY> char_t <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_i128asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i128asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType I128)) (i128asClone_spec_attrs))
     <TY> (int I128) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_i16asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i16asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType I16)) (i16asClone_spec_attrs))
     <TY> (int I16) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_i32asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i32asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType I32)) (i32asClone_spec_attrs))
     <TY> (int I32) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_i64asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i64asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType I64)) (i64asClone_spec_attrs))
     <TY> (int I64) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_i8asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_i8asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType I8)) (i8asClone_spec_attrs))
     <TY> (int I8) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_isizeasClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_isizeasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType ISize)) (isizeasClone_spec_attrs))
     <TY> (int ISize) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_u128asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u128asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType U128)) (u128asClone_spec_attrs))
     <TY> (int U128) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_u16asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u16asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType U16)) (u16asClone_spec_attrs))
     <TY> (int U16) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_u32asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u32asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType U32)) (u32asClone_spec_attrs))
     <TY> (int U32) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_u64asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u64asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType U64)) (u64asClone_spec_attrs))
     <TY> (int U64) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_u8asClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_u8asClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType U8)) (u8asClone_spec_attrs))
     <TY> (int U8) <INST!>).(Clone_clone_spec)   <MERGE!>.

Definition trait_incl_of_usizeasClone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_usizeasClone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),((Clone_base_spec (Z) ((IntSynType USize)) (usizeasClone_spec_attrs))
     <TY> (int USize) <INST!>).(Clone_clone_spec)   <MERGE!>.


Definition trait_incl_of_std_marker_PhantomDataTasClone_clone (T_rt: RT) (T_st: syn_type) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (True).

Definition type_of_std_marker_PhantomDataTasClone_clone (T_rt: RT) (T_st: syn_type) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),((Clone_base_spec ((((core_marker_PhantomData_rt) ((T_rt))))) (((core_marker_PhantomData_sls (T_st)) : syn_type)) ((std_marker_PhantomDataTasClone_spec_attrs (T_rt))))
     <TY> (core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>) <INST!>).(Clone_clone_spec)   <MERGE!>.



End specs.
Section constTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition constTasClone_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Clone_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_constTasClone_clone ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (loc) (PtrSynType)) (constTasClone_spec_attrs (T_rt)) 
             <TY> alias_ptr_t : (spec_with 2 [] fn_spec);
      |}
  .
  Definition constTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (constTasClone_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Clone_base_spec loc PtrSynType (constTasClone_spec_attrs (T_rt))<TY> alias_ptr_t <INST!>))).
End constTasClone_spec.

Section constTasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition constTasCopy_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Copy_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (loc)).
  Definition constTasCopy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (constTasCopy_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Copy_base_spec loc PtrSynType (constTasClone_spec_attrs ((T_rt))) (constTasCopy_spec_attrs (T_rt))<TY> alias_ptr_t <INST!>))).
  Lemma constTasCopy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp loc alias_ptr_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End constTasCopy_spec.

Section mutTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition mutTasClone_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Clone_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_mutTasClone_clone ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (loc) (PtrSynType)) (mutTasClone_spec_attrs (T_rt)) 
             <TY> alias_ptr_t : (spec_with 2 [] fn_spec);
      |}
  .
  Definition mutTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (mutTasClone_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Clone_base_spec loc PtrSynType (mutTasClone_spec_attrs (T_rt))<TY> alias_ptr_t <INST!>))).
End mutTasClone_spec.

Section mutTasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition mutTasCopy_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Copy_spec (loc))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (loc)).
  Definition mutTasCopy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (mutTasCopy_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Copy_base_spec loc PtrSynType (mutTasClone_spec_attrs ((T_rt))) (mutTasCopy_spec_attrs (T_rt))<TY> alias_ptr_t <INST!>))).
  Lemma mutTasCopy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp loc alias_ptr_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End mutTasCopy_spec.

Section boolasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition boolasClone_spec  : (spec_with _ _ (Clone_spec (bool))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_boolasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (bool) (BoolSynType)) boolasClone_spec_attrs 
             <TY> bool_t : (spec_with 2 [] fn_spec);
      |}
  .
  Definition boolasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), boolasClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec bool BoolSynType boolasClone_spec_attrs<TY> bool_t <INST!>))).
End boolasClone_spec.

Section boolasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition boolasCopy_spec  : (spec_with _ _ (Copy_spec (bool))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (bool)).
  Definition boolasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), boolasCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec bool BoolSynType boolasClone_spec_attrs boolasCopy_spec_attrs<TY> bool_t <INST!>))).
  Lemma boolasCopy_semantic_interp  : (Copy_semantic_interp bool bool_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End boolasCopy_spec.

Section charasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition charasClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_charasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) (CharSynType)) charasClone_spec_attrs 
             <TY> char_t : (spec_with 2 [] fn_spec);
      |}
  .
  Definition charasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), charasClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z CharSynType charasClone_spec_attrs<TY> char_t <INST!>))).
End charasClone_spec.

Section charasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition charasCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition charasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), charasCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z CharSynType charasClone_spec_attrs charasCopy_spec_attrs<TY> char_t <INST!>))).
  Lemma charasCopy_semantic_interp  : (Copy_semantic_interp Z char_t).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End charasCopy_spec.

Section i128asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i128asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I128))) i128asClone_spec_attrs 
             <TY> (int I128) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i128asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType I128) i128asClone_spec_attrs<TY> (int I128) <INST!>))).
End i128asClone_spec.

Section i128asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i128asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition i128asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i128asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType I128) i128asClone_spec_attrs i128asCopy_spec_attrs<TY> (int I128) <INST!>))).
  Lemma i128asCopy_semantic_interp  : (Copy_semantic_interp Z (int I128)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i128asCopy_spec.

Section i16asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i16asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I16))) i16asClone_spec_attrs 
             <TY> (int I16) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i16asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType I16) i16asClone_spec_attrs<TY> (int I16) <INST!>))).
End i16asClone_spec.

Section i16asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i16asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition i16asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i16asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType I16) i16asClone_spec_attrs i16asCopy_spec_attrs<TY> (int I16) <INST!>))).
  Lemma i16asCopy_semantic_interp  : (Copy_semantic_interp Z (int I16)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i16asCopy_spec.

Section i32asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i32asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I32))) i32asClone_spec_attrs 
             <TY> (int I32) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i32asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType I32) i32asClone_spec_attrs<TY> (int I32) <INST!>))).
End i32asClone_spec.

Section i32asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i32asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition i32asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i32asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType I32) i32asClone_spec_attrs i32asCopy_spec_attrs<TY> (int I32) <INST!>))).
  Lemma i32asCopy_semantic_interp  : (Copy_semantic_interp Z (int I32)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i32asCopy_spec.

Section i64asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i64asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I64))) i64asClone_spec_attrs 
             <TY> (int I64) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i64asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType I64) i64asClone_spec_attrs<TY> (int I64) <INST!>))).
End i64asClone_spec.

Section i64asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i64asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition i64asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i64asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType I64) i64asClone_spec_attrs i64asCopy_spec_attrs<TY> (int I64) <INST!>))).
  Lemma i64asCopy_semantic_interp  : (Copy_semantic_interp Z (int I64)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i64asCopy_spec.

Section i8asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_i8asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType I8))) i8asClone_spec_attrs 
             <TY> (int I8) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition i8asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType I8) i8asClone_spec_attrs<TY> (int I8) <INST!>))).
End i8asClone_spec.

Section i8asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition i8asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition i8asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), i8asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType I8) i8asClone_spec_attrs i8asCopy_spec_attrs<TY> (int I8) <INST!>))).
  Lemma i8asCopy_semantic_interp  : (Copy_semantic_interp Z (int I8)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End i8asCopy_spec.

Section isizeasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_isizeasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType ISize))) isizeasClone_spec_attrs 
             <TY> (int ISize) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition isizeasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType ISize) isizeasClone_spec_attrs<TY> (int ISize) <INST!>))).
End isizeasClone_spec.

Section isizeasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition isizeasCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition isizeasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), isizeasCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType ISize) isizeasClone_spec_attrs isizeasCopy_spec_attrs<TY> (int ISize) <INST!>))).
  Lemma isizeasCopy_semantic_interp  : (Copy_semantic_interp Z (int ISize)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End isizeasCopy_spec.

Section u128asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u128asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U128))) u128asClone_spec_attrs 
             <TY> (int U128) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u128asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType U128) u128asClone_spec_attrs<TY> (int U128) <INST!>))).
End u128asClone_spec.

Section u128asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u128asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition u128asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u128asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType U128) u128asClone_spec_attrs u128asCopy_spec_attrs<TY> (int U128) <INST!>))).
  Lemma u128asCopy_semantic_interp  : (Copy_semantic_interp Z (int U128)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u128asCopy_spec.

Section u16asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u16asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U16))) u16asClone_spec_attrs 
             <TY> (int U16) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u16asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType U16) u16asClone_spec_attrs<TY> (int U16) <INST!>))).
End u16asClone_spec.

Section u16asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u16asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition u16asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u16asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType U16) u16asClone_spec_attrs u16asCopy_spec_attrs<TY> (int U16) <INST!>))).
  Lemma u16asCopy_semantic_interp  : (Copy_semantic_interp Z (int U16)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u16asCopy_spec.

Section u32asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u32asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U32))) u32asClone_spec_attrs 
             <TY> (int U32) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u32asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType U32) u32asClone_spec_attrs<TY> (int U32) <INST!>))).
End u32asClone_spec.

Section u32asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u32asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition u32asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u32asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType U32) u32asClone_spec_attrs u32asCopy_spec_attrs<TY> (int U32) <INST!>))).
  Lemma u32asCopy_semantic_interp  : (Copy_semantic_interp Z (int U32)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u32asCopy_spec.

Section u64asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u64asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U64))) u64asClone_spec_attrs 
             <TY> (int U64) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u64asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType U64) u64asClone_spec_attrs<TY> (int U64) <INST!>))).
End u64asClone_spec.

Section u64asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u64asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition u64asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u64asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType U64) u64asClone_spec_attrs u64asCopy_spec_attrs<TY> (int U64) <INST!>))).
  Lemma u64asCopy_semantic_interp  : (Copy_semantic_interp Z (int U64)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u64asCopy_spec.

Section u8asClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_u8asClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType U8))) u8asClone_spec_attrs 
             <TY> (int U8) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition u8asClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType U8) u8asClone_spec_attrs<TY> (int U8) <INST!>))).
End u8asClone_spec.

Section u8asCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition u8asCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition u8asCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), u8asCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType U8) u8asClone_spec_attrs u8asCopy_spec_attrs<TY> (int U8) <INST!>))).
  Lemma u8asCopy_semantic_interp  : (Copy_semantic_interp Z (int U8)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End u8asCopy_spec.

Section usizeasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasClone_spec  : (spec_with _ _ (Clone_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_usizeasClone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (Z) ((IntSynType USize))) usizeasClone_spec_attrs 
             <TY> (int USize) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition usizeasClone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasClone_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Clone_base_spec Z (IntSynType USize) usizeasClone_spec_attrs<TY> (int USize) <INST!>))).
End usizeasClone_spec.

Section usizeasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition usizeasCopy_spec  : (spec_with _ _ (Copy_spec (Z))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ (Z)).
  Definition usizeasCopy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), usizeasCopy_spec <INST!>) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (Copy_base_spec Z (IntSynType USize) usizeasClone_spec_attrs usizeasCopy_spec_attrs<TY> (int USize) <INST!>))).
  Lemma usizeasCopy_semantic_interp  : (Copy_semantic_interp Z (int USize)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End usizeasCopy_spec.

Section std_marker_PhantomDataTasClone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_marker_PhantomDataTasClone_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Clone_spec ((((core_marker_PhantomData_rt) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_std_marker_PhantomDataTasClone_clone ((T_rt)) (T_st)) 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec ((((core_marker_PhantomData_rt) ((T_rt))))) (((core_marker_PhantomData_sls (T_st)) : syn_type))) (std_marker_PhantomDataTasClone_spec_attrs (T_rt)) 
             <TY> (core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition std_marker_PhantomDataTasClone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_marker_PhantomDataTasClone_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Clone_base_spec (((core_marker_PhantomData_rt) ((T_rt)))) ((core_marker_PhantomData_sls (T_st)) : syn_type) (std_marker_PhantomDataTasClone_spec_attrs (T_rt))<TY> (core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>) <INST!>))).
End std_marker_PhantomDataTasClone_spec.

Section std_marker_PhantomDataTasCopy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition std_marker_PhantomDataTasCopy_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (Copy_spec ((((core_marker_PhantomData_rt) ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ ((((core_marker_PhantomData_rt) ((T_rt)))))).
  Definition std_marker_PhantomDataTasCopy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (std_marker_PhantomDataTasCopy_spec (T_rt) (T_st)) <TY> T_ty <INST!>) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (Copy_base_spec (((core_marker_PhantomData_rt) ((T_rt)))) ((core_marker_PhantomData_sls (T_st)) : syn_type) (std_marker_PhantomDataTasClone_spec_attrs ((T_rt))) (std_marker_PhantomDataTasCopy_spec_attrs (T_rt))<TY> (core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>) <INST!>))).
  Lemma std_marker_PhantomDataTasCopy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp (((core_marker_PhantomData_rt) ((T_rt)))) (core_marker_PhantomData_ty ((T_rt))  <TY> T_ty <INST!>)).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End std_marker_PhantomDataTasCopy_spec.

