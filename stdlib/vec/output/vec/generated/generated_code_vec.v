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
From rrstd.sized.sized.generated Require Export generated_specs_sized.
Section Iter_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Iter_sls (T_st: syn_type) : struct_layout_spec :=
    let Iter_st (T_st: syn_type) := UnitSynType in
    mk_sls "Iter" [
    ("end_or_len", PtrSynType);
    ("_marker", ((core_marker_PhantomData_sls (RefSynType)) : syn_type))] StructReprRust.
  Definition Iter_st (T_st: syn_type) : syn_type := Iter_sls T_st.
End Iter_sls.

Section IterMut_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition IterMut_sls (T_st: syn_type) : struct_layout_spec :=
    let IterMut_st (T_st: syn_type) := UnitSynType in
    mk_sls "IterMut" [
    ("ptr", ((nonnull_NonNull_sls (T_st)) : syn_type));
    ("end_or_len", PtrSynType);
    ("_marker", ((core_marker_PhantomData_sls (RefSynType)) : syn_type))] StructReprRust.
  Definition IterMut_st (T_st: syn_type) : syn_type := IterMut_sls T_st.
End IterMut_sls.

Section IntoIter_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition IntoIter_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let IntoIter_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "IntoIter" [
    ("_x", ((core_marker_PhantomData_sls (T_st)) : syn_type));
    ("_y", A_st)] StructReprRust.
  Definition IntoIter_st (T_st: syn_type) (A_st: syn_type) : syn_type := IntoIter_sls T_st A_st.
End IntoIter_sls.

Section RawVecInner_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RawVecInner_sls (A_st: syn_type) : struct_layout_spec :=
    let RawVecInner_st (A_st: syn_type) := UnitSynType in
    mk_sls "RawVecInner" [
    ("ptr", ((unique_Unique_sls ((IntSynType U8))) : syn_type));
    ("cap", (IntSynType USize));
    ("alloc", A_st)] StructReprRust.
  Definition RawVecInner_st (A_st: syn_type) : syn_type := RawVecInner_sls A_st.
End RawVecInner_sls.

Section RawVec_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RawVec_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let RawVec_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "RawVec" [
    ("inner", (RawVecInner_st (A_st)));
    ("_marker", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition RawVec_st (T_st: syn_type) (A_st: syn_type) : syn_type := RawVec_sls T_st A_st.
End RawVec_sls.

Section Vec_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Vec_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let Vec_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "Vec" [
    ("buf", (RawVec_st (T_st) (A_st)));
    ("len", (IntSynType USize))] StructReprRust.
  Definition Vec_st (T_st: syn_type) (A_st: syn_type) : syn_type := Vec_sls T_st A_st.
End Vec_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition Vec_TA_is_empty_def (Vec_TA_len_T_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["Vec_inv_t"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS Vec_TA_len_T_A_loc ["vlft6"] [RSTTyVar "T"; RSTTyVar "A"] [@{expr} move{ RefOp } ("__3")] (Some (Na1Ord, (IntOp USize), "__2"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__2")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_IntoIter_def (DropGlue_A_drop_glue_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (IntoIter_sls (T_st) (A_st)) } "_y")] None
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_RawVecInner_def (DropGlue_A_drop_glue_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (RawVecInner_sls (A_st)) } "alloc")] None
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.