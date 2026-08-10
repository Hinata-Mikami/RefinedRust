From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
Section nonnull_NonNull_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition nonnull_NonNull_sls (T_st: syn_type) : struct_layout_spec :=
    let nonnull_NonNull_st (T_st: syn_type) := UnitSynType in
    mk_sls "nonnull_NonNull" [
    ("pointer", PtrSynType)] StructReprTransparent.
  Definition nonnull_NonNull_st (T_st: syn_type) : syn_type := nonnull_NonNull_sls T_st.
End nonnull_NonNull_sls.

Section unique_Unique_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition unique_Unique_sls (T_st: syn_type) : struct_layout_spec :=
    let unique_Unique_st (T_st: syn_type) := UnitSynType in
    mk_sls "unique_Unique" [
    ("pointer", (nonnull_NonNull_st (T_st)));
    ("_marker", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition unique_Unique_st (T_st: syn_type) : syn_type := unique_Unique_sls T_st.
End unique_Unique_sls.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition nonnull_NonNullTasstd_clone_Clone_clone_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (nonnull_NonNull_st (T_st)) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } (!{ RefOp } ( "self" ));
      return (move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_as_ptr_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      local_live{ PtrSynType } "__2";
      local_live{ PtrSynType } "__3";
      "__3" <-{ PtrOp } copy{ PtrOp } (("self") at{ (nonnull_NonNull_sls (T_st)) } "pointer");
      "__2" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__3"));
      "__0" <-{ PtrOp } copy{ PtrOp } ("__2");
      local_dead "__3";
      local_dead "__2";
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_cast_def (nonnull_NonNull_T_as_ptr_T_loc: loc) (T_st: syn_type) (U_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (nonnull_NonNull_st (U_st)) } "__0";
      local_live{ PtrSynType } "__2";
      local_live{ PtrSynType } "__3";
      local_live{ PtrSynType } "__4";
      local_live{ PtrSynType } "__5";
      local_live{ (nonnull_NonNull_st (T_st)) } "__6";
      "__6" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__6")] (Some (Na1Ord, PtrOp, "__5"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__6";
      "__4" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__5"));
      "__3" <-{ PtrOp } copy{ PtrOp } ("__4");
      "__2" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__3"));
      local_dead "__5";
      local_dead "__3";
      "__0" <-{ (use_op_alg' (nonnull_NonNull_st (U_st))) } StructInit (nonnull_NonNull_sls (U_st)) [("pointer", move{ PtrOp } ("__2") : expr)];
      local_dead "__4";
      local_dead "__2";
      return (move{ (use_op_alg' (nonnull_NonNull_st (U_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_is_aligned_def (mut_ptr_is_aligned_T_loc: loc) (nonnull_NonNull_T_as_ptr_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ PtrSynType } "__2";
      local_live{ (nonnull_NonNull_st (T_st)) } "__3";
      "__3" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__3")] (Some (Na1Ord, PtrOp, "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      CallS mut_ptr_is_aligned_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__2")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_is_aligned_to_def (mut_ptr_is_aligned_to_T_loc: loc) (nonnull_NonNull_T_as_ptr_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout);
     ("align", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ PtrSynType } "__3";
      local_live{ (nonnull_NonNull_st (T_st)) } "__4";
      "__4" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__4")] (Some (Na1Ord, PtrOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align");
      CallS mut_ptr_is_aligned_to_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__3"); move{ (IntOp USize) } ("__5")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_new_def (mut_ptr_is_null_T_loc: loc) (nonnull_NonNull_T_new_unchecked_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els ((nonnull_NonNull_st (T_st)))) : syn_type) } "__0";
      local_live{ BoolSynType } "__2";
      local_live{ PtrSynType } "__3";
      "__3" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS mut_ptr_is_null_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__3")] (Some (Na1Ord, BoolOp, "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__2") then
       Goto "_bb2"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      "__0" <-{ (use_op_alg' ((Option_els ((nonnull_NonNull_st (T_st)))) : syn_type)) } EnumInit (Option_els ((nonnull_NonNull_st (T_st)))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["nonnull_NonNull_inv_t"] (RSTScopeInst [] [RSTTyVar "T"] [])] [])) (StructInit (Option_None_sls ((nonnull_NonNull_st (T_st)))) []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__3";
      local_live{ (nonnull_NonNull_st (T_st)) } "__4";
      local_live{ PtrSynType } "__5";
      "__5" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS nonnull_NonNull_T_new_unchecked_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__5")] (Some (Na1Ord, (use_op_alg' (nonnull_NonNull_st (T_st))), "__4"))
      ( Goto "_bb4")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__5";
      "__0" <-{ (use_op_alg' ((Option_els ((nonnull_NonNull_st (T_st)))) : syn_type)) } EnumInit (Option_els ((nonnull_NonNull_st (T_st)))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["nonnull_NonNull_inv_t"] (RSTScopeInst [] [RSTTyVar "T"] [])] [])) (StructInit (Option_Some_sls ((nonnull_NonNull_st (T_st)))) [("0", move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__4") : expr)]);
      local_dead "__4";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__2";
      return (move{ (use_op_alg' ((Option_els ((nonnull_NonNull_st (T_st)))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_new_unchecked_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (nonnull_NonNull_st (T_st)) } "__0";
      local_live{ PtrSynType } "__2";
      local_live{ PtrSynType } "__3";
      local_live{ PtrSynType } "__4";
      local_live{ PtrSynType } "__5";
      "__5" <-{ PtrOp } copy{ PtrOp } ("ptr");
      "__4" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__5"));
      local_dead "__5";
      "__3" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__4"));
      "__2" <-{ PtrOp } copy{ PtrOp } ("__3");
      local_dead "__4";
      "__0" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } StructInit (nonnull_NonNull_sls (T_st)) [("pointer", move{ PtrOp } ("__2") : expr)];
      local_dead "__3";
      local_dead "__2";
      return (move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_read_def (nonnull_NonNull_T_as_ptr_T_loc: loc) (read_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ PtrSynType } "__2";
      local_live{ PtrSynType } "__3";
      local_live{ (nonnull_NonNull_st (T_st)) } "__4";
      "__4" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__4")] (Some (Na1Ord, PtrOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      "__2" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__3"));
      local_dead "__4";
      local_dead "__3";
      CallS read_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__2")] (Some (Na1Ord, (use_op_alg' T_st), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__2";
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_read_volatile_def (nonnull_NonNull_T_as_ptr_T_loc: loc) (read_volatile_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ PtrSynType } "__2";
      local_live{ PtrSynType } "__3";
      local_live{ (nonnull_NonNull_st (T_st)) } "__4";
      "__4" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__4")] (Some (Na1Ord, PtrOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      "__2" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__3"));
      local_dead "__4";
      local_dead "__3";
      CallS read_volatile_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__2")] (Some (Na1Ord, (use_op_alg' T_st), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__2";
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_write_def (DropGlue_T_drop_glue_loc: loc) (nonnull_NonNull_T_as_ptr_T_loc: loc) (write_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout);
     ("val", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ BoolSynType } "__6";
      "__6" <-{ BoolOp } val_of_bool false;
      "__6" <-{ BoolOp } val_of_bool true;
      local_live{ PtrSynType } "__3";
      local_live{ (nonnull_NonNull_st (T_st)) } "__4";
      "__4" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__4")] (Some (Na1Ord, PtrOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_live{ T_st } "__5";
      "__6" <-{ BoolOp } val_of_bool false;
      "__5" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("val");
      CallS write_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__3"); move{ (use_op_alg' T_st) } ("__5")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb5")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__3";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("val")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__6") then
       Goto "_bb4"
      else
       Goto "_bb3"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition nonnull_NonNull_T_write_volatile_def (DropGlue_T_drop_glue_loc: loc) (nonnull_NonNull_T_as_ptr_T_loc: loc) (write_volatile_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (nonnull_NonNull_st (T_st))) : layout);
     ("val", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ BoolSynType } "__6";
      "__6" <-{ BoolOp } val_of_bool false;
      "__6" <-{ BoolOp } val_of_bool true;
      local_live{ PtrSynType } "__3";
      local_live{ (nonnull_NonNull_st (T_st)) } "__4";
      "__4" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("self");
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__4")] (Some (Na1Ord, PtrOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_live{ T_st } "__5";
      "__6" <-{ BoolOp } val_of_bool false;
      "__5" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("val");
      CallS write_volatile_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__3"); move{ (use_op_alg' T_st) } ("__5")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb5")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__3";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("val")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__6") then
       Goto "_bb4"
      else
       Goto "_bb3"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unique_UniqueTasstd_clone_Clone_clone_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (unique_Unique_st (T_st)) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (use_op_alg' (unique_Unique_st (T_st))) } copy{ (use_op_alg' (unique_Unique_st (T_st))) } (!{ RefOp } ( "self" ));
      return (move{ (use_op_alg' (unique_Unique_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unique_Unique_T_as_ptr_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (unique_Unique_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (nonnull_NonNull_st (T_st)) } "__0";
      "__0" <-{ (use_op_alg' (nonnull_NonNull_st (T_st))) } copy{ (use_op_alg' (nonnull_NonNull_st (T_st))) } (("self") at{ (unique_Unique_sls (T_st)) } "pointer");
      return (move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unique_Unique_T_dangling_def (dangling_mut_T_loc: loc) (unique_Unique_T_new_unchecked_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (unique_Unique_st (T_st)) } "__0";
      local_live{ PtrSynType } "__1";
      CallS dangling_mut_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, PtrOp, "__1"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      CallS unique_Unique_T_new_unchecked_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__1")] (Some (Na1Ord, (use_op_alg' (unique_Unique_st (T_st))), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__1";
      return (move{ (use_op_alg' (unique_Unique_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unique_Unique_T_new_unchecked_def (nonnull_NonNull_T_new_unchecked_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (unique_Unique_st (T_st)) } "__0";
      local_live{ (nonnull_NonNull_st (T_st)) } "__2";
      local_live{ PtrSynType } "__3";
      "__3" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS nonnull_NonNull_T_new_unchecked_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__3")] (Some (Na1Ord, (use_op_alg' (nonnull_NonNull_st (T_st))), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__4";
      "__4" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (unique_Unique_st (T_st))) } StructInit (unique_Unique_sls (T_st)) [("pointer", move{ (use_op_alg' (nonnull_NonNull_st (T_st))) } ("__2") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__4") : expr)];
      local_dead "__4";
      local_dead "__2";
      return (move{ (use_op_alg' (unique_Unique_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.