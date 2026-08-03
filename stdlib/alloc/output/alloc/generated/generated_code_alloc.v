From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
Section Global_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Global_sls  : struct_layout_spec :=
    let Global_st  := UnitSynType in
    mk_sls "Global" [] StructReprRust.
  Definition Global_st  : syn_type := Global_sls .
End Global_sls.

Section layout_LayoutError_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition layout_LayoutError_sls  : struct_layout_spec :=
    let layout_LayoutError_st  := UnitSynType in
    mk_sls "layout_LayoutError" [] StructReprRust.
  Definition layout_LayoutError_st  : syn_type := layout_LayoutError_sls .
End layout_LayoutError_sls.

Section layout_Layout_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition layout_Layout_sls  : struct_layout_spec :=
    let layout_Layout_st  := UnitSynType in
    mk_sls "layout_Layout" [
    ("size", (IntSynType USize));
    ("align", (alignment_Alignment_sls : syn_type))] StructReprRust.
  Definition layout_Layout_st  : syn_type := layout_Layout_sls .
End layout_Layout_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition layout_Layout_align_def (alignment_Alignment_as_usize_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (alignment_Alignment_sls : syn_type) } "__2";
      "__2" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "align");
      CallS alignment_Alignment_as_usize_loc [] [] [@{expr} move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__2")] (Some (Na1Ord, IntOp USize, "__0"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_from_size_align_def (layout_Layout_from_size_align_unchecked_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("align", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type) } "__0";
      local_live{ layout_Layout_st } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("size");
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ IntOp USize } copy{ IntOp USize } ("align");
      CallS layout_Layout_from_size_align_unchecked_loc [] [] [@{expr} move{ IntOp USize } ("__4"); move{ IntOp USize } ("__5")] (Some (Na1Ord, (use_op_alg' layout_Layout_st), "__3"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } EnumInit (Result_els (layout_Layout_st) (layout_LayoutError_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] []); RSTLitType ["layout_LayoutError_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (layout_Layout_st) (layout_LayoutError_st)) [("0", move{ (use_op_alg' layout_Layout_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_from_size_align_unchecked_def (alignment_Alignment_new_unchecked_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("align", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__4";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ IntOp USize } copy{ IntOp USize } ("align");
      CallS alignment_Alignment_new_unchecked_loc [] [] [@{expr} move{ IntOp USize } ("__5")] (Some (Na1Ord, (use_op_alg' (alignment_Alignment_sls : syn_type)), "__4"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      "__0" <-{ (use_op_alg' layout_Layout_st) } StructInit layout_Layout_sls [("size", move{ IntOp USize } ("__3") : expr); ("align", move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__4") : expr)];
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_new_def (layout_Layout_from_size_align_unchecked_loc: loc) (mem_align_of_T_loc: loc) (mem_size_of_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      local_live{ (IntSynType USize) } "__1";
      CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, IntOp USize, "__1"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_live{ (IntSynType USize) } "__2";
      CallS mem_align_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, IntOp USize, "__2"))
      ( Goto "_bb2")
      ( StuckS)
     ]>%E $
     <[
     "_bb2" :=
      CallS layout_Layout_from_size_align_unchecked_loc [] [] [@{expr} move{ IntOp USize } ("__1"); move{ IntOp USize } ("__2")] (Some (Na1Ord, (use_op_alg' layout_Layout_st), "__0"))
      ( Goto "_bb3")
      ( StuckS)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__2";
      local_dead "__1";
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_size_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ IntOp USize } copy{ IntOp USize } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "size");
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.