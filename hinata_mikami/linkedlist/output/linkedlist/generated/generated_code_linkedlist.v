From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.alloc.vec.generated Require Export generated_specs_vec.
From rrstd.arithops.arithops.generated Require Export generated_specs_arithops.
From rrstd.boxed.boxed.generated Require Export generated_specs_boxed.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.stdlib.stdlib.generated Require Export generated_specs_stdlib.
Section Node_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Node_sls  : struct_layout_spec :=
    let Node_st  := UnitSynType in
    mk_sls "Node" [
    ("value", (IntSynType I32));
    ("next", PtrSynType);
    ("marked", BoolSynType)] StructReprRust.
  Definition Node_st  : syn_type := Node_sls .
End Node_sls.

Section Heap_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Heap_sls  : struct_layout_spec :=
    let Heap_st  := UnitSynType in
    mk_sls "Heap" [
    ("all_nodes", ((Vec_sls (PtrSynType) ((Global_sls : syn_type))) : syn_type))] StructReprRust.
  Definition Heap_st  : syn_type := Heap_sls .
End Heap_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition Heap_alloc_def (Box_T_into_raw_Node_loc: loc) (Box_T_new_Node_loc: loc) (Vec_TA_push_mutNode_std_alloc_Global_loc: loc) (ptr_null_mut_Node_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("value", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ ((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type) } "node";
      local_live{ Node_st } "__4";
      local_live{ (IntSynType I32) } "__5";
      "__5" <-{ IntOp I32 } copy{ IntOp I32 } ("value");
      local_live{ PtrSynType } "__6";
      "__6" <-{ PtrOp } CallE ptr_null_mut_Node_loc [] [] [@{expr} ];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__4" <-{ (use_op_alg' Node_st) } StructInit Node_sls [("value", move{ IntOp I32 } ("__5") : expr); ("next", move{ PtrOp } ("__6") : expr); ("marked", val_of_bool false : expr)];
      local_dead "__6";
      local_dead "__5";
      "node" <-{ (use_op_alg' ((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type)) } CallE Box_T_new_Node_loc [] [] [@{expr} move{ (use_op_alg' Node_st) } ("__4")];
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__4";
      local_live{ PtrSynType } "ptr";
      local_live{ ((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type) } "__8";
      "__8" <-{ (use_op_alg' ((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type)) } ("node");
      "ptr" <-{ PtrOp } CallE Box_T_into_raw_Node_loc [] [] [@{expr} move{ (use_op_alg' ((Box_sls (Node_st) ((Global_sls : syn_type))) : syn_type)) } ("__8")];
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_live{ UnitSynType } "__9";
      local_live{ PtrSynType } "__10";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__10" <-{ PtrOp } &ref{ Mut, Some (RSTLitType ["Vec_inv_t"] (RSTScopeInst [] [RSTAliasPtr; RSTLitType ["Global_ty"] (RSTScopeInst [] [] [])] [AppDef ["GlobalasAllocator_spec_attrs"] []])), "llft3" } ((!{ PtrOp } ( "self" )) at{ Heap_sls } "all_nodes");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ PtrSynType } "__11";
      "__11" <-{ PtrOp } copy{ PtrOp } ("ptr");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      "__9" <-{ StructOp unit_sl [] } CallE Vec_TA_push_mutNode_std_alloc_Global_loc ["vlft6"] [] [@{expr} move{ PtrOp } ("__10"); move{ PtrOp } ("__11")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__11";
      local_dead "__10";
      local_dead "__9";
      "__0" <-{ PtrOp } copy{ PtrOp } ("ptr");
      local_dead "ptr";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "node";
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Heap_new_def (Vec_T_new_mutNode_loc: loc) : function :=
  {|
     f_args := [
      
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Heap_st } "__0";
      local_live{ ((Vec_sls (PtrSynType) ((Global_sls : syn_type))) : syn_type) } "__1";
      "__1" <-{ (use_op_alg' ((Vec_sls (PtrSynType) ((Global_sls : syn_type))) : syn_type)) } CallE Vec_T_new_mutNode_loc [] [] [@{expr} ];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ (use_op_alg' Heap_st) } StructInit Heap_sls [("all_nodes", move{ (use_op_alg' ((Vec_sls (PtrSynType) ((Global_sls : syn_type))) : syn_type)) } ("__1") : expr)];
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__1";
      return (move{ (use_op_alg' Heap_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Node_set_next_def  : function :=
  {|
     f_args := [
      ("node", void* : layout);
     ("next", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ PtrSynType } "__3";
      "__3" <-{ PtrOp } copy{ PtrOp } ("next");
      (!{ PtrOp } ( "node" )) at{ Node_sls } "next" <-{ PtrOp } move{ PtrOp } ("__3");
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.