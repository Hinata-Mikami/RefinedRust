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
    ("next", PtrSynType)] StructReprRust.
  Definition Node_st  : syn_type := Node_sls .
End Node_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition Node_id_Node_def  : function :=
  {|
     f_args := [
      ("p", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      "__0" <-{ PtrOp } copy{ PtrOp } ("p");
      return (move{ PtrOp } ("__0"))
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




Program Definition id_def  : function :=
  {|
     f_args := [
      ("p", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      "__0" <-{ PtrOp } copy{ PtrOp } ("p");
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition id_Cell_def  : function :=
  {|
     f_args := [
      ("p", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      "__0" <-{ PtrOp } copy{ PtrOp } ("p");
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.