From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
Section RcInner_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RcInner_sls (T_st: syn_type) : struct_layout_spec :=
    let RcInner_st (T_st: syn_type) := UnitSynType in
    mk_sls "RcInner" [
    ("count", (IntSynType USize));
    ("data", T_st)] StructReprRust.
  Definition RcInner_st (T_st: syn_type) : syn_type := RcInner_sls T_st.
End RcInner_sls.

Section SimpleRC_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition SimpleRC_sls (T_st: syn_type) : struct_layout_spec :=
    let SimpleRC_st (T_st: syn_type) := UnitSynType in
    mk_sls "SimpleRC" [
    ("ptr", PtrSynType)] StructReprRust.
  Definition SimpleRC_st (T_st: syn_type) : syn_type := SimpleRC_sls T_st.
End SimpleRC_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Definition SimpleRC_T_new_def (box_into_raw_RcInnerT_loc: loc) (box_new_RcInnerT_loc: loc) (T_st: syn_type) : function := 
  {|
   f_args := [
    ("data", (use_layout_alg' T_st) : layout)
   ];
   f_local_vars := [
    ("__0", (use_layout_alg' (SimpleRC_st (T_st))) : layout);
   ("__2", (layout_of unit_sl) : layout);
   ("inner", (use_layout_alg' (RcInner_st (T_st))) : layout);
   ("__4", (use_layout_alg' T_st) : layout);
   ("boxed", void* : layout);
   ("__6", (use_layout_alg' (RcInner_st (T_st))) : layout);
   ("ptr", void* : layout);
   ("__8", void* : layout);
   ("__9", void* : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "__4" <-{ (use_op_alg' T_st) } use{ (use_op_alg' T_st) } ("data");
    "inner" <-{ (use_op_alg' (RcInner_st (T_st))) } StructInit (RcInner_sls (T_st)) [("count", i2v (1) USize : expr); ("data", use{ (use_op_alg' T_st) } ("__4") : expr)];
    Goto "_bb1"
   ]>%E $
   <[
   "_bb1" :=
    "__6" <-{ (use_op_alg' (RcInner_st (T_st))) } use{ (use_op_alg' (RcInner_st (T_st))) } ("inner");
    "boxed" <-{ PtrOp } CallE box_new_RcInnerT_loc [] [RSTTyVar "T"] [@{expr} use{ (use_op_alg' (RcInner_st (T_st))) } ("__6")];
    Goto "_bb2"
   ]>%E $
   <[
   "_bb2" :=
    "__8" <-{ PtrOp } use{ PtrOp } ("boxed");
    "ptr" <-{ PtrOp } CallE box_into_raw_RcInnerT_loc [] [RSTTyVar "T"] [@{expr} use{ PtrOp } ("__8")];
    Goto "_bb3"
   ]>%E $
   <[
   "_bb3" :=
    "__9" <-{ PtrOp } use{ PtrOp } ("ptr");
    "__0" <-{ (use_op_alg' (SimpleRC_st (T_st))) } StructInit (SimpleRC_sls (T_st)) [("ptr", use{ PtrOp } ("__9") : expr)];
    Goto "_bb4"
   ]>%E $
   <[
   "_bb4" :=
    Goto "_bb5"
   ]>%E $
   <[
   "_bb5" :=
    Goto "_bb6"
   ]>%E $
   <[
   "_bb6" :=
    return (use{ (use_op_alg' (SimpleRC_st (T_st))) } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

(* closure shims *)
End code.