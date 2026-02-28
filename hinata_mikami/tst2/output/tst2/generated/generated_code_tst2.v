From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
Section Data_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Data_sls  : struct_layout_spec :=
    let Data_st  := UnitSynType in
    mk_sls "Data" [
    ("value", (IntSynType I32))] StructReprRust.
  Definition Data_st  : syn_type := Data_sls .
End Data_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Definition id_data_def  : function := 
  {|
   f_args := [
    ("d", (use_layout_alg' Data_st) : layout)
   ];
   f_local_vars := [
    ("__0", (use_layout_alg' Data_st) : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "__0" <-{ (use_op_alg' Data_st) } use{ (use_op_alg' Data_st) } ("d");
    return (use{ (use_op_alg' Data_st) } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

Definition main_def (id_data_loc: loc) : function := 
  {|
   f_args := [
    
   ];
   f_local_vars := [
    ("__0", (layout_of unit_sl) : layout);
   ("d", (use_layout_alg' Data_st) : layout);
   ("__2", (use_layout_alg' Data_st) : layout);
   ("__3", (use_layout_alg' Data_st) : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "d" <-{ (use_op_alg' Data_st) } StructInit Data_sls [("value", i2v (10) I32 : expr)];
    "__3" <-{ (use_op_alg' Data_st) } use{ (use_op_alg' Data_st) } ("d");
    "__2" <-{ (use_op_alg' Data_st) } CallE id_data_loc [] [] [@{expr} use{ (use_op_alg' Data_st) } ("__3")];
    Goto "_bb1"
   ]>%E $
   <[
   "_bb1" :=
    "__0" <-{ StructOp unit_sl [] } zst_val;
    return (use{ StructOp unit_sl [] } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

(* closure shims *)
End code.