From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
Section UnsafeCell_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition UnsafeCell_sls (T_st: syn_type) : struct_layout_spec :=
    let UnsafeCell_st (T_st: syn_type) := UnitSynType in
    mk_sls "UnsafeCell" [
    ("value", T_st)] StructReprTransparent.
  Definition UnsafeCell_st (T_st: syn_type) : syn_type := UnsafeCell_sls T_st.
End UnsafeCell_sls.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition drop_glue_UnsafeCell_def (DropGlue_T_drop_glue_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (UnsafeCell_sls (T_st)) } "value")] None
      ( Goto "_bb1")
      ( Unwind)
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