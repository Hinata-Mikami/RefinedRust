From radium Require Import lang notation.
From refinedrust Require Import typing shims.
Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition drop_def (DropGlue_T_drop_glue_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("x", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("x")] None
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.