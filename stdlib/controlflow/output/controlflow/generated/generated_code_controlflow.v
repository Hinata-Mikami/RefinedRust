From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.result.result.generated Require Export generated_specs_result.
Section convert_Infallible_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Program Definition convert_Infallible_els  : enum_layout_spec := mk_els "convert_Infallible" ISize [] EnumReprRust [] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque convert_Infallible_els.
  Definition convert_Infallible_st  : syn_type := convert_Infallible_els .
End convert_Infallible_els.

Section ControlFlow_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition ControlFlow_Continue_sls (B_st: syn_type) (C_st: syn_type) : struct_layout_spec :=
    let ControlFlow_Continue_st (B_st: syn_type) (C_st: syn_type) := UnitSynType in
    let ControlFlow_st (B_st: syn_type) (C_st: syn_type) := UnitSynType in
    mk_sls "ControlFlow_Continue" [
    ("0", C_st)] StructReprRust.
  Definition ControlFlow_Continue_st (B_st: syn_type) (C_st: syn_type) : syn_type := ControlFlow_Continue_sls B_st C_st.

  Definition ControlFlow_Break_sls (B_st: syn_type) (C_st: syn_type) : struct_layout_spec :=
    let ControlFlow_Break_st (B_st: syn_type) (C_st: syn_type) := UnitSynType in
    let ControlFlow_st (B_st: syn_type) (C_st: syn_type) := UnitSynType in
    mk_sls "ControlFlow_Break" [
    ("0", B_st)] StructReprRust.
  Definition ControlFlow_Break_st (B_st: syn_type) (C_st: syn_type) : syn_type := ControlFlow_Break_sls B_st C_st.

  Program Definition ControlFlow_els (B_st: syn_type) (C_st: syn_type) : enum_layout_spec := mk_els "ControlFlow" ISize [
    ("Continue", ControlFlow_Continue_st (B_st: syn_type) (C_st: syn_type));
    ("Break", ControlFlow_Break_st (B_st: syn_type) (C_st: syn_type))] EnumReprRust [("Continue", 0); ("Break", 1)] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque ControlFlow_els.
  Definition ControlFlow_st (B_st: syn_type) (C_st: syn_type) : syn_type := ControlFlow_els B_st C_st.
End ControlFlow_els.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition ControlFlowBCasFromResidualControlFlowBconvert_Infallible_from_residual_def (B_st: syn_type) (C_st: syn_type) : function :=
  {|
     f_args := [
      ("residual", (use_layout_alg' (ControlFlow_st (B_st) (convert_Infallible_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (ControlFlow_st (B_st) (C_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ (IntSynType ISize) } "__9";
      "__2" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (convert_Infallible_st))) ("residual");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ convert_Infallible_st } "i";
      "i" <-{ (use_op_alg' convert_Infallible_st) } move{ (use_op_alg' convert_Infallible_st) } ((EnumData ((ControlFlow_els (B_st) (convert_Infallible_st))) "Continue" ("residual")) at{ (ControlFlow_Continue_sls (B_st) (convert_Infallible_st)) } "0");
      local_live{ UnitSynType } "__6";
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ B_st } "b";
      "b" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ((EnumData ((ControlFlow_els (B_st) (convert_Infallible_st))) "Break" ("residual")) at{ (ControlFlow_Break_sls (B_st) (convert_Infallible_st)) } "0");
      local_live{ B_st } "__4";
      "__4" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("b");
      "__0" <-{ (use_op_alg' (ControlFlow_st (B_st) (C_st))) } EnumInit (ControlFlow_els (B_st) (C_st)) "Break" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTTyVar "B"; RSTTyVar "C"] [])) (StructInit (ControlFlow_Break_sls (B_st) (C_st)) [("0", move{ (use_op_alg' B_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "b";
      "__7" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (convert_Infallible_st))) ("residual");
      return (move{ (use_op_alg' (ControlFlow_st (B_st) (C_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition ControlFlowBCasTry_branch_def (B_st: syn_type) (C_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (ControlFlow_st (B_st) (C_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (ControlFlow_st ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ BoolSynType } "__8";
      local_live{ BoolSynType } "__9";
      local_live{ (IntSynType ISize) } "__10";
      "__9" <-{ BoolOp } val_of_bool false;
      "__8" <-{ BoolOp } val_of_bool false;
      "__8" <-{ BoolOp } val_of_bool true;
      "__9" <-{ BoolOp } val_of_bool true;
      "__2" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (C_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ B_st } "b";
      "b" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ((EnumData ((ControlFlow_els (B_st) (C_st))) "Break" ("self")) at{ (ControlFlow_Break_sls (B_st) (C_st)) } "0");
      local_live{ (ControlFlow_st (B_st) (convert_Infallible_st)) } "__6";
      local_live{ B_st } "__7";
      "__7" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("b");
      "__6" <-{ (use_op_alg' (ControlFlow_st (B_st) (convert_Infallible_st))) } EnumInit (ControlFlow_els (B_st) (convert_Infallible_st)) "Break" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTTyVar "B"; RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (ControlFlow_Break_sls (B_st) (convert_Infallible_st)) [("0", move{ (use_op_alg' B_st) } ("__7") : expr)]);
      local_dead "__7";
      "__0" <-{ (use_op_alg' (ControlFlow_st ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st))) } EnumInit (ControlFlow_els ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st)) "Break" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTLitType ["ControlFlow_ty"] (RSTScopeInst [] [RSTTyVar "B"; RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] [])] []); RSTTyVar "C"] [])) (StructInit (ControlFlow_Break_sls ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st)) [("0", move{ (use_op_alg' (ControlFlow_st (B_st) (convert_Infallible_st))) } ("__6") : expr)]);
      local_dead "__6";
      local_dead "b";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ C_st } "c";
      "c" <-{ (use_op_alg' C_st) } move{ (use_op_alg' C_st) } ((EnumData ((ControlFlow_els (B_st) (C_st))) "Continue" ("self")) at{ (ControlFlow_Continue_sls (B_st) (C_st)) } "0");
      local_live{ C_st } "__4";
      "__4" <-{ (use_op_alg' C_st) } move{ (use_op_alg' C_st) } ("c");
      "__0" <-{ (use_op_alg' (ControlFlow_st ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st))) } EnumInit (ControlFlow_els ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st)) "Continue" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTLitType ["ControlFlow_ty"] (RSTScopeInst [] [RSTTyVar "B"; RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] [])] []); RSTTyVar "C"] [])) (StructInit (ControlFlow_Continue_sls ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st)) [("0", move{ (use_op_alg' C_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "c";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      "__10" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (C_st))) ("self");
      return (move{ (use_op_alg' (ControlFlow_st ((ControlFlow_st (B_st) (convert_Infallible_st))) (C_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition ControlFlowBCasTry_from_output_def (B_st: syn_type) (C_st: syn_type) : function :=
  {|
     f_args := [
      ("output", (use_layout_alg' C_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (ControlFlow_st (B_st) (C_st)) } "__0";
      local_live{ C_st } "__2";
      "__2" <-{ (use_op_alg' C_st) } move{ (use_op_alg' C_st) } ("output");
      "__0" <-{ (use_op_alg' (ControlFlow_st (B_st) (C_st))) } EnumInit (ControlFlow_els (B_st) (C_st)) "Continue" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTTyVar "B"; RSTTyVar "C"] [])) (StructInit (ControlFlow_Continue_sls (B_st) (C_st)) [("0", move{ (use_op_alg' C_st) } ("__2") : expr)]);
      local_dead "__2";
      return (move{ (use_op_alg' (ControlFlow_st (B_st) (C_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition ControlFlow_BC_break_value_def (drop_glue_ControlFlow_B_C_loc: loc) (B_st: syn_type) (C_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (ControlFlow_st (B_st) (C_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (B_st)) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ BoolSynType } "__5";
      local_live{ (IntSynType ISize) } "__6";
      "__5" <-{ BoolOp } val_of_bool false;
      "__5" <-{ BoolOp } val_of_bool true;
      "__2" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (C_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ B_st } "x";
      "x" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ((EnumData ((ControlFlow_els (B_st) (C_st))) "Break" ("self")) at{ (ControlFlow_Break_sls (B_st) (C_st)) } "0");
      local_live{ B_st } "__4";
      "__4" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("x");
      "__0" <-{ (use_op_alg' ((Option_els (B_st)) : syn_type)) } EnumInit (Option_els (B_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "B"] [])) (StructInit (Option_Some_sls (B_st)) [("0", move{ (use_op_alg' B_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "x";
      Goto "_bb7"
     ]>%E $
     <[
     "_bb3" :=
      "__0" <-{ (use_op_alg' ((Option_els (B_st)) : syn_type)) } EnumInit (Option_els (B_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "B"] [])) (StructInit (Option_None_sls (B_st)) []);
      Goto "_bb7"
     ]>%E $
     <[
     "_bb5" :=
      return (move{ (use_op_alg' ((Option_els (B_st)) : syn_type)) } ("__0"))
     ]>%E $
     <[
     "_bb6" :=
      expr: CallE drop_glue_ControlFlow_B_C_loc [] [RSTTyVar "B"; RSTTyVar "C"] [@{expr} &raw{ Mut } ("self")];
      Goto "_bb5"
     ]>%E $
     <[
     "_bb7" :=
      "__6" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (C_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__6")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb5"]) (Goto "_bb6")
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Tasconvert_FromT_from_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("t", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("t");
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Tasconvert_IntoU_into_def (convert_From_U_T_from_loc: loc) (T_st: syn_type) (U_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ U_st } "__0";
      local_live{ T_st } "__2";
      "__2" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("self");
      "__0" <-{ (use_op_alg' U_st) } CallE convert_From_U_T_from_loc [] [] [@{expr} move{ (use_op_alg' T_st) } ("__2")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ (use_op_alg' U_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_ControlFlow_def (DropGlue_B_drop_glue_loc: loc) (DropGlue_C_drop_glue_loc: loc) (B_st: syn_type) (C_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ (IntSynType ISize) } "__3";
      "__2" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (B_st) (C_st))) (!{ PtrOp } ( "ptr" ));
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb2" :=
      expr: CallE DropGlue_C_drop_glue_loc [] [] [@{expr} &raw{ Mut } ((EnumData ((ControlFlow_els (B_st) (C_st))) "Continue" (!{ PtrOp } ( "ptr" ))) at{ (ControlFlow_Continue_sls (B_st) (C_st)) } "0")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb3" :=
      expr: CallE DropGlue_B_drop_glue_loc [] [] [@{expr} &raw{ Mut } ((EnumData ((ControlFlow_els (B_st) (C_st))) "Break" (!{ PtrOp } ( "ptr" ))) at{ (ControlFlow_Break_sls (B_st) (C_st)) } "0")];
      Goto "_bb1"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_option_OptionTasFromResidual_from_residual_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("residual", (use_layout_alg' ((Option_els (convert_Infallible_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (T_st)) : syn_type) } "__0";
      "__0" <-{ (use_op_alg' ((Option_els (T_st)) : syn_type)) } EnumInit (Option_els (T_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_None_sls (T_st)) []);
      return (move{ (use_op_alg' ((Option_els (T_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_option_OptionTasTry_branch_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((Option_els (T_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (ControlFlow_st (((Option_els (convert_Infallible_st)) : syn_type)) (T_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType ISize) } "__7";
      "__6" <-{ BoolOp } val_of_bool false;
      "__6" <-{ BoolOp } val_of_bool true;
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ ((Option_els (convert_Infallible_st)) : syn_type) } "__5";
      "__5" <-{ (use_op_alg' ((Option_els (convert_Infallible_st)) : syn_type)) } EnumInit (Option_els (convert_Infallible_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_None_sls (convert_Infallible_st)) []);
      "__0" <-{ (use_op_alg' (ControlFlow_st (((Option_els (convert_Infallible_st)) : syn_type)) (T_st))) } EnumInit (ControlFlow_els (((Option_els (convert_Infallible_st)) : syn_type)) (T_st)) "Break" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTLitType ["Option_ty"] (RSTScopeInst [] [RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] [])] []); RSTTyVar "T"] [])) (StructInit (ControlFlow_Break_sls (((Option_els (convert_Infallible_st)) : syn_type)) (T_st)) [("0", move{ (use_op_alg' ((Option_els (convert_Infallible_st)) : syn_type)) } ("__5") : expr)]);
      local_dead "__5";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "v";
      "v" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Option_els (T_st))) "Some" ("self")) at{ (Option_Some_sls (T_st)) } "0");
      local_live{ T_st } "__4";
      "__4" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v");
      "__0" <-{ (use_op_alg' (ControlFlow_st (((Option_els (convert_Infallible_st)) : syn_type)) (T_st))) } EnumInit (ControlFlow_els (((Option_els (convert_Infallible_st)) : syn_type)) (T_st)) "Continue" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTLitType ["Option_ty"] (RSTScopeInst [] [RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] [])] []); RSTTyVar "T"] [])) (StructInit (ControlFlow_Continue_sls (((Option_els (convert_Infallible_st)) : syn_type)) (T_st)) [("0", move{ (use_op_alg' T_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "v";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      "__7" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      return (move{ (use_op_alg' (ControlFlow_st (((Option_els (convert_Infallible_st)) : syn_type)) (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_option_OptionTasTry_from_output_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("output", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (T_st)) : syn_type) } "__0";
      local_live{ T_st } "__2";
      "__2" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("output");
      "__0" <-{ (use_op_alg' ((Option_els (T_st)) : syn_type)) } EnumInit (Option_els (T_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_Some_sls (T_st)) [("0", move{ (use_op_alg' T_st) } ("__2") : expr)]);
      local_dead "__2";
      return (move{ (use_op_alg' ((Option_els (T_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_result_ResultTEasTry_branch_def (T_st: syn_type) (E_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((Result_els (T_st) (E_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (ControlFlow_st (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ BoolSynType } "__8";
      local_live{ BoolSynType } "__9";
      local_live{ (IntSynType ISize) } "__10";
      "__9" <-{ BoolOp } val_of_bool false;
      "__8" <-{ BoolOp } val_of_bool false;
      "__8" <-{ BoolOp } val_of_bool true;
      "__9" <-{ BoolOp } val_of_bool true;
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Result_els (T_st) (E_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ E_st } "e";
      "e" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ((EnumData ((Result_els (T_st) (E_st))) "Err" ("self")) at{ (Result_Err_sls (T_st) (E_st)) } "0");
      local_live{ ((Result_els (convert_Infallible_st) (E_st)) : syn_type) } "__6";
      local_live{ E_st } "__7";
      "__7" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ("e");
      "__6" <-{ (use_op_alg' ((Result_els (convert_Infallible_st) (E_st)) : syn_type)) } EnumInit (Result_els (convert_Infallible_st) (E_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] []); RSTTyVar "E"] [])) (StructInit (Result_Err_sls (convert_Infallible_st) (E_st)) [("0", move{ (use_op_alg' E_st) } ("__7") : expr)]);
      local_dead "__7";
      "__0" <-{ (use_op_alg' (ControlFlow_st (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st))) } EnumInit (ControlFlow_els (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st)) "Break" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTLitType ["Result_ty"] (RSTScopeInst [] [RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] []); RSTTyVar "E"] []); RSTTyVar "T"] [])) (StructInit (ControlFlow_Break_sls (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st)) [("0", move{ (use_op_alg' ((Result_els (convert_Infallible_st) (E_st)) : syn_type)) } ("__6") : expr)]);
      local_dead "__6";
      local_dead "e";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "v";
      "v" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Result_els (T_st) (E_st))) "Ok" ("self")) at{ (Result_Ok_sls (T_st) (E_st)) } "0");
      local_live{ T_st } "__4";
      "__4" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v");
      "__0" <-{ (use_op_alg' (ControlFlow_st (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st))) } EnumInit (ControlFlow_els (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st)) "Continue" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTLitType ["Result_ty"] (RSTScopeInst [] [RSTLitType ["convert_Infallible_ty"] (RSTScopeInst [] [] []); RSTTyVar "E"] []); RSTTyVar "T"] [])) (StructInit (ControlFlow_Continue_sls (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st)) [("0", move{ (use_op_alg' T_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "v";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      "__10" <-{ IntOp ISize } EnumDiscriminant ((Result_els (T_st) (E_st))) ("self");
      return (move{ (use_op_alg' (ControlFlow_st (((Result_els (convert_Infallible_st) (E_st)) : syn_type)) (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_result_ResultTEasTry_from_output_def (T_st: syn_type) (E_st: syn_type) : function :=
  {|
     f_args := [
      ("output", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (T_st) (E_st)) : syn_type) } "__0";
      local_live{ T_st } "__2";
      "__2" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("output");
      "__0" <-{ (use_op_alg' ((Result_els (T_st) (E_st)) : syn_type)) } EnumInit (Result_els (T_st) (E_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "E"] [])) (StructInit (Result_Ok_sls (T_st) (E_st)) [("0", move{ (use_op_alg' T_st) } ("__2") : expr)]);
      local_dead "__2";
      return (move{ (use_op_alg' ((Result_els (T_st) (E_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_result_ResultTFasFromResidualstd_result_Resultconvert_InfallibleE_from_residual_def (convert_From_F_E_from_loc: loc) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("residual", (use_layout_alg' ((Result_els (convert_Infallible_st) (E_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (T_st) (F_st)) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ BoolSynType } "__7";
      local_live{ (IntSynType ISize) } "__8";
      local_live{ (IntSynType ISize) } "__10";
      "__7" <-{ BoolOp } val_of_bool false;
      "__7" <-{ BoolOp } val_of_bool true;
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Result_els (convert_Infallible_st) (E_st))) ("residual");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ UnitSynType } "__6";
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ E_st } "e";
      "e" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ((EnumData ((Result_els (convert_Infallible_st) (E_st))) "Err" ("residual")) at{ (Result_Err_sls (convert_Infallible_st) (E_st)) } "0");
      local_live{ F_st } "__4";
      local_live{ E_st } "__5";
      "__5" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ("e");
      "__4" <-{ (use_op_alg' F_st) } CallE convert_From_F_E_from_loc [] [] [@{expr} move{ (use_op_alg' E_st) } ("__5")];
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__5";
      "__0" <-{ (use_op_alg' ((Result_els (T_st) (F_st)) : syn_type)) } EnumInit (Result_els (T_st) (F_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "F"] [])) (StructInit (Result_Err_sls (T_st) (F_st)) [("0", move{ (use_op_alg' F_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "e";
      "__8" <-{ IntOp ISize } EnumDiscriminant ((Result_els (convert_Infallible_st) (E_st))) ("residual");
      return (move{ (use_op_alg' ((Result_els (T_st) (F_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.