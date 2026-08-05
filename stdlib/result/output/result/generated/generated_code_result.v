From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
Section Error_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Error_sls  : struct_layout_spec :=
    let Error_st  := UnitSynType in
    mk_sls "Error" [] StructReprRust.
  Definition Error_st  : syn_type := Error_sls .
End Error_sls.

Section Result_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Result_Ok_sls (T_st: syn_type) (E_st: syn_type) : struct_layout_spec :=
    let Result_Ok_st (T_st: syn_type) (E_st: syn_type) := UnitSynType in
    let Result_st (T_st: syn_type) (E_st: syn_type) := UnitSynType in
    mk_sls "Result_Ok" [
    ("0", T_st)] StructReprRust.
  Definition Result_Ok_st (T_st: syn_type) (E_st: syn_type) : syn_type := Result_Ok_sls T_st E_st.

  Definition Result_Err_sls (T_st: syn_type) (E_st: syn_type) : struct_layout_spec :=
    let Result_Err_st (T_st: syn_type) (E_st: syn_type) := UnitSynType in
    let Result_st (T_st: syn_type) (E_st: syn_type) := UnitSynType in
    mk_sls "Result_Err" [
    ("0", E_st)] StructReprRust.
  Definition Result_Err_st (T_st: syn_type) (E_st: syn_type) : syn_type := Result_Err_sls T_st E_st.

  Program Definition Result_els (T_st: syn_type) (E_st: syn_type) : enum_layout_spec := mk_els "Result" ISize [
    ("Ok", Result_Ok_st (T_st: syn_type) (E_st: syn_type));
    ("Err", Result_Err_st (T_st: syn_type) (E_st: syn_type))] EnumReprRust [("Ok", 0); ("Err", 1)] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque Result_els.
  Definition Result_st (T_st: syn_type) (E_st: syn_type) : syn_type := Result_els T_st E_st.
End Result_els.

Section Formatter_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Formatter_sls  : struct_layout_spec :=
    let Formatter_st  := UnitSynType in
    mk_sls "Formatter" [
    ("_marker", ((core_marker_PhantomData_sls (RefSynType)) : syn_type))] StructReprRust.
  Definition Formatter_st  : syn_type := Formatter_sls .
End Formatter_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition ResultTEasstd_clone_Clone_clone_def (Clone_E_clone_loc: loc) (Clone_T_clone_loc: loc) (T_st: syn_type) (E_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Result_st (T_st) (E_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      "__2" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (T_st) (E_st))) (!{ RefOp } ( "self" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ RefSynType } "__6";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft7"; (* composite *)
      "__6" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "E"), "vlft3" } ((EnumData ((Result_els (T_st) (E_st))) "Err" (!{ RefOp } ( "self" ))) at{ (Result_Err_sls (T_st) (E_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft10" "vlft3"; (* post-assignment *)
      local_live{ E_st } "__7";
      local_live{ RefSynType } "__8";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft10"; (* composite *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "E"), "vlft4" } (!{ RefOp } ( "__6" ));
      annot{ 1 }: CopyLftNameAnnot "plft11" "vlft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft11"; (* function_call *)
      CallS Clone_E_clone_loc ["vlft12"] [] [@{expr} move{ RefOp } ("__8")] (Some (Na1Ord, (use_op_alg' E_st), "__7"))
      ( Goto "_bb5")
      ( StuckS)
     ]>%E $
     <[
     "_bb3" :=
      local_live{ RefSynType } "__self_0";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* composite *)
      "__self_0" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft5" } ((EnumData ((Result_els (T_st) (E_st))) "Ok" (!{ RefOp } ( "self" ))) at{ (Result_Ok_sls (T_st) (E_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft5"; (* post-assignment *)
      local_live{ T_st } "__4";
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft8"; (* composite *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft6" } (!{ RefOp } ( "__self_0" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft9"; (* function_call *)
      CallS Clone_T_clone_loc ["vlft13"] [] [@{expr} move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' T_st), "__4"))
      ( Goto "_bb4")
      ( StuckS)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__5";
      "__0" <-{ (use_op_alg' (Result_st (T_st) (E_st))) } EnumInit (Result_els (T_st) (E_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "E"] [])) (StructInit (Result_Ok_sls (T_st) (E_st)) [("0", move{ (use_op_alg' T_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "__self_0";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__8";
      "__0" <-{ (use_op_alg' (Result_st (T_st) (E_st))) } EnumInit (Result_els (T_st) (E_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "E"] [])) (StructInit (Result_Err_sls (T_st) (E_st)) [("0", move{ (use_op_alg' E_st) } ("__7") : expr)]);
      local_dead "__7";
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      return (move{ (use_op_alg' (Result_st (T_st) (E_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Result_TE_map_def (DropGlue_F_drop_glue_loc: loc) (FnOnce_F_T_call_once_loc: loc) (T_st: syn_type) (E_st: syn_type) (U_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Result_st (T_st) (E_st))) : layout);
     ("op", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Result_st (U_st) (E_st)) } "__0";
      local_live{ (IntSynType ISize) } "__3";
      local_live{ BoolSynType } "__11";
      local_live{ BoolSynType } "__12";
      local_live{ BoolSynType } "__13";
      "__11" <-{ BoolOp } val_of_bool false;
      "__13" <-{ BoolOp } val_of_bool false;
      "__12" <-{ BoolOp } val_of_bool false;
      "__12" <-{ BoolOp } val_of_bool true;
      "__13" <-{ BoolOp } val_of_bool true;
      "__11" <-{ BoolOp } val_of_bool true;
      "__3" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (T_st) (E_st))) ("self");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__3")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ E_st } "e";
      "e" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ((EnumData ((Result_els (T_st) (E_st))) "Err" ("self")) at{ (Result_Err_sls (T_st) (E_st)) } "0");
      local_live{ E_st } "__10";
      "__10" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ("e");
      "__0" <-{ (use_op_alg' (Result_st (U_st) (E_st))) } EnumInit (Result_els (U_st) (E_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "U"; RSTTyVar "E"] [])) (StructInit (Result_Err_sls (U_st) (E_st)) [("0", move{ (use_op_alg' E_st) } ("__10") : expr)]);
      local_dead "__10";
      local_dead "e";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "t";
      "t" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Result_els (T_st) (E_st))) "Ok" ("self")) at{ (Result_Ok_sls (T_st) (E_st)) } "0");
      local_live{ U_st } "__5";
      local_live{ F_st } "__6";
      "__11" <-{ BoolOp } val_of_bool false;
      "__6" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("op");
      local_live{ ((tuple1_sls (T_st)) : syn_type) } "__7";
      local_live{ T_st } "__8";
      "__8" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("t");
      "__7" <-{ (use_op_alg' ((tuple1_sls (T_st)) : syn_type)) } StructInit (tuple1_sls (T_st)) [("0", move{ (use_op_alg' T_st) } ("__8") : expr)];
      CallS FnOnce_F_T_call_once_loc [] [] [@{expr} move{ (use_op_alg' F_st) } ("__6"); move{ (use_op_alg' ((tuple1_sls (T_st)) : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' U_st), "__5"))
      ( Goto "_bb4")
      ( StuckS)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      "__0" <-{ (use_op_alg' (Result_st (U_st) (E_st))) } EnumInit (Result_els (U_st) (E_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "U"; RSTTyVar "E"] [])) (StructInit (Result_Ok_sls (U_st) (E_st)) [("0", move{ (use_op_alg' U_st) } ("__5") : expr)]);
      local_dead "__5";
      local_dead "t";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__11") then
       Goto "_bb8"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      return (move{ (use_op_alg' (Result_st (U_st) (E_st))) } ("__0"))
     ]>%E $
     <[
     "_bb8" :=
      CallS DropGlue_F_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("op")] None
      ( Goto "_bb6")
      ( StuckS)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Result_TE_map_err_def (DropGlue_O_drop_glue_loc: loc) (FnOnce_O_E_call_once_loc: loc) (T_st: syn_type) (E_st: syn_type) (F_st: syn_type) (O_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Result_st (T_st) (E_st))) : layout);
     ("op", (use_layout_alg' O_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Result_st (T_st) (F_st)) } "__0";
      local_live{ (IntSynType ISize) } "__3";
      local_live{ BoolSynType } "__11";
      local_live{ BoolSynType } "__12";
      local_live{ BoolSynType } "__13";
      "__11" <-{ BoolOp } val_of_bool false;
      "__13" <-{ BoolOp } val_of_bool false;
      "__12" <-{ BoolOp } val_of_bool false;
      "__12" <-{ BoolOp } val_of_bool true;
      "__13" <-{ BoolOp } val_of_bool true;
      "__11" <-{ BoolOp } val_of_bool true;
      "__3" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (T_st) (E_st))) ("self");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__3")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ E_st } "e";
      "e" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ((EnumData ((Result_els (T_st) (E_st))) "Err" ("self")) at{ (Result_Err_sls (T_st) (E_st)) } "0");
      local_live{ F_st } "__7";
      local_live{ O_st } "__8";
      "__11" <-{ BoolOp } val_of_bool false;
      "__8" <-{ (use_op_alg' O_st) } move{ (use_op_alg' O_st) } ("op");
      local_live{ ((tuple1_sls (E_st)) : syn_type) } "__9";
      local_live{ E_st } "__10";
      "__10" <-{ (use_op_alg' E_st) } move{ (use_op_alg' E_st) } ("e");
      "__9" <-{ (use_op_alg' ((tuple1_sls (E_st)) : syn_type)) } StructInit (tuple1_sls (E_st)) [("0", move{ (use_op_alg' E_st) } ("__10") : expr)];
      CallS FnOnce_O_E_call_once_loc [] [] [@{expr} move{ (use_op_alg' O_st) } ("__8"); move{ (use_op_alg' ((tuple1_sls (E_st)) : syn_type)) } ("__9")] (Some (Na1Ord, (use_op_alg' F_st), "__7"))
      ( Goto "_bb4")
      ( StuckS)
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "t";
      "t" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Result_els (T_st) (E_st))) "Ok" ("self")) at{ (Result_Ok_sls (T_st) (E_st)) } "0");
      local_live{ T_st } "__5";
      "__5" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("t");
      "__0" <-{ (use_op_alg' (Result_st (T_st) (F_st))) } EnumInit (Result_els (T_st) (F_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "F"] [])) (StructInit (Result_Ok_sls (T_st) (F_st)) [("0", move{ (use_op_alg' T_st) } ("__5") : expr)]);
      local_dead "__5";
      local_dead "t";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      "__0" <-{ (use_op_alg' (Result_st (T_st) (F_st))) } EnumInit (Result_els (T_st) (F_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "F"] [])) (StructInit (Result_Err_sls (T_st) (F_st)) [("0", move{ (use_op_alg' F_st) } ("__7") : expr)]);
      local_dead "__7";
      local_dead "e";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__11") then
       Goto "_bb8"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      return (move{ (use_op_alg' (Result_st (T_st) (F_st))) } ("__0"))
     ]>%E $
     <[
     "_bb8" :=
      CallS DropGlue_O_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("op")] None
      ( Goto "_bb6")
      ( StuckS)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_Result_def (DropGlue_E_drop_glue_loc: loc) (DropGlue_T_drop_glue_loc: loc) (T_st: syn_type) (E_st: syn_type) : function :=
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
      "__2" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (T_st) (E_st))) (!{ RefOp } ( "ptr" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__2")) (<[ 0%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb2" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((EnumData ((Result_els (T_st) (E_st))) "Ok" (!{ RefOp } ( "ptr" ))) at{ (Result_Ok_sls (T_st) (E_st)) } "0")] None
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb3" :=
      CallS DropGlue_E_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((EnumData ((Result_els (T_st) (E_st))) "Err" (!{ RefOp } ( "ptr" ))) at{ (Result_Err_sls (T_st) (E_st)) } "0")] None
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.