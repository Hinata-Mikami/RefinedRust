From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.result.result.generated Require Export generated_specs_result.
Section Option_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Option_None_sls (T_st: syn_type) : struct_layout_spec :=
    let Option_None_st (T_st: syn_type) := UnitSynType in
    let Option_st (T_st: syn_type) := UnitSynType in
    mk_sls "Option_None" [] StructReprRust.
  Definition Option_None_st (T_st: syn_type) : syn_type := Option_None_sls T_st.

  Definition Option_Some_sls (T_st: syn_type) : struct_layout_spec :=
    let Option_Some_st (T_st: syn_type) := UnitSynType in
    let Option_st (T_st: syn_type) := UnitSynType in
    mk_sls "Option_Some" [
    ("0", T_st)] StructReprRust.
  Definition Option_Some_st (T_st: syn_type) : syn_type := Option_Some_sls T_st.

  Program Definition Option_els (T_st: syn_type) : enum_layout_spec := mk_els "Option" ISize [
    ("None", Option_None_st (T_st: syn_type));
    ("Some", Option_Some_st (T_st: syn_type))] EnumReprRust [("None", 0); ("Some", 1)] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque Option_els.
  Definition Option_st (T_st: syn_type) : syn_type := Option_els T_st.
End Option_els.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition OptionTasstd_clone_Clone_clone_def (Clone_T_clone_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Option_st (T_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) (!{ PtrOp } ( "self" ));
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ PtrSynType } "__self_0";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft5"; (* composite *)
      "__self_0" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft3" } ((EnumData ((Option_els (T_st))) "Some" (!{ PtrOp } ( "self" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft6" "vlft3"; (* post-assignment *)
      local_live{ T_st } "__4";
      local_live{ PtrSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* composite *)
      "__5" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft4" } (!{ PtrOp } ( "__self_0" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "vlft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft7"; (* function_call *)
      "__4" <-{ (use_op_alg' T_st) } CallE Clone_T_clone_loc ["vlft8"] [] [@{expr} move{ PtrOp } ("__5")];
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      "__0" <-{ (use_op_alg' (Option_st (T_st))) } EnumInit (Option_els (T_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_None_sls (T_st)) []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__5";
      "__0" <-{ (use_op_alg' (Option_st (T_st))) } EnumInit (Option_els (T_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_Some_sls (T_st)) [("0", move{ (use_op_alg' T_st) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "__self_0";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      return (move{ (use_op_alg' (Option_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Option_OptionT_flatten_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Option_st ((Option_st (T_st))))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Option_st (T_st)) } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ BoolSynType } "__4";
      local_live{ (IntSynType ISize) } "__5";
      "__4" <-{ BoolOp } val_of_bool false;
      "__4" <-{ BoolOp } val_of_bool true;
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Option_els ((Option_st (T_st))))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (use_op_alg' (Option_st (T_st))) } EnumInit (Option_els (T_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_None_sls (T_st)) []);
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ (Option_st (T_st)) } "inner";
      "inner" <-{ (use_op_alg' (Option_st (T_st))) } move{ (use_op_alg' (Option_st (T_st))) } ((EnumData ((Option_els ((Option_st (T_st))))) "Some" ("self")) at{ (Option_Some_sls ((Option_st (T_st)))) } "0");
      "__0" <-{ (use_op_alg' (Option_st (T_st))) } move{ (use_op_alg' (Option_st (T_st))) } ("inner");
      local_dead "inner";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      "__5" <-{ IntOp ISize } EnumDiscriminant ((Option_els ((Option_st (T_st))))) ("self");
      return (move{ (use_op_alg' (Option_st (T_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Option_T_filter_def (DropGlue_P_drop_glue_loc: loc) (DropGlue_T_drop_glue_loc: loc) (FnOnce_P_REFT_call_once_loc: loc) (T_st: syn_type) (P_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Option_st (T_st))) : layout);
     ("predicate", (use_layout_alg' P_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Option_st (T_st)) } "__0";
      local_live{ (IntSynType ISize) } "__4";
      local_live{ UnitSynType } "__11";
      local_live{ BoolSynType } "__13";
      local_live{ BoolSynType } "__14";
      local_live{ (IntSynType ISize) } "__15";
      local_live{ (IntSynType ISize) } "__17";
      local_live{ (IntSynType ISize) } "__19";
      "__13" <-{ BoolOp } val_of_bool false;
      "__14" <-{ BoolOp } val_of_bool false;
      "__14" <-{ BoolOp } val_of_bool true;
      "__13" <-{ BoolOp } val_of_bool true;
      local_live{ UnitSynType } "__3";
      "__4" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__4")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb1"]) (Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      local_live{ T_st } "x";
      "x" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Option_els (T_st))) "Some" ("self")) at{ (Option_Some_sls (T_st)) } "0");
      local_live{ BoolSynType } "__6";
      local_live{ P_st } "__7";
      "__13" <-{ BoolOp } val_of_bool false;
      "__7" <-{ (use_op_alg' P_st) } move{ (use_op_alg' P_st) } ("predicate");
      local_live{ ((tuple1_sls (PtrSynType)) : syn_type) } "__8";
      local_live{ PtrSynType } "__9";
      local_live{ PtrSynType } "__10";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__10" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "T"), "llft2" } ("x");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft7"; (* composite *)
      "__9" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft3" } (!{ PtrOp } ( "__10" ));
      annot{ 1 }: CopyLftNameAnnot "plft6" "vlft3"; (* post-assignment *)
      "__8" <-{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } StructInit (tuple1_sls (PtrSynType)) [("0", move{ PtrOp } ("__9") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft5" "plft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft5"; (* function_call *)
      "__6" <-{ BoolOp } CallE FnOnce_P_REFT_call_once_loc ["vlft4"] [] [@{expr} move{ (use_op_alg' P_st) } ("__7"); move{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } ("__8")];
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_live{ T_st } "__12";
      "__12" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("x");
      "__0" <-{ (use_op_alg' (Option_st (T_st))) } EnumInit (Option_els (T_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_Some_sls (T_st)) [("0", move{ (use_op_alg' T_st) } ("__12") : expr)]);
      local_dead "__12";
      local_dead "__6";
      local_dead "x";
      local_dead "__3";
      "__17" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Goto "_bb9"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      "__3" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__6";
      expr: CallE DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ Mut } ("x")];
      Goto "_bb6"
     ]>%E $
     <[
     "_bb5" :=
      "__3" <-{ StructOp unit_sl [] } zst_val;
      Goto "_bb7"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "x";
      Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__3";
      "__0" <-{ (use_op_alg' (Option_st (T_st))) } EnumInit (Option_els (T_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "T"] [])) (StructInit (Option_None_sls (T_st)) []);
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb11"
      else
       Goto "_bb8"
     ]>%E $
     <[
     "_bb8" :=
      "__15" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      return (move{ (use_op_alg' (Option_st (T_st))) } ("__0"))
     ]>%E $
     <[
     "_bb11" :=
      expr: CallE DropGlue_P_drop_glue_loc [] [] [@{expr} &raw{ Mut } ("predicate")];
      Goto "_bb8"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Option_T_map_def (DropGlue_F_drop_glue_loc: loc) (FnOnce_F_T_call_once_loc: loc) (T_st: syn_type) (U_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Option_st (T_st))) : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Option_st (U_st)) } "__0";
      local_live{ (IntSynType ISize) } "__3";
      local_live{ BoolSynType } "__9";
      local_live{ BoolSynType } "__10";
      local_live{ (IntSynType ISize) } "__11";
      local_live{ (IntSynType ISize) } "__13";
      "__9" <-{ BoolOp } val_of_bool false;
      "__10" <-{ BoolOp } val_of_bool false;
      "__10" <-{ BoolOp } val_of_bool true;
      "__9" <-{ BoolOp } val_of_bool true;
      "__3" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__3")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (use_op_alg' (Option_st (U_st))) } EnumInit (Option_els (U_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "U"] [])) (StructInit (Option_None_sls (U_st)) []);
      Goto "_bb7"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "x";
      "x" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Option_els (T_st))) "Some" ("self")) at{ (Option_Some_sls (T_st)) } "0");
      local_live{ U_st } "__5";
      local_live{ F_st } "__6";
      "__9" <-{ BoolOp } val_of_bool false;
      "__6" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("f");
      local_live{ ((tuple1_sls (T_st)) : syn_type) } "__7";
      local_live{ T_st } "__8";
      "__8" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("x");
      "__7" <-{ (use_op_alg' ((tuple1_sls (T_st)) : syn_type)) } StructInit (tuple1_sls (T_st)) [("0", move{ (use_op_alg' T_st) } ("__8") : expr)];
      "__5" <-{ (use_op_alg' U_st) } CallE FnOnce_F_T_call_once_loc [] [] [@{expr} move{ (use_op_alg' F_st) } ("__6"); move{ (use_op_alg' ((tuple1_sls (T_st)) : syn_type)) } ("__7")];
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      "__0" <-{ (use_op_alg' (Option_st (U_st))) } EnumInit (Option_els (U_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "U"] [])) (StructInit (Option_Some_sls (U_st)) [("0", move{ (use_op_alg' U_st) } ("__5") : expr)]);
      local_dead "__5";
      local_dead "x";
      Goto "_bb7"
     ]>%E $
     <[
     "_bb5" :=
      "__11" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      return (move{ (use_op_alg' (Option_st (U_st))) } ("__0"))
     ]>%E $
     <[
     "_bb6" :=
      expr: CallE DropGlue_F_drop_glue_loc [] [] [@{expr} &raw{ Mut } ("f")];
      Goto "_bb5"
     ]>%E $
     <[
     "_bb7" :=
      if{ BoolOp }: copy{ BoolOp } ("__9") then
       Goto "_bb6"
      else
       Goto "_bb5"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Option_T_unwrap_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Option_st (T_st))) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ (IntSynType ISize) } "__2";
      local_live{ (IntSynType ISize) } "__5";
      local_live{ (IntSynType ISize) } "__7";
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ UnitSynType } "__4";
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "val";
      "val" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Option_els (T_st))) "Some" ("self")) at{ (Option_Some_sls (T_st)) } "0");
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("val");
      local_dead "val";
      "__5" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Option_T_unwrap_or_def (DropGlue_T_drop_glue_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' (Option_st (T_st))) : layout);
     ("def", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ (IntSynType ISize) } "__3";
      local_live{ BoolSynType } "__5";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ (IntSynType ISize) } "__9";
      "__5" <-{ BoolOp } val_of_bool false;
      "__6" <-{ BoolOp } val_of_bool false;
      "__6" <-{ BoolOp } val_of_bool true;
      "__5" <-{ BoolOp } val_of_bool true;
      "__3" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__3")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb2"; Goto "_bb3"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      "__5" <-{ BoolOp } val_of_bool false;
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("def");
      Goto "_bb7"
     ]>%E $
     <[
     "_bb3" :=
      local_live{ T_st } "x";
      "x" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ((EnumData ((Option_els (T_st))) "Some" ("self")) at{ (Option_Some_sls (T_st)) } "0");
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("x");
      local_dead "x";
      Goto "_bb7"
     ]>%E $
     <[
     "_bb4" :=
      "__7" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) ("self");
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
     <[
     "_bb6" :=
      expr: CallE DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ Mut } ("def")];
      Goto "_bb4"
     ]>%E $
     <[
     "_bb7" :=
      if{ BoolOp }: copy{ BoolOp } ("__5") then
       Goto "_bb6"
      else
       Goto "_bb4"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_Option_def (DropGlue_T_drop_glue_loc: loc) (T_st: syn_type) : function :=
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
      "__2" <-{ IntOp ISize } EnumDiscriminant ((Option_els (T_st))) (!{ PtrOp } ( "ptr" ));
      Switch (ISize: int_type) (move{ IntOp ISize } ("__2")) (<[ 0%Z := 0%nat ]> $ ∅) ([Goto "_bb1"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb2" :=
      expr: CallE DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ Mut } ((EnumData ((Option_els (T_st))) "Some" (!{ PtrOp } ( "ptr" ))) at{ (Option_Some_sls (T_st)) } "0")];
      Goto "_bb1"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.