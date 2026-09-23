From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.option.option.generated Require Export generated_specs_option.
Section Ordering_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Ordering_Less_sls  : struct_layout_spec :=
    let Ordering_Less_st  := UnitSynType in
    let Ordering_st  := UnitSynType in
    mk_sls "Ordering_Less" [] StructReprRust.
  Definition Ordering_Less_st  : syn_type := Ordering_Less_sls .

  Definition Ordering_Equal_sls  : struct_layout_spec :=
    let Ordering_Equal_st  := UnitSynType in
    let Ordering_st  := UnitSynType in
    mk_sls "Ordering_Equal" [] StructReprRust.
  Definition Ordering_Equal_st  : syn_type := Ordering_Equal_sls .

  Definition Ordering_Greater_sls  : struct_layout_spec :=
    let Ordering_Greater_st  := UnitSynType in
    let Ordering_st  := UnitSynType in
    mk_sls "Ordering_Greater" [] StructReprRust.
  Definition Ordering_Greater_st  : syn_type := Ordering_Greater_sls .

  Program Definition Ordering_els  : enum_layout_spec := mk_els "Ordering" I8 [
    ("Less", Ordering_Less_st );
    ("Equal", Ordering_Equal_st );
    ("Greater", Ordering_Greater_st )] EnumReprRust [("Less", -1); ("Equal", 0); ("Greater", 1)] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque Ordering_els.
  Definition Ordering_st  : syn_type := Ordering_els .
End Ordering_els.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition Eq_assert_fields_are_eq_def (Self_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ord_clamp_def (DropGlue_Self_drop_glue_loc: loc) (panic_shim_loc: loc) (Self_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("min", (use_layout_alg' Self_st) : layout);
     ("max", (use_layout_alg' Self_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Self_st } "__0";
      local_live{ NeverSynType } "__4";
      local_live{ NeverSynType } "__5";
      CallS panic_shim_loc [] [] [@{expr} ] None
      ( StuckS)
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      CallS DropGlue_Self_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("max")] None
      ( Goto "_bb2")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb2" :=
      CallS DropGlue_Self_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("min")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb3" :=
      CallS DropGlue_Self_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("self")] None
      ( Goto "_bb4")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb4" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ord_max_def (max_by_Self_closuresrclibrs1498014986_loc: loc) (Self_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("other", (use_layout_alg' Self_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Self_st } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ Self_st } "__4";
      "__4" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("other");
      local_live{ UnitSynType } "__5";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      CallS max_by_Self_closuresrclibrs1498014986_loc [] [RSTTyVar "Self"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ (use_op_alg' Self_st) } ("__4"); move{ (StructOp unit_sl []) } ("__5")] (Some (Na1Ord, (use_op_alg' Self_st), "__0"))
      ( Goto "_bb1")
      ( Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' Self_st) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ord_min_def (min_by_Self_closuresrclibrs1578015786_loc: loc) (Self_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("other", (use_layout_alg' Self_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Self_st } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ Self_st } "__4";
      "__4" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("other");
      local_live{ UnitSynType } "__5";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      CallS min_by_Self_closuresrclibrs1578015786_loc [] [RSTTyVar "Self"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ (use_op_alg' Self_st) } ("__4"); move{ (StructOp unit_sl []) } ("__5")] (Some (Na1Ord, (use_op_alg' Self_st), "__0"))
      ( Goto "_bb1")
      ( Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' Self_st) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_as_raw_def  : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ RefSynType } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])), "llft2" } ("self");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft5"; (* borrow *)
      "__2" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])), "vlft3" } (!{ RefOp } ( "__3" ));
      annot{ 1 }: CopyLftNameAnnot "plft4" "vlft3"; (* post-assignment *)
      "__0" <-{ (IntOp I8) } EnumDiscriminant (Ordering_els) (!{ RefOp } ( "__2" ));
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      local_dead "__3";
      local_dead "__2";
      return (move{ (IntOp I8) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_is_eq_def (Ordering_as_raw_loc: loc) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } move{ (use_op_alg' Ordering_st) } ("self");
      CallS Ordering_as_raw_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__3")] (Some (Na1Ord, (IntOp I8), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__2")) = { (IntOp I8) , (IntOp I8) , U8 } (i2v (0) I8);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_is_ge_def (Ordering_as_raw_loc: loc) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } move{ (use_op_alg' Ordering_st) } ("self");
      CallS Ordering_as_raw_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__3")] (Some (Na1Ord, (IntOp I8), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__2")) ≥{ (IntOp I8) , (IntOp I8) , U8 } (i2v (0) I8);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_is_gt_def (Ordering_as_raw_loc: loc) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } move{ (use_op_alg' Ordering_st) } ("self");
      CallS Ordering_as_raw_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__3")] (Some (Na1Ord, (IntOp I8), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__2")) >{ (IntOp I8) , (IntOp I8) , U8 } (i2v (0) I8);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_is_le_def (Ordering_as_raw_loc: loc) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } move{ (use_op_alg' Ordering_st) } ("self");
      CallS Ordering_as_raw_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__3")] (Some (Na1Ord, (IntOp I8), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__2")) ≤{ (IntOp I8) , (IntOp I8) , U8 } (i2v (0) I8);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_is_lt_def (Ordering_as_raw_loc: loc) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } move{ (use_op_alg' Ordering_st) } ("self");
      CallS Ordering_as_raw_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__3")] (Some (Na1Ord, (IntOp I8), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__2")) <{ (IntOp I8) , (IntOp I8) , U8 } (i2v (0) I8);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Ordering_is_ne_def (Ordering_as_raw_loc: loc) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Ordering_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } move{ (use_op_alg' Ordering_st) } ("self");
      CallS Ordering_as_raw_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__3")] (Some (Na1Ord, (IntOp I8), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__2")) != { (IntOp I8) , (IntOp I8) , U8 } (i2v (0) I8);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition PartialEq_ne_def (PartialEq_Self_Rhs_eq_loc: loc) (Self_st: syn_type) (Rhs_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Self"), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Rhs"), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS PartialEq_Self_Rhs_eq_loc ["vlft10"; "vlft11"] [RSTTyVar "Self"; RSTTyVar "Rhs"] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, BoolOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (move{ BoolOp } ("__3"));
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition PartialOrd_ge_def (PartialOrd_Self_Rhs_partial_cmp_loc: loc) (Self_st: syn_type) (Rhs_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Self"), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Rhs"), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS PartialOrd_Self_Rhs_partial_cmp_loc ["vlft10"; "vlft11"] [RSTTyVar "Self"; RSTTyVar "Rhs"] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' ((Option_els (Ordering_st)) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (Ordering_st))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      "__6" <-{ (IntOp I8) } EnumDiscriminant (Ordering_els) ((EnumData ((Option_els (Ordering_st))) "Some" ("__3")) at{ (Option_Some_sls (Ordering_st)) } "0");
      Switch (I8: int_type) (move{ (IntOp I8) } ("__6")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb4"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ BoolOp } val_of_bool true;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition PartialOrd_gt_def (PartialOrd_Self_Rhs_partial_cmp_loc: loc) (Self_st: syn_type) (Rhs_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Self"), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Rhs"), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS PartialOrd_Self_Rhs_partial_cmp_loc ["vlft10"; "vlft11"] [RSTTyVar "Self"; RSTTyVar "Rhs"] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' ((Option_els (Ordering_st)) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (Ordering_st))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      "__6" <-{ (IntOp I8) } EnumDiscriminant (Ordering_els) ((EnumData ((Option_els (Ordering_st))) "Some" ("__3")) at{ (Option_Some_sls (Ordering_st)) } "0");
      Switch (I8: int_type) (move{ (IntOp I8) } ("__6")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb4"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ BoolOp } val_of_bool true;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition PartialOrd_le_def (PartialOrd_Self_Rhs_partial_cmp_loc: loc) (Self_st: syn_type) (Rhs_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Self"), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Rhs"), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS PartialOrd_Self_Rhs_partial_cmp_loc ["vlft10"; "vlft11"] [RSTTyVar "Self"; RSTTyVar "Rhs"] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' ((Option_els (Ordering_st)) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (Ordering_st))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      "__6" <-{ (IntOp I8) } EnumDiscriminant (Ordering_els) ((EnumData ((Option_els (Ordering_st))) "Some" ("__3")) at{ (Option_Some_sls (Ordering_st)) } "0");
      Switch (I8: int_type) (move{ (IntOp I8) } ("__6")) (<[ 0%Z := 1%nat ]> $ <[ 255%Z := 0%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb4"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ BoolOp } val_of_bool true;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition PartialOrd_lt_def (PartialOrd_Self_Rhs_partial_cmp_loc: loc) (Self_st: syn_type) (Rhs_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Self"), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Rhs"), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS PartialOrd_Self_Rhs_partial_cmp_loc ["vlft10"; "vlft11"] [RSTTyVar "Self"; RSTTyVar "Rhs"] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' ((Option_els (Ordering_st)) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (Ordering_st))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      "__6" <-{ (IntOp I8) } EnumDiscriminant (Ordering_els) ((EnumData ((Option_els (Ordering_st))) "Some" ("__3")) at{ (Option_Some_sls (Ordering_st)) } "0");
      Switch (I8: int_type) (move{ (IntOp I8) } ("__6")) (<[ 255%Z := 0%nat ]> $ ∅) ([Goto "_bb4"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ BoolOp } val_of_bool true;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasOrd_cmp_def (Ord_A_cmp_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft5" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft11" "vlft5"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft9"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft6" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft12" "vlft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft11"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft14" "plft12"; (* function_call *)
      CallS Ord_A_cmp_loc ["vlft13"; "vlft14"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialEqREFB_eq_def (PartialEq_A_B_eq_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_eq_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialEqREFB_ne_def (PartialEq_A_B_ne_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_ne_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialEqREFmutB_eq_def (PartialEq_A_B_eq_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_eq_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialEqREFmutB_ne_def (PartialEq_A_B_ne_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_ne_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialOrdREFB_ge_def (PartialOrd_A_B_ge_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialOrd_A_B_ge_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialOrdREFB_gt_def (PartialOrd_A_B_gt_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialOrd_A_B_gt_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialOrdREFB_le_def (PartialOrd_A_B_le_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialOrd_A_B_le_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialOrdREFB_lt_def (PartialOrd_A_B_lt_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialOrd_A_B_lt_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFAasPartialOrdREFB_partial_cmp_def (PartialOrd_A_B_partial_cmp_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialOrd_A_B_partial_cmp_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, (use_op_alg' ((Option_els (Ordering_st)) : syn_type)), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFmutAasPartialEqREFB_eq_def (PartialEq_A_B_eq_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_eq_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFmutAasPartialEqREFB_ne_def (PartialEq_A_B_ne_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_ne_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFmutAasPartialEqREFmutB_eq_def (PartialEq_A_B_eq_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_eq_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFmutAasPartialEqREFmutB_ne_def (PartialEq_A_B_ne_loc: loc) (A_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "ulft_4"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft13" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft11"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "B"), "vlft8" } (!{ RefOp } ( !{ RefOp } ( "other" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft14" "vlft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft13"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft14"; (* function_call *)
      CallS PartialEq_A_B_ne_loc ["vlft15"; "vlft16"] [RSTTyVar "A"; RSTTyVar "B"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition boolasPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      "__3" <-{ BoolOp } copy{ BoolOp } (!{ RefOp } ( "self" ));
      local_live{ BoolSynType } "__4";
      "__4" <-{ BoolOp } copy{ BoolOp } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ BoolOp } ("__3")) = { BoolOp , BoolOp , U8 } (move{ BoolOp } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition boolasPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      "__3" <-{ BoolOp } copy{ BoolOp } (!{ RefOp } ( "self" ));
      local_live{ BoolSynType } "__4";
      "__4" <-{ BoolOp } copy{ BoolOp } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ BoolOp } ("__3")) != { BoolOp , BoolOp , U8 } (move{ BoolOp } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__5";
      "__5" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp I128) } ("__4")) <{ (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType I128) } "__7";
      "__7" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__8";
      "__8" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp I128) } ("__7")) = { (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__3")) = { (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__3")) != { (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__3")) ≥{ (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__3")) >{ (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__3")) ≤{ (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__3")) <{ (IntOp I128) , (IntOp I128) , U8 } (move{ (IntOp I128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asPartialOrd_partial_cmp_def (i128asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt I128), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt I128), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS i128asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__5";
      "__5" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp I16) } ("__4")) <{ (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType I16) } "__7";
      "__7" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__8";
      "__8" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp I16) } ("__7")) = { (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__3")) = { (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__3")) != { (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__3")) ≥{ (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__3")) >{ (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__3")) ≤{ (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__3")) <{ (IntOp I16) , (IntOp I16) , U8 } (move{ (IntOp I16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asPartialOrd_partial_cmp_def (i16asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt I16), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt I16), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS i16asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__5";
      "__5" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp I32) } ("__4")) <{ (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType I32) } "__7";
      "__7" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__8";
      "__8" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp I32) } ("__7")) = { (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__3")) = { (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__3")) != { (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__3")) ≥{ (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__3")) >{ (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__3")) ≤{ (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__3")) <{ (IntOp I32) , (IntOp I32) , U8 } (move{ (IntOp I32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asPartialOrd_partial_cmp_def (i32asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt I32), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt I32), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS i32asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__5";
      "__5" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp I64) } ("__4")) <{ (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType I64) } "__7";
      "__7" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__8";
      "__8" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp I64) } ("__7")) = { (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__3")) = { (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__3")) != { (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__3")) ≥{ (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__3")) >{ (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__3")) ≤{ (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__3")) <{ (IntOp I64) , (IntOp I64) , U8 } (move{ (IntOp I64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asPartialOrd_partial_cmp_def (i64asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt I64), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt I64), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS i64asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__5";
      "__5" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp I8) } ("__4")) <{ (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType I8) } "__7";
      "__7" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__8";
      "__8" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp I8) } ("__7")) = { (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__3")) = { (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__3")) != { (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__3")) ≥{ (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__3")) >{ (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__3")) ≤{ (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp I8) } ("__3")) <{ (IntOp I8) , (IntOp I8) , U8 } (move{ (IntOp I8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asPartialOrd_partial_cmp_def (i8asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt I8), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt I8), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS i8asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__5";
      "__5" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp ISize) } ("__4")) <{ (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType ISize) } "__7";
      "__7" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__8";
      "__8" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp ISize) } ("__7")) = { (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__3")) = { (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__3")) != { (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__3")) ≥{ (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__3")) >{ (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__3")) ≤{ (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__3")) <{ (IntOp ISize) , (IntOp ISize) , U8 } (move{ (IntOp ISize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasPartialOrd_partial_cmp_def (isizeasOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt ISize), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt ISize), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS isizeasOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition max_def (Ord_T_max_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("v1", (use_layout_alg' T_st) : layout);
     ("v2", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ T_st } "__3";
      "__3" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v1");
      local_live{ T_st } "__4";
      "__4" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v2");
      CallS Ord_T_max_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' T_st) } ("__3"); move{ (use_op_alg' T_st) } ("__4")] (Some (Na1Ord, (use_op_alg' T_st), "__0"))
      ( Goto "_bb1")
      ( Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition max_by_def (DropGlue_T_drop_glue_loc: loc) (FnOnce_F_REFTREFT_call_once_loc: loc) (Ordering_is_lt_loc: loc) (T_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("v1", (use_layout_alg' T_st) : layout);
     ("v2", (use_layout_alg' T_st) : layout);
     ("compare", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ BoolSynType } "__12";
      local_live{ BoolSynType } "__13";
      "__13" <-{ BoolOp } val_of_bool false;
      "__12" <-{ BoolOp } val_of_bool false;
      "__13" <-{ BoolOp } val_of_bool true;
      "__12" <-{ BoolOp } val_of_bool true;
      local_live{ BoolSynType } "__4";
      local_live{ Ordering_st } "__5";
      local_live{ F_st } "__6";
      "__6" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("compare");
      local_live{ ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) } "__7";
      local_live{ RefSynType } "__8";
      local_live{ RefSynType } "__9";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__9" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "llft2" } ("v2");
      annot{ 1 }: CopyLftNameAnnot "plft11" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft11"; (* borrow *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft3" } (!{ RefOp } ( "__9" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "vlft3"; (* post-assignment *)
      local_live{ RefSynType } "__10";
      local_live{ RefSynType } "__11";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__11" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "llft4" } ("v1");
      annot{ 1 }: CopyLftNameAnnot "plft13" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft13"; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft5" } (!{ RefOp } ( "__11" ));
      annot{ 1 }: CopyLftNameAnnot "plft12" "vlft5"; (* post-assignment *)
      "__7" <-{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } StructInit (tuple2_sls (RefSynType) (RefSynType)) [("0", move{ RefOp } ("__8") : expr); ("1", move{ RefOp } ("__10") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft8" "plft10"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "plft12"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* function_call *)
      CallS FnOnce_F_REFTREFT_call_once_loc ["vlft6"; "vlft7"; "vlft6"; "vlft7"] [RSTTyVar "T"; RSTTyVar "F"] [@{expr} move{ (use_op_alg' F_st) } ("__6"); move{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__5"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb8")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__10";
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      CallS Ordering_is_lt_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__5")] (Some (Na1Ord, BoolOp, "__4"))
      ( Goto "_bb2")
      ( Goto "_bb8")
     ]>%E $
     <[
     "_bb2" :=
      if{ BoolOp }: move{ BoolOp } ("__4") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__11";
      local_dead "__9";
      local_dead "__5";
      "__13" <-{ BoolOp } val_of_bool false;
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v1");
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__11";
      local_dead "__9";
      local_dead "__5";
      "__12" <-{ BoolOp } val_of_bool false;
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v2");
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__4";
      if{ BoolOp }: copy{ BoolOp } ("__12") then
       Goto "_bb10"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb11"
      else
       Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
     <[
     "_bb8" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v2")] None
      ( Goto "_bb13")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb9" :=
      Unwind
     ]>%E $
     <[
     "_bb10" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v2")] None
      ( Goto "_bb6")
      ( Goto "_bb13")
     ]>%E $
     <[
     "_bb11" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v1")] None
      ( Goto "_bb7")
      ( Goto "_bb9")
     ]>%E $
     <[
     "_bb12" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v1")] None
      ( Goto "_bb9")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb13" :=
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb12"
      else
       Goto "_bb9"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition min_def (Ord_T_min_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("v1", (use_layout_alg' T_st) : layout);
     ("v2", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ T_st } "__3";
      "__3" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v1");
      local_live{ T_st } "__4";
      "__4" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v2");
      CallS Ord_T_min_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' T_st) } ("__3"); move{ (use_op_alg' T_st) } ("__4")] (Some (Na1Ord, (use_op_alg' T_st), "__0"))
      ( Goto "_bb1")
      ( Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition min_by_def (DropGlue_T_drop_glue_loc: loc) (FnOnce_F_REFTREFT_call_once_loc: loc) (Ordering_is_lt_loc: loc) (T_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("v1", (use_layout_alg' T_st) : layout);
     ("v2", (use_layout_alg' T_st) : layout);
     ("compare", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ T_st } "__0";
      local_live{ BoolSynType } "__12";
      local_live{ BoolSynType } "__13";
      "__13" <-{ BoolOp } val_of_bool false;
      "__12" <-{ BoolOp } val_of_bool false;
      "__13" <-{ BoolOp } val_of_bool true;
      "__12" <-{ BoolOp } val_of_bool true;
      local_live{ BoolSynType } "__4";
      local_live{ Ordering_st } "__5";
      local_live{ F_st } "__6";
      "__6" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("compare");
      local_live{ ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) } "__7";
      local_live{ RefSynType } "__8";
      local_live{ RefSynType } "__9";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__9" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "llft2" } ("v2");
      annot{ 1 }: CopyLftNameAnnot "plft11" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft11"; (* borrow *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft3" } (!{ RefOp } ( "__9" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "vlft3"; (* post-assignment *)
      local_live{ RefSynType } "__10";
      local_live{ RefSynType } "__11";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__11" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "llft4" } ("v1");
      annot{ 1 }: CopyLftNameAnnot "plft13" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft13"; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft5" } (!{ RefOp } ( "__11" ));
      annot{ 1 }: CopyLftNameAnnot "plft12" "vlft5"; (* post-assignment *)
      "__7" <-{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } StructInit (tuple2_sls (RefSynType) (RefSynType)) [("0", move{ RefOp } ("__8") : expr); ("1", move{ RefOp } ("__10") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft8" "plft10"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "plft12"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft9"; (* function_call *)
      CallS FnOnce_F_REFTREFT_call_once_loc ["vlft6"; "vlft7"; "vlft6"; "vlft7"] [RSTTyVar "T"; RSTTyVar "F"] [@{expr} move{ (use_op_alg' F_st) } ("__6"); move{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__5"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb8")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__10";
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      CallS Ordering_is_lt_loc [] [] [@{expr} move{ (use_op_alg' Ordering_st) } ("__5")] (Some (Na1Ord, BoolOp, "__4"))
      ( Goto "_bb2")
      ( Goto "_bb8")
     ]>%E $
     <[
     "_bb2" :=
      if{ BoolOp }: move{ BoolOp } ("__4") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__11";
      local_dead "__9";
      local_dead "__5";
      "__12" <-{ BoolOp } val_of_bool false;
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v2");
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__11";
      local_dead "__9";
      local_dead "__5";
      "__13" <-{ BoolOp } val_of_bool false;
      "__0" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("v1");
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__4";
      if{ BoolOp }: copy{ BoolOp } ("__12") then
       Goto "_bb10"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb11"
      else
       Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      return (move{ (use_op_alg' T_st) } ("__0"))
     ]>%E $
     <[
     "_bb8" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v2")] None
      ( Goto "_bb13")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb9" :=
      Unwind
     ]>%E $
     <[
     "_bb10" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v2")] None
      ( Goto "_bb6")
      ( Goto "_bb13")
     ]>%E $
     <[
     "_bb11" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v1")] None
      ( Goto "_bb7")
      ( Goto "_bb9")
     ]>%E $
     <[
     "_bb12" :=
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("v1")] None
      ( Goto "_bb9")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb13" :=
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb12"
      else
       Goto "_bb9"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_option_OptionTasOrd_cmp_def (Ord_T_cmp_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      local_live{ (IntSynType ISize) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ (IntSynType ISize) } "__8";
      annot{ 1 }: CopyLftNameAnnot "plft13" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft14" "ulft_2"; (* initialization *)
      local_live{ ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      "__4" <-{ RefOp } copy{ RefOp } ("self");
      annot{ 1 }: CopyLftNameAnnot "plft17" "plft13"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      "__5" <-{ RefOp } copy{ RefOp } ("other");
      annot{ 1 }: CopyLftNameAnnot "plft18" "plft14"; (* post-assignment *)
      "__3" <-{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } StructInit (tuple2_sls (RefSynType) (RefSynType)) [("0", move{ RefOp } ("__4") : expr); ("1", move{ RefOp } ("__5") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft15" "plft17"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft16" "plft18"; (* post-assignment *)
      local_dead "__5";
      local_dead "__4";
      "__8" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "0" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__8")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      "__6" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__6")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb6"; Goto "_bb7"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb3" :=
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb5"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb9"
     ]>%E $
     <[
     "_bb5" :=
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb9"
     ]>%E $
     <[
     "_bb6" :=
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb9"
     ]>%E $
     <[
     "_bb7" :=
      local_live{ RefSynType } "l";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft15"; (* borrow *)
      "l" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft7" } ((EnumData ((Option_els (T_st))) "Some" (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "0" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft19" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "r";
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft16"; (* borrow *)
      "r" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft9" } ((EnumData ((Option_els (T_st))) "Some" (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft20" "vlft9"; (* post-assignment *)
      local_live{ RefSynType } "__11";
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft19"; (* borrow *)
      "__11" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft11" } (!{ RefOp } ( "l" ));
      annot{ 1 }: CopyLftNameAnnot "plft21" "vlft11"; (* post-assignment *)
      local_live{ RefSynType } "__12";
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft20"; (* borrow *)
      "__12" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft12" } (!{ RefOp } ( "r" ));
      annot{ 1 }: CopyLftNameAnnot "plft22" "vlft12"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft23" "plft21"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft24" "plft22"; (* function_call *)
      CallS Ord_T_cmp_loc ["vlft23"; "vlft24"] [RSTTyVar "T"] [@{expr} move{ RefOp } ("__11"); move{ RefOp } ("__12")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__0"))
      ( Goto "_bb8")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__12";
      local_dead "__11";
      local_dead "r";
      local_dead "l";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_option_OptionTasPartialEq_eq_def (PartialEq_T_T_eq_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType ISize) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ (IntSynType ISize) } "__8";
      annot{ 1 }: CopyLftNameAnnot "plft13" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft14" "ulft_2"; (* initialization *)
      local_live{ ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      "__4" <-{ RefOp } copy{ RefOp } ("self");
      annot{ 1 }: CopyLftNameAnnot "plft17" "plft13"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      "__5" <-{ RefOp } copy{ RefOp } ("other");
      annot{ 1 }: CopyLftNameAnnot "plft18" "plft14"; (* post-assignment *)
      "__3" <-{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } StructInit (tuple2_sls (RefSynType) (RefSynType)) [("0", move{ RefOp } ("__4") : expr); ("1", move{ RefOp } ("__5") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft15" "plft17"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft16" "plft18"; (* post-assignment *)
      local_dead "__5";
      local_dead "__4";
      "__8" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "0" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__8")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      "__6" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__6")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb6"; Goto "_bb7"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb3" :=
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb5"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ BoolOp } val_of_bool true;
      Goto "_bb9"
     ]>%E $
     <[
     "_bb5" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb9"
     ]>%E $
     <[
     "_bb6" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb9"
     ]>%E $
     <[
     "_bb7" :=
      local_live{ RefSynType } "l";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft15"; (* borrow *)
      "l" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft7" } ((EnumData ((Option_els (T_st))) "Some" (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "0" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft19" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "r";
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft16"; (* borrow *)
      "r" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft9" } ((EnumData ((Option_els (T_st))) "Some" (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft20" "vlft9"; (* post-assignment *)
      local_live{ RefSynType } "__11";
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft19"; (* borrow *)
      "__11" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft11" } (!{ RefOp } ( "l" ));
      annot{ 1 }: CopyLftNameAnnot "plft21" "vlft11"; (* post-assignment *)
      local_live{ RefSynType } "__12";
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft20"; (* borrow *)
      "__12" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft12" } (!{ RefOp } ( "r" ));
      annot{ 1 }: CopyLftNameAnnot "plft22" "vlft12"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft23" "plft21"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft24" "plft22"; (* function_call *)
      CallS PartialEq_T_T_eq_loc ["vlft23"; "vlft24"] [RSTTyVar "T"] [@{expr} move{ RefOp } ("__11"); move{ RefOp } ("__12")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb8")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__12";
      local_dead "__11";
      local_dead "r";
      local_dead "l";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition std_option_OptionTasPartialOrd_partial_cmp_def (PartialOrd_T_T_partial_cmp_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__6";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ (IntSynType ISize) } "__8";
      annot{ 1 }: CopyLftNameAnnot "plft13" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft14" "ulft_2"; (* initialization *)
      local_live{ ((tuple2_sls (RefSynType) (RefSynType)) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      "__4" <-{ RefOp } copy{ RefOp } ("self");
      annot{ 1 }: CopyLftNameAnnot "plft17" "plft13"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      "__5" <-{ RefOp } copy{ RefOp } ("other");
      annot{ 1 }: CopyLftNameAnnot "plft18" "plft14"; (* post-assignment *)
      "__3" <-{ (use_op_alg' ((tuple2_sls (RefSynType) (RefSynType)) : syn_type)) } StructInit (tuple2_sls (RefSynType) (RefSynType)) [("0", move{ RefOp } ("__4") : expr); ("1", move{ RefOp } ("__5") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft15" "plft17"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft16" "plft18"; (* post-assignment *)
      local_dead "__5";
      local_dead "__4";
      "__8" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "0" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__8")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      "__6" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__6")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb6"; Goto "_bb7"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb3" :=
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (T_st))) (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb5"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb4" :=
      local_live{ Ordering_st } "__15";
      "__15" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__15") : expr)]);
      local_dead "__15";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb5" :=
      local_live{ Ordering_st } "__14";
      "__14" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__14") : expr)]);
      local_dead "__14";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb6" :=
      local_live{ Ordering_st } "__13";
      "__13" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__13") : expr)]);
      local_dead "__13";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb7" :=
      local_live{ RefSynType } "l";
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft15"; (* borrow *)
      "l" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft7" } ((EnumData ((Option_els (T_st))) "Some" (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "0" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft19" "vlft7"; (* post-assignment *)
      local_live{ RefSynType } "r";
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft16"; (* borrow *)
      "r" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft9" } ((EnumData ((Option_els (T_st))) "Some" (!{ RefOp } ( ("__3") at{ (tuple2_sls (RefSynType) (RefSynType)) } "1" ))) at{ (Option_Some_sls (T_st)) } "0");
      annot{ 1 }: CopyLftNameAnnot "plft20" "vlft9"; (* post-assignment *)
      local_live{ RefSynType } "__11";
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft19"; (* borrow *)
      "__11" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft11" } (!{ RefOp } ( "l" ));
      annot{ 1 }: CopyLftNameAnnot "plft21" "vlft11"; (* post-assignment *)
      local_live{ RefSynType } "__12";
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft20"; (* borrow *)
      "__12" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft12" } (!{ RefOp } ( "r" ));
      annot{ 1 }: CopyLftNameAnnot "plft22" "vlft12"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft23" "plft21"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft24" "plft22"; (* function_call *)
      CallS PartialOrd_T_T_partial_cmp_loc ["vlft23"; "vlft24"] [RSTTyVar "T"] [@{expr} move{ RefOp } ("__11"); move{ RefOp } ("__12")] (Some (Na1Ord, (use_op_alg' ((Option_els (Ordering_st)) : syn_type)), "__0"))
      ( Goto "_bb8")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__12";
      local_dead "__11";
      local_dead "r";
      local_dead "l";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__5";
      "__5" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp U128) } ("__4")) <{ (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType U128) } "__7";
      "__7" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__8";
      "__8" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp U128) } ("__7")) = { (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U128) } ("__3")) = { (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U128) } ("__3")) != { (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U128) } ("__3")) ≥{ (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U128) } ("__3")) >{ (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U128) } ("__3")) ≤{ (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U128) } ("__3")) <{ (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asPartialOrd_partial_cmp_def (u128asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt U128), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt U128), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS u128asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__5";
      "__5" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp U16) } ("__4")) <{ (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType U16) } "__7";
      "__7" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__8";
      "__8" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp U16) } ("__7")) = { (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U16) } ("__3")) = { (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U16) } ("__3")) != { (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U16) } ("__3")) ≥{ (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U16) } ("__3")) >{ (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U16) } ("__3")) ≤{ (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U16) } ("__3")) <{ (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asPartialOrd_partial_cmp_def (u16asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt U16), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt U16), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS u16asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__5";
      "__5" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp U32) } ("__4")) <{ (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType U32) } "__7";
      "__7" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__8";
      "__8" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp U32) } ("__7")) = { (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U32) } ("__3")) = { (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U32) } ("__3")) != { (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U32) } ("__3")) ≥{ (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U32) } ("__3")) >{ (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U32) } ("__3")) ≤{ (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U32) } ("__3")) <{ (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asPartialOrd_partial_cmp_def (u32asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt U32), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt U32), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS u32asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__5";
      "__5" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp U64) } ("__4")) <{ (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType U64) } "__7";
      "__7" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__8";
      "__8" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp U64) } ("__7")) = { (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U64) } ("__3")) = { (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U64) } ("__3")) != { (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U64) } ("__3")) ≥{ (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U64) } ("__3")) >{ (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U64) } ("__3")) ≤{ (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U64) } ("__3")) <{ (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asPartialOrd_partial_cmp_def (u64asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt U64), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt U64), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS u64asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__5";
      "__5" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp U8) } ("__4")) <{ (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType U8) } "__7";
      "__7" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__8";
      "__8" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp U8) } ("__7")) = { (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U8) } ("__3")) = { (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U8) } ("__3")) != { (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U8) } ("__3")) ≥{ (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U8) } ("__3")) >{ (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U8) } ("__3")) ≤{ (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp U8) } ("__3")) <{ (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asPartialOrd_partial_cmp_def (u8asOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt U8), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt U8), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS u8asOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unitasOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("_other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unitasPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("_other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      "__0" <-{ BoolOp } val_of_bool true;
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unitasPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("_other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      "__0" <-{ BoolOp } val_of_bool false;
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition unitasPartialOrd_partial_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("__2", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      "__3" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasOrd_cmp_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ Ordering_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__3" <-{ BoolOp } (move{ (IntOp USize) } ("__4")) <{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Less" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Less_sls []);
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__6" <-{ BoolOp } (move{ (IntOp USize) } ("__7")) = { (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Equal" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Equal_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' Ordering_st) } EnumInit Ordering_els "Greater" (RSTEnumDef ["Ordering_enum"] (RSTScopeInst [] [] [])) (StructInit Ordering_Greater_sls []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      return (move{ (use_op_alg' Ordering_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialEq_eq_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) = { (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialEq_ne_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) != { (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialOrd_ge_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) ≥{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialOrd_gt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) >{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialOrd_le_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) ≤{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialOrd_lt_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "other" ));
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) <{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasPartialOrd_partial_cmp_def (usizeasOrd_cmp_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Ordering_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_2"; (* initialization *)
      local_live{ Ordering_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTInt USize), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft4"; (* post-assignment *)
      local_live{ RefSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft7"; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTInt USize), "vlft5" } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS usizeasOrd_cmp_loc ["vlft10"; "vlft11"] [] [@{expr} move{ RefOp } ("__4"); move{ RefOp } ("__5")] (Some (Na1Ord, (use_op_alg' Ordering_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__0" <-{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } EnumInit (Option_els (Ordering_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["Ordering_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Option_Some_sls (Ordering_st)) [("0", move{ (use_op_alg' Ordering_st) } ("__3") : expr)]);
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (Ordering_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.