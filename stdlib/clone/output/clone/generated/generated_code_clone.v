From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition Clone_clone_from_def (Clone_Self_clone_loc: loc) (DropGlue_Self_drop_glue_loc: loc) (Self_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("source", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      local_live{ Self_st } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Self"), "vlft4" } (!{ RefOp } ( "source" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "vlft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft7"; (* function_call *)
      CallS Clone_Self_clone_loc ["vlft8"] [] [@{expr} move{ RefOp } ("__4")] (Some (Na1Ord, (use_op_alg' Self_st), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      CallS DropGlue_Self_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } (!{ RefOp } ( "self" ))] None
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      !{ RefOp } ( "self" ) <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("__3");
      local_dead "__3";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
     <[
     "_bb3" :=
      !{ RefOp } ( "self" ) <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("__3");
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition boolasClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ BoolOp } copy{ BoolOp } (!{ RefOp } ( "self" ));
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition charasClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ CharSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ CharOp } copy{ CharOp } (!{ RefOp } ( "self" ));
      return (move{ CharOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition constTasClone_clone_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ PtrOp } copy{ PtrOp } (!{ RefOp } ( "self" ));
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp I128) } copy{ (IntOp I128) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp I128) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp I16) } copy{ (IntOp I16) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp I16) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp I32) } copy{ (IntOp I32) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp I32) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp I64) } copy{ (IntOp I64) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp I64) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp I8) } copy{ (IntOp I8) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp I8) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp ISize) } copy{ (IntOp ISize) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp ISize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition mutTasClone_clone_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ PtrOp } copy{ PtrOp } (!{ RefOp } ( "self" ));
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp U128) } copy{ (IntOp U128) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp U128) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp U16) } copy{ (IntOp U16) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp U16) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp U32) } copy{ (IntOp U32) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp U32) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp U64) } copy{ (IntOp U64) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp U64) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp U8) } copy{ (IntOp U8) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp U8) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasClone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp USize) } copy{ (IntOp USize) } (!{ RefOp } ( "self" ));
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.