From radium Require Import lang notation.
From refinedrust Require Import typing shims.
Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition i128_is_negative_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I128) } "__2";
      "__2" <-{ (IntOp I128) } copy{ (IntOp I128) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__2")) <{ (IntOp I128) , (IntOp I128) , U8 } (i2v (0) I128);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128_is_positive_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I128) } "__2";
      "__2" <-{ (IntOp I128) } copy{ (IntOp I128) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I128) } ("__2")) >{ (IntOp I128) , (IntOp I128) , U8 } (i2v (0) I128);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16_is_negative_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I16) } "__2";
      "__2" <-{ (IntOp I16) } copy{ (IntOp I16) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__2")) <{ (IntOp I16) , (IntOp I16) , U8 } (i2v (0) I16);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16_is_positive_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I16) } "__2";
      "__2" <-{ (IntOp I16) } copy{ (IntOp I16) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I16) } ("__2")) >{ (IntOp I16) , (IntOp I16) , U8 } (i2v (0) I16);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32_is_negative_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I32) } "__2";
      "__2" <-{ (IntOp I32) } copy{ (IntOp I32) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__2")) <{ (IntOp I32) , (IntOp I32) , U8 } (i2v (0) I32);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32_is_positive_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I32) } "__2";
      "__2" <-{ (IntOp I32) } copy{ (IntOp I32) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I32) } ("__2")) >{ (IntOp I32) , (IntOp I32) , U8 } (i2v (0) I32);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64_is_negative_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I64) } "__2";
      "__2" <-{ (IntOp I64) } copy{ (IntOp I64) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__2")) <{ (IntOp I64) , (IntOp I64) , U8 } (i2v (0) I64);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64_is_positive_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I64) } "__2";
      "__2" <-{ (IntOp I64) } copy{ (IntOp I64) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp I64) } ("__2")) >{ (IntOp I64) , (IntOp I64) , U8 } (i2v (0) I64);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8_is_negative_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      "__2" <-{ (IntOp I8) } copy{ (IntOp I8) } ("x");
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




Program Definition i8_is_positive_def  : function :=
  {|
     f_args := [
      ("x", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType I8) } "__2";
      "__2" <-{ (IntOp I8) } copy{ (IntOp I8) } ("x");
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




Program Definition isize_is_negative_def  : function :=
  {|
     f_args := [
      ("x", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType ISize) } "__2";
      "__2" <-{ (IntOp ISize) } copy{ (IntOp ISize) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__2")) <{ (IntOp ISize) , (IntOp ISize) , U8 } (i2v (0) ISize);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isize_is_positive_def  : function :=
  {|
     f_args := [
      ("x", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType ISize) } "__2";
      "__2" <-{ (IntOp ISize) } copy{ (IntOp ISize) } ("x");
      "__0" <-{ BoolOp } (move{ (IntOp ISize) } ("__2")) >{ (IntOp ISize) , (IntOp ISize) , U8 } (i2v (0) ISize);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128_abs_diff_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("x", (it_layout U128) : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__8";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__11";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ (IntOp U128) } copy{ (IntOp U128) } ("x");
      local_live{ (IntSynType U128) } "__5";
      "__5" <-{ (IntOp U128) } copy{ (IntOp U128) } ("other");
      "__3" <-{ BoolOp } (move{ (IntOp U128) } ("__4")) <{ (IntOp U128) , (IntOp U128) , U8 } (move{ (IntOp U128) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U128) } "__6";
      "__6" <-{ (IntOp U128) } copy{ (IntOp U128) } ("other");
      local_live{ (IntSynType U128) } "__7";
      "__7" <-{ (IntOp U128) } copy{ (IntOp U128) } ("x");
      "__8" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ (IntOp U128) } ("__6")) -{ (IntOp U128) , (IntOp U128) } (copy{ (IntOp U128) } ("__7")) : expr); ("1", (copy{ (IntOp U128) } ("__6")) -c{ (IntOp U128) , (IntOp U128) } (copy{ (IntOp U128) } ("__7")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__8") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb2"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (IntOp U128) } move{ (IntOp U128) } (("__8") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__7";
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U128) } "__9";
      "__9" <-{ (IntOp U128) } copy{ (IntOp U128) } ("x");
      local_live{ (IntSynType U128) } "__10";
      "__10" <-{ (IntOp U128) } copy{ (IntOp U128) } ("other");
      "__11" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ (IntOp U128) } ("__9")) -{ (IntOp U128) , (IntOp U128) } (copy{ (IntOp U128) } ("__10")) : expr); ("1", (copy{ (IntOp U128) } ("__9")) -c{ (IntOp U128) , (IntOp U128) } (copy{ (IntOp U128) } ("__10")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__11") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb4"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (IntOp U128) } move{ (IntOp U128) } (("__11") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__10";
      local_dead "__9";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ (IntOp U128) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16_abs_diff_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("x", (it_layout U16) : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__8";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__11";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ (IntOp U16) } copy{ (IntOp U16) } ("x");
      local_live{ (IntSynType U16) } "__5";
      "__5" <-{ (IntOp U16) } copy{ (IntOp U16) } ("other");
      "__3" <-{ BoolOp } (move{ (IntOp U16) } ("__4")) <{ (IntOp U16) , (IntOp U16) , U8 } (move{ (IntOp U16) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U16) } "__6";
      "__6" <-{ (IntOp U16) } copy{ (IntOp U16) } ("other");
      local_live{ (IntSynType U16) } "__7";
      "__7" <-{ (IntOp U16) } copy{ (IntOp U16) } ("x");
      "__8" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ (IntOp U16) } ("__6")) -{ (IntOp U16) , (IntOp U16) } (copy{ (IntOp U16) } ("__7")) : expr); ("1", (copy{ (IntOp U16) } ("__6")) -c{ (IntOp U16) , (IntOp U16) } (copy{ (IntOp U16) } ("__7")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__8") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb2"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (IntOp U16) } move{ (IntOp U16) } (("__8") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__7";
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U16) } "__9";
      "__9" <-{ (IntOp U16) } copy{ (IntOp U16) } ("x");
      local_live{ (IntSynType U16) } "__10";
      "__10" <-{ (IntOp U16) } copy{ (IntOp U16) } ("other");
      "__11" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ (IntOp U16) } ("__9")) -{ (IntOp U16) , (IntOp U16) } (copy{ (IntOp U16) } ("__10")) : expr); ("1", (copy{ (IntOp U16) } ("__9")) -c{ (IntOp U16) , (IntOp U16) } (copy{ (IntOp U16) } ("__10")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__11") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb4"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (IntOp U16) } move{ (IntOp U16) } (("__11") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__10";
      local_dead "__9";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ (IntOp U16) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32_abs_diff_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("x", (it_layout U32) : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__8";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__11";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ (IntOp U32) } copy{ (IntOp U32) } ("x");
      local_live{ (IntSynType U32) } "__5";
      "__5" <-{ (IntOp U32) } copy{ (IntOp U32) } ("other");
      "__3" <-{ BoolOp } (move{ (IntOp U32) } ("__4")) <{ (IntOp U32) , (IntOp U32) , U8 } (move{ (IntOp U32) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U32) } "__6";
      "__6" <-{ (IntOp U32) } copy{ (IntOp U32) } ("other");
      local_live{ (IntSynType U32) } "__7";
      "__7" <-{ (IntOp U32) } copy{ (IntOp U32) } ("x");
      "__8" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ (IntOp U32) } ("__6")) -{ (IntOp U32) , (IntOp U32) } (copy{ (IntOp U32) } ("__7")) : expr); ("1", (copy{ (IntOp U32) } ("__6")) -c{ (IntOp U32) , (IntOp U32) } (copy{ (IntOp U32) } ("__7")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__8") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb2"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (IntOp U32) } move{ (IntOp U32) } (("__8") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__7";
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U32) } "__9";
      "__9" <-{ (IntOp U32) } copy{ (IntOp U32) } ("x");
      local_live{ (IntSynType U32) } "__10";
      "__10" <-{ (IntOp U32) } copy{ (IntOp U32) } ("other");
      "__11" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ (IntOp U32) } ("__9")) -{ (IntOp U32) , (IntOp U32) } (copy{ (IntOp U32) } ("__10")) : expr); ("1", (copy{ (IntOp U32) } ("__9")) -c{ (IntOp U32) , (IntOp U32) } (copy{ (IntOp U32) } ("__10")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__11") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb4"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (IntOp U32) } move{ (IntOp U32) } (("__11") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__10";
      local_dead "__9";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ (IntOp U32) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64_abs_diff_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("x", (it_layout U64) : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__8";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__11";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ (IntOp U64) } copy{ (IntOp U64) } ("x");
      local_live{ (IntSynType U64) } "__5";
      "__5" <-{ (IntOp U64) } copy{ (IntOp U64) } ("other");
      "__3" <-{ BoolOp } (move{ (IntOp U64) } ("__4")) <{ (IntOp U64) , (IntOp U64) , U8 } (move{ (IntOp U64) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U64) } "__6";
      "__6" <-{ (IntOp U64) } copy{ (IntOp U64) } ("other");
      local_live{ (IntSynType U64) } "__7";
      "__7" <-{ (IntOp U64) } copy{ (IntOp U64) } ("x");
      "__8" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ (IntOp U64) } ("__6")) -{ (IntOp U64) , (IntOp U64) } (copy{ (IntOp U64) } ("__7")) : expr); ("1", (copy{ (IntOp U64) } ("__6")) -c{ (IntOp U64) , (IntOp U64) } (copy{ (IntOp U64) } ("__7")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__8") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb2"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (IntOp U64) } move{ (IntOp U64) } (("__8") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__7";
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U64) } "__9";
      "__9" <-{ (IntOp U64) } copy{ (IntOp U64) } ("x");
      local_live{ (IntSynType U64) } "__10";
      "__10" <-{ (IntOp U64) } copy{ (IntOp U64) } ("other");
      "__11" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ (IntOp U64) } ("__9")) -{ (IntOp U64) , (IntOp U64) } (copy{ (IntOp U64) } ("__10")) : expr); ("1", (copy{ (IntOp U64) } ("__9")) -c{ (IntOp U64) , (IntOp U64) } (copy{ (IntOp U64) } ("__10")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__11") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb4"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (IntOp U64) } move{ (IntOp U64) } (("__11") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__10";
      local_dead "__9";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ (IntOp U64) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8_abs_diff_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("x", (it_layout U8) : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__8";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__11";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ (IntOp U8) } copy{ (IntOp U8) } ("x");
      local_live{ (IntSynType U8) } "__5";
      "__5" <-{ (IntOp U8) } copy{ (IntOp U8) } ("other");
      "__3" <-{ BoolOp } (move{ (IntOp U8) } ("__4")) <{ (IntOp U8) , (IntOp U8) , U8 } (move{ (IntOp U8) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U8) } "__6";
      "__6" <-{ (IntOp U8) } copy{ (IntOp U8) } ("other");
      local_live{ (IntSynType U8) } "__7";
      "__7" <-{ (IntOp U8) } copy{ (IntOp U8) } ("x");
      "__8" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ (IntOp U8) } ("__6")) -{ (IntOp U8) , (IntOp U8) } (copy{ (IntOp U8) } ("__7")) : expr); ("1", (copy{ (IntOp U8) } ("__6")) -c{ (IntOp U8) , (IntOp U8) } (copy{ (IntOp U8) } ("__7")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__8") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb2"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (IntOp U8) } move{ (IntOp U8) } (("__8") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__7";
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType U8) } "__9";
      "__9" <-{ (IntOp U8) } copy{ (IntOp U8) } ("x");
      local_live{ (IntSynType U8) } "__10";
      "__10" <-{ (IntOp U8) } copy{ (IntOp U8) } ("other");
      "__11" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ (IntOp U8) } ("__9")) -{ (IntOp U8) , (IntOp U8) } (copy{ (IntOp U8) } ("__10")) : expr); ("1", (copy{ (IntOp U8) } ("__9")) -c{ (IntOp U8) , (IntOp U8) } (copy{ (IntOp U8) } ("__10")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__11") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb4"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (IntOp U8) } move{ (IntOp U8) } (("__11") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__10";
      local_dead "__9";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ (IntOp U8) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usize_abs_diff_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("x", (it_layout USize) : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__8";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__11";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("x");
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("other");
      "__3" <-{ BoolOp } (move{ (IntOp USize) } ("__4")) <{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("other");
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("x");
      "__8" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ (IntOp USize) } ("__6")) -{ (IntOp USize) , (IntOp USize) } (copy{ (IntOp USize) } ("__7")) : expr); ("1", (copy{ (IntOp USize) } ("__6")) -c{ (IntOp USize) , (IntOp USize) } (copy{ (IntOp USize) } ("__7")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__8") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb2"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ (IntOp USize) } move{ (IntOp USize) } (("__8") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__7";
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "__9";
      "__9" <-{ (IntOp USize) } copy{ (IntOp USize) } ("x");
      local_live{ (IntSynType USize) } "__10";
      "__10" <-{ (IntOp USize) } copy{ (IntOp USize) } ("other");
      "__11" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ (IntOp USize) } ("__9")) -{ (IntOp USize) , (IntOp USize) } (copy{ (IntOp USize) } ("__10")) : expr); ("1", (copy{ (IntOp USize) } ("__9")) -c{ (IntOp USize) , (IntOp USize) } (copy{ (IntOp USize) } ("__10")) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__11") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb4"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ (IntOp USize) } move{ (IntOp USize) } (("__11") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__10";
      local_dead "__9";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
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