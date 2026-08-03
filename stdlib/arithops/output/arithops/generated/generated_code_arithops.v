From radium Require Import lang notation.
From refinedrust Require Import typing shims.
Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition REFTasDeref_deref_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ RefSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft7"; (* composite *)
      "__0" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft4" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft4"; (* post-assignment *)
      annot{ 1 }: ExtendLftAnnot "plft5"; (* return *)
      return (move{ RefOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi128asAddREFai128_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) +{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) +c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi128asAddi128_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) +{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) +c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi128asMulREFai128_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) ×{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) ×c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi128asMuli128_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) ×{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) ×c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi128asSubREFai128_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) -{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) -c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi128asSubi128_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) -{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) -c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi16asAddREFai16_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) +{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) +c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi16asAddi16_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) +{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) +c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi16asMulREFai16_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) ×{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) ×c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi16asMuli16_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) ×{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) ×c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi16asSubREFai16_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) -{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) -c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi16asSubi16_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) -{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) -c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi32asAddREFai32_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) +{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) +c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi32asAddi32_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) +{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) +c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi32asMulREFai32_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) ×{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) ×c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi32asMuli32_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) ×{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) ×c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi32asSubREFai32_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) -{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) -c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi32asSubi32_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) -{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) -c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi64asAddREFai64_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) +{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) +c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi64asAddi64_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) +{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) +c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi64asMulREFai64_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) ×{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) ×c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi64asMuli64_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) ×{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) ×c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi64asSubREFai64_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) -{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) -c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi64asSubi64_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) -{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) -c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi8asAddREFai8_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) +{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) +c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi8asAddi8_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) +{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) +c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi8asMulREFai8_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) ×{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) ×c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi8asMuli8_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) ×{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) ×c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi8asSubREFai8_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) -{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) -c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFi8asSubi8_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) -{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) -c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFisizeasAddREFaisize_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) +{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) +c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFisizeasAddisize_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) +{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) +c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFisizeasMulREFaisize_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) ×{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) ×c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFisizeasMulisize_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) ×{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) ×c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFisizeasSubREFaisize_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) -{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) -c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFisizeasSubisize_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) -{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) -c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFmutTasDeref_deref_def (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ RefSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft7"; (* composite *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft6"; (* composite *)
      "__0" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "T"), "vlft4" } (!{ RefOp } ( !{ RefOp } ( "self" ) ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft4"; (* post-assignment *)
      annot{ 1 }: ExtendLftAnnot "plft5"; (* return *)
      return (move{ RefOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu128asAddREFau128_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) +{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) +c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu128asAddu128_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) +{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) +c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu128asMulREFau128_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) ×{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) ×c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu128asMulu128_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) ×{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) ×c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu128asSubREFau128_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) -{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) -c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu128asSubu128_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) -{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) -c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu16asAddREFau16_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) +{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) +c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu16asAddu16_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) +{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) +c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu16asMulREFau16_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) ×{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) ×c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu16asMulu16_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) ×{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) ×c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu16asSubREFau16_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) -{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) -c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu16asSubu16_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) -{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) -c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu32asAddREFau32_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) +{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) +c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu32asAddu32_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) +{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) +c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu32asMulREFau32_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) ×{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) ×c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu32asMulu32_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) ×{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) ×c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu32asSubREFau32_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) -{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) -c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu32asSubu32_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) -{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) -c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu64asAddREFau64_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) +{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) +c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu64asAddu64_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) +{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) +c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu64asMulREFau64_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) ×{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) ×c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu64asMulu64_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) ×{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) ×c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu64asSubREFau64_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) -{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) -c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu64asSubu64_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) -{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) -c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu8asAddREFau8_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) +{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) +c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu8asAddu8_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) +{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) +c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu8asMulREFau8_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) ×{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) ×c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu8asMulu8_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) ×{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) ×c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu8asSubREFau8_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) -{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) -c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFu8asSubu8_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) -{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) -c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFusizeasAddREFausize_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) +{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) +c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFusizeasAddusize_add_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) +{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) +c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFusizeasMulREFausize_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) ×{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) ×c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFusizeasMulusize_mul_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) ×{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) ×c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFusizeasSubREFausize_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_a"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) -{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) -c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition REFusizeasSubusize_sub_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "self" ));
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) -{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) -c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asAddAssignREFi128_add_assign_def (i128asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I128), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I128) } "__5";
      "__5" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i128asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I128 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } (!{ RefOp } ( "self" ))) +{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__3")) : expr); ("1", (copy{ IntOp I128 } (!{ RefOp } ( "self" ))) +c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I128 } move{ IntOp I128 } (("__4") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asAddREFai128_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I128) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("self");
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) +{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) +c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I128) : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("self");
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) +{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) +c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asMulAssignREFi128_mul_assign_def (i128asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I128), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I128) } "__5";
      "__5" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i128asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I128 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } (!{ RefOp } ( "self" ))) ×{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__3")) : expr); ("1", (copy{ IntOp I128 } (!{ RefOp } ( "self" ))) ×c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I128 } move{ IntOp I128 } (("__4") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asMulREFai128_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I128) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("self");
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) ×{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) ×c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I128) : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("self");
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) ×{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) ×c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asSubAssignREFi128_sub_assign_def (i128asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I128), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I128) } "__5";
      "__5" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i128asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I128 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } (!{ RefOp } ( "self" ))) -{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__3")) : expr); ("1", (copy{ IntOp I128 } (!{ RefOp } ( "self" ))) -c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I128 } move{ IntOp I128 } (("__4") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asSubREFai128_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I128) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("self");
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) -{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) -c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i128asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I128) : layout);
     ("other", (it_layout I128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I128) } "__3";
      "__3" <-{ IntOp I128 } copy{ IntOp I128 } ("self");
      local_live{ (IntSynType I128) } "__4";
      "__4" <-{ IntOp I128 } copy{ IntOp I128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I128)) BoolSynType) [("0", (copy{ IntOp I128 } ("__3")) -{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr); ("1", (copy{ IntOp I128 } ("__3")) -c{ IntOp I128 , IntOp I128 } (copy{ IntOp I128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I128 } move{ IntOp I128 } (("__5") at{ (tuple2_sls ((IntSynType I128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asAddAssignREFi16_add_assign_def (i16asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I16), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I16) } "__5";
      "__5" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i16asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I16 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } (!{ RefOp } ( "self" ))) +{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__3")) : expr); ("1", (copy{ IntOp I16 } (!{ RefOp } ( "self" ))) +c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I16 } move{ IntOp I16 } (("__4") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asAddREFai16_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I16) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("self");
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) +{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) +c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I16) : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("self");
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) +{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) +c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asMulAssignREFi16_mul_assign_def (i16asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I16), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I16) } "__5";
      "__5" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i16asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I16 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } (!{ RefOp } ( "self" ))) ×{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__3")) : expr); ("1", (copy{ IntOp I16 } (!{ RefOp } ( "self" ))) ×c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I16 } move{ IntOp I16 } (("__4") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asMulREFai16_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I16) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("self");
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) ×{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) ×c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I16) : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("self");
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) ×{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) ×c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asSubAssignREFi16_sub_assign_def (i16asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I16), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I16) } "__5";
      "__5" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i16asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I16 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } (!{ RefOp } ( "self" ))) -{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__3")) : expr); ("1", (copy{ IntOp I16 } (!{ RefOp } ( "self" ))) -c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I16 } move{ IntOp I16 } (("__4") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asSubREFai16_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I16) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("self");
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) -{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) -c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i16asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I16) : layout);
     ("other", (it_layout I16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I16) } "__3";
      "__3" <-{ IntOp I16 } copy{ IntOp I16 } ("self");
      local_live{ (IntSynType I16) } "__4";
      "__4" <-{ IntOp I16 } copy{ IntOp I16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I16)) BoolSynType) [("0", (copy{ IntOp I16 } ("__3")) -{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr); ("1", (copy{ IntOp I16 } ("__3")) -c{ IntOp I16 , IntOp I16 } (copy{ IntOp I16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I16 } move{ IntOp I16 } (("__5") at{ (tuple2_sls ((IntSynType I16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asAddAssignREFi32_add_assign_def (i32asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I32), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I32) } "__5";
      "__5" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i32asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I32 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } (!{ RefOp } ( "self" ))) +{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__3")) : expr); ("1", (copy{ IntOp I32 } (!{ RefOp } ( "self" ))) +c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I32 } move{ IntOp I32 } (("__4") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asAddREFai32_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I32) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("self");
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) +{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) +c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I32) : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("self");
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) +{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) +c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asMulAssignREFi32_mul_assign_def (i32asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I32), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I32) } "__5";
      "__5" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i32asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I32 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } (!{ RefOp } ( "self" ))) ×{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__3")) : expr); ("1", (copy{ IntOp I32 } (!{ RefOp } ( "self" ))) ×c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I32 } move{ IntOp I32 } (("__4") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asMulREFai32_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I32) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("self");
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) ×{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) ×c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I32) : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("self");
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) ×{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) ×c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asSubAssignREFi32_sub_assign_def (i32asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I32), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I32) } "__5";
      "__5" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i32asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I32 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } (!{ RefOp } ( "self" ))) -{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__3")) : expr); ("1", (copy{ IntOp I32 } (!{ RefOp } ( "self" ))) -c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I32 } move{ IntOp I32 } (("__4") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asSubREFai32_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I32) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("self");
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) -{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) -c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i32asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I32) : layout);
     ("other", (it_layout I32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I32) } "__3";
      "__3" <-{ IntOp I32 } copy{ IntOp I32 } ("self");
      local_live{ (IntSynType I32) } "__4";
      "__4" <-{ IntOp I32 } copy{ IntOp I32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I32)) BoolSynType) [("0", (copy{ IntOp I32 } ("__3")) -{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr); ("1", (copy{ IntOp I32 } ("__3")) -c{ IntOp I32 , IntOp I32 } (copy{ IntOp I32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I32 } move{ IntOp I32 } (("__5") at{ (tuple2_sls ((IntSynType I32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asAddAssignREFi64_add_assign_def (i64asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I64), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I64) } "__5";
      "__5" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i64asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I64 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } (!{ RefOp } ( "self" ))) +{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__3")) : expr); ("1", (copy{ IntOp I64 } (!{ RefOp } ( "self" ))) +c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I64 } move{ IntOp I64 } (("__4") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asAddREFai64_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I64) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("self");
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) +{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) +c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I64) : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("self");
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) +{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) +c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asMulAssignREFi64_mul_assign_def (i64asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I64), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I64) } "__5";
      "__5" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i64asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I64 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } (!{ RefOp } ( "self" ))) ×{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__3")) : expr); ("1", (copy{ IntOp I64 } (!{ RefOp } ( "self" ))) ×c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I64 } move{ IntOp I64 } (("__4") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asMulREFai64_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I64) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("self");
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) ×{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) ×c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I64) : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("self");
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) ×{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) ×c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asSubAssignREFi64_sub_assign_def (i64asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I64), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I64) } "__5";
      "__5" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i64asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I64 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } (!{ RefOp } ( "self" ))) -{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__3")) : expr); ("1", (copy{ IntOp I64 } (!{ RefOp } ( "self" ))) -c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I64 } move{ IntOp I64 } (("__4") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asSubREFai64_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I64) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("self");
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) -{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) -c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i64asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I64) : layout);
     ("other", (it_layout I64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I64) } "__3";
      "__3" <-{ IntOp I64 } copy{ IntOp I64 } ("self");
      local_live{ (IntSynType I64) } "__4";
      "__4" <-{ IntOp I64 } copy{ IntOp I64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I64)) BoolSynType) [("0", (copy{ IntOp I64 } ("__3")) -{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr); ("1", (copy{ IntOp I64 } ("__3")) -c{ IntOp I64 , IntOp I64 } (copy{ IntOp I64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I64 } move{ IntOp I64 } (("__5") at{ (tuple2_sls ((IntSynType I64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asAddAssignREFi8_add_assign_def (i8asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I8), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I8) } "__5";
      "__5" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i8asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I8 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } (!{ RefOp } ( "self" ))) +{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__3")) : expr); ("1", (copy{ IntOp I8 } (!{ RefOp } ( "self" ))) +c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I8 } move{ IntOp I8 } (("__4") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asAddREFai8_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I8) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("self");
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) +{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) +c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I8) : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("self");
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) +{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) +c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asMulAssignREFi8_mul_assign_def (i8asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I8), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I8) } "__5";
      "__5" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i8asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I8 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } (!{ RefOp } ( "self" ))) ×{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__3")) : expr); ("1", (copy{ IntOp I8 } (!{ RefOp } ( "self" ))) ×c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I8 } move{ IntOp I8 } (("__4") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asMulREFai8_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I8) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("self");
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) ×{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) ×c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I8) : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("self");
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) ×{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) ×c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asSubAssignREFi8_sub_assign_def (i8asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt I8), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType I8) } "__5";
      "__5" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS i8asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp I8 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } (!{ RefOp } ( "self" ))) -{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__3")) : expr); ("1", (copy{ IntOp I8 } (!{ RefOp } ( "self" ))) -c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp I8 } move{ IntOp I8 } (("__4") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asSubREFai8_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I8) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("self");
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) -{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) -c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition i8asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout I8) : layout);
     ("other", (it_layout I8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType I8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType I8) } "__3";
      "__3" <-{ IntOp I8 } copy{ IntOp I8 } ("self");
      local_live{ (IntSynType I8) } "__4";
      "__4" <-{ IntOp I8 } copy{ IntOp I8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType I8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType I8)) BoolSynType) [("0", (copy{ IntOp I8 } ("__3")) -{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr); ("1", (copy{ IntOp I8 } ("__3")) -c{ IntOp I8 , IntOp I8 } (copy{ IntOp I8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp I8 } move{ IntOp I8 } (("__5") at{ (tuple2_sls ((IntSynType I8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp I8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasAddAssignREFisize_add_assign_def (isizeasAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt ISize), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType ISize) } "__5";
      "__5" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS isizeasAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp ISize } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } (!{ RefOp } ( "self" ))) +{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__3")) : expr); ("1", (copy{ IntOp ISize } (!{ RefOp } ( "self" ))) +c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp ISize } move{ IntOp ISize } (("__4") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasAddREFaisize_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout ISize) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("self");
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) +{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) +c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout ISize) : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("self");
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) +{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) +c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasMulAssignREFisize_mul_assign_def (isizeasMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt ISize), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType ISize) } "__5";
      "__5" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS isizeasMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp ISize } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } (!{ RefOp } ( "self" ))) ×{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__3")) : expr); ("1", (copy{ IntOp ISize } (!{ RefOp } ( "self" ))) ×c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp ISize } move{ IntOp ISize } (("__4") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasMulREFaisize_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout ISize) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("self");
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) ×{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) ×c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout ISize) : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("self");
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) ×{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) ×c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasSubAssignREFisize_sub_assign_def (isizeasSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt ISize), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType ISize) } "__5";
      "__5" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS isizeasSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp ISize } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } (!{ RefOp } ( "self" ))) -{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__3")) : expr); ("1", (copy{ IntOp ISize } (!{ RefOp } ( "self" ))) -c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp ISize } move{ IntOp ISize } (("__4") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasSubREFaisize_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout ISize) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("self");
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) -{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) -c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition isizeasSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout ISize) : layout);
     ("other", (it_layout ISize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType ISize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType ISize) } "__3";
      "__3" <-{ IntOp ISize } copy{ IntOp ISize } ("self");
      local_live{ (IntSynType ISize) } "__4";
      "__4" <-{ IntOp ISize } copy{ IntOp ISize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType ISize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType ISize)) BoolSynType) [("0", (copy{ IntOp ISize } ("__3")) -{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr); ("1", (copy{ IntOp ISize } ("__3")) -c{ IntOp ISize , IntOp ISize } (copy{ IntOp ISize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp ISize } move{ IntOp ISize } (("__5") at{ (tuple2_sls ((IntSynType ISize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp ISize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asAddAssignREFu128_add_assign_def (u128asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U128), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U128) } "__5";
      "__5" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u128asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U128 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } (!{ RefOp } ( "self" ))) +{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__3")) : expr); ("1", (copy{ IntOp U128 } (!{ RefOp } ( "self" ))) +c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U128 } move{ IntOp U128 } (("__4") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asAddREFau128_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U128) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("self");
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) +{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) +c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U128) : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("self");
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) +{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) +c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asMulAssignREFu128_mul_assign_def (u128asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U128), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U128) } "__5";
      "__5" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u128asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U128 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } (!{ RefOp } ( "self" ))) ×{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__3")) : expr); ("1", (copy{ IntOp U128 } (!{ RefOp } ( "self" ))) ×c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U128 } move{ IntOp U128 } (("__4") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asMulREFau128_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U128) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("self");
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) ×{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) ×c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U128) : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("self");
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) ×{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) ×c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asSubAssignREFu128_sub_assign_def (u128asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U128), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U128) } "__5";
      "__5" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u128asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U128 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } (!{ RefOp } ( "self" ))) -{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__3")) : expr); ("1", (copy{ IntOp U128 } (!{ RefOp } ( "self" ))) -c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U128 } move{ IntOp U128 } (("__4") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asSubREFau128_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U128) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("self");
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) -{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) -c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u128asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U128) : layout);
     ("other", (it_layout U128) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U128) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U128) } "__3";
      "__3" <-{ IntOp U128 } copy{ IntOp U128 } ("self");
      local_live{ (IntSynType U128) } "__4";
      "__4" <-{ IntOp U128 } copy{ IntOp U128 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U128)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U128)) BoolSynType) [("0", (copy{ IntOp U128 } ("__3")) -{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr); ("1", (copy{ IntOp U128 } ("__3")) -c{ IntOp U128 , IntOp U128 } (copy{ IntOp U128 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U128 } move{ IntOp U128 } (("__5") at{ (tuple2_sls ((IntSynType U128)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U128 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asAddAssignREFu16_add_assign_def (u16asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U16), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U16) } "__5";
      "__5" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u16asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U16 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } (!{ RefOp } ( "self" ))) +{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__3")) : expr); ("1", (copy{ IntOp U16 } (!{ RefOp } ( "self" ))) +c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U16 } move{ IntOp U16 } (("__4") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asAddREFau16_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U16) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("self");
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) +{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) +c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U16) : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("self");
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) +{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) +c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asMulAssignREFu16_mul_assign_def (u16asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U16), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U16) } "__5";
      "__5" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u16asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U16 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } (!{ RefOp } ( "self" ))) ×{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__3")) : expr); ("1", (copy{ IntOp U16 } (!{ RefOp } ( "self" ))) ×c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U16 } move{ IntOp U16 } (("__4") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asMulREFau16_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U16) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("self");
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) ×{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) ×c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U16) : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("self");
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) ×{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) ×c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asSubAssignREFu16_sub_assign_def (u16asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U16), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U16) } "__5";
      "__5" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u16asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U16 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } (!{ RefOp } ( "self" ))) -{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__3")) : expr); ("1", (copy{ IntOp U16 } (!{ RefOp } ( "self" ))) -c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U16 } move{ IntOp U16 } (("__4") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asSubREFau16_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U16) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("self");
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) -{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) -c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U16) : layout);
     ("other", (it_layout U16) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U16) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U16) } "__3";
      "__3" <-{ IntOp U16 } copy{ IntOp U16 } ("self");
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__3")) -{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr); ("1", (copy{ IntOp U16 } ("__3")) -c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U16 } move{ IntOp U16 } (("__5") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U16 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asAddAssignREFu32_add_assign_def (u32asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U32), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U32) } "__5";
      "__5" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u32asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U32 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } (!{ RefOp } ( "self" ))) +{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__3")) : expr); ("1", (copy{ IntOp U32 } (!{ RefOp } ( "self" ))) +c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U32 } move{ IntOp U32 } (("__4") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asAddREFau32_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U32) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("self");
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) +{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) +c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U32) : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("self");
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) +{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) +c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asMulAssignREFu32_mul_assign_def (u32asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U32), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U32) } "__5";
      "__5" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u32asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U32 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } (!{ RefOp } ( "self" ))) ×{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__3")) : expr); ("1", (copy{ IntOp U32 } (!{ RefOp } ( "self" ))) ×c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U32 } move{ IntOp U32 } (("__4") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asMulREFau32_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U32) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("self");
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) ×{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) ×c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U32) : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("self");
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) ×{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) ×c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asSubAssignREFu32_sub_assign_def (u32asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U32), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U32) } "__5";
      "__5" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u32asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U32 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } (!{ RefOp } ( "self" ))) -{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__3")) : expr); ("1", (copy{ IntOp U32 } (!{ RefOp } ( "self" ))) -c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U32 } move{ IntOp U32 } (("__4") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asSubREFau32_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U32) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("self");
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) -{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) -c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U32) : layout);
     ("other", (it_layout U32) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U32) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U32) } "__3";
      "__3" <-{ IntOp U32 } copy{ IntOp U32 } ("self");
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__3")) -{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr); ("1", (copy{ IntOp U32 } ("__3")) -c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U32 } move{ IntOp U32 } (("__5") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U32 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asAddAssignREFu64_add_assign_def (u64asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U64), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U64) } "__5";
      "__5" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u64asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U64 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } (!{ RefOp } ( "self" ))) +{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__3")) : expr); ("1", (copy{ IntOp U64 } (!{ RefOp } ( "self" ))) +c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U64 } move{ IntOp U64 } (("__4") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asAddREFau64_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U64) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("self");
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) +{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) +c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U64) : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("self");
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) +{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) +c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asMulAssignREFu64_mul_assign_def (u64asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U64), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U64) } "__5";
      "__5" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u64asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U64 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } (!{ RefOp } ( "self" ))) ×{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__3")) : expr); ("1", (copy{ IntOp U64 } (!{ RefOp } ( "self" ))) ×c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U64 } move{ IntOp U64 } (("__4") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asMulREFau64_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U64) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("self");
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) ×{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) ×c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U64) : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("self");
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) ×{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) ×c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asSubAssignREFu64_sub_assign_def (u64asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U64), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U64) } "__5";
      "__5" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u64asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U64 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } (!{ RefOp } ( "self" ))) -{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__3")) : expr); ("1", (copy{ IntOp U64 } (!{ RefOp } ( "self" ))) -c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U64 } move{ IntOp U64 } (("__4") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asSubREFau64_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U64) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("self");
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) -{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) -c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U64) : layout);
     ("other", (it_layout U64) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U64) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U64) } "__3";
      "__3" <-{ IntOp U64 } copy{ IntOp U64 } ("self");
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__3")) -{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr); ("1", (copy{ IntOp U64 } ("__3")) -c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U64 } move{ IntOp U64 } (("__5") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U64 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asAddAssignREFu8_add_assign_def (u8asAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U8), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U8) } "__5";
      "__5" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u8asAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U8 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } (!{ RefOp } ( "self" ))) +{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__3")) : expr); ("1", (copy{ IntOp U8 } (!{ RefOp } ( "self" ))) +c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U8 } move{ IntOp U8 } (("__4") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asAddREFau8_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U8) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("self");
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) +{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) +c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U8) : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("self");
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) +{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) +c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asMulAssignREFu8_mul_assign_def (u8asMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U8), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U8) } "__5";
      "__5" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u8asMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U8 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } (!{ RefOp } ( "self" ))) ×{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__3")) : expr); ("1", (copy{ IntOp U8 } (!{ RefOp } ( "self" ))) ×c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U8 } move{ IntOp U8 } (("__4") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asMulREFau8_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U8) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("self");
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) ×{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) ×c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U8) : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("self");
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) ×{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) ×c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asSubAssignREFu8_sub_assign_def (u8asSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt U8), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType U8) } "__5";
      "__5" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS u8asSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp U8 } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } (!{ RefOp } ( "self" ))) -{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__3")) : expr); ("1", (copy{ IntOp U8 } (!{ RefOp } ( "self" ))) -c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp U8 } move{ IntOp U8 } (("__4") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asSubREFau8_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U8) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("self");
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) -{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) -c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout U8) : layout);
     ("other", (it_layout U8) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType U8) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType U8) } "__3";
      "__3" <-{ IntOp U8 } copy{ IntOp U8 } ("self");
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__3")) -{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr); ("1", (copy{ IntOp U8 } ("__3")) -c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp U8 } move{ IntOp U8 } (("__5") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp U8 } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasAddAssignREFusize_add_assign_def (usizeasAddAssign_add_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt USize), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS usizeasAddAssign_add_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp USize } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasAddAssign_add_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } (!{ RefOp } ( "self" ))) +{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__3")) : expr); ("1", (copy{ IntOp USize } (!{ RefOp } ( "self" ))) +c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp USize } move{ IntOp USize } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasAddREFausize_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout USize) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) +{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) +c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasAdd_add_def  : function :=
  {|
     f_args := [
      ("self", (it_layout USize) : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) +{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) +c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasMulAssignREFusize_mul_assign_def (usizeasMulAssign_mul_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt USize), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS usizeasMulAssign_mul_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp USize } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasMulAssign_mul_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } (!{ RefOp } ( "self" ))) ×{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__3")) : expr); ("1", (copy{ IntOp USize } (!{ RefOp } ( "self" ))) ×c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp USize } move{ IntOp USize } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasMulREFausize_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout USize) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) ×{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) ×c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasMul_mul_def  : function :=
  {|
     f_args := [
      ("self", (it_layout USize) : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) ×{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) ×c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasSubAssignREFusize_sub_assign_def (usizeasSubAssign_sub_assign_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTInt USize), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft5"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS usizeasSubAssign_sub_assign_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__4"); move{ IntOp USize } ("__5")] (Some (Na1Ord, StructOp unit_sl [], "__3"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ StructOp unit_sl [] } zst_val;
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasSubAssign_sub_assign_def  : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } (!{ RefOp } ( "self" ))) -{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__3")) : expr); ("1", (copy{ IntOp USize } (!{ RefOp } ( "self" ))) -c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__3")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      !{ RefOp } ( "self" ) <-{ IntOp USize } move{ IntOp USize } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      "__0" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__3";
      return (move{ StructOp unit_sl [] } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasSubREFausize_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout USize) : layout);
     ("other", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_a"; (* initialization *)
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ RefOp } ( "other" ));
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) -{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) -c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasSub_sub_def  : function :=
  {|
     f_args := [
      ("self", (it_layout USize) : layout);
     ("other", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__5";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("other");
      "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__3")) -{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr); ("1", (copy{ IntOp USize } ("__3")) -c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__4")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      "__0" <-{ IntOp USize } move{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__4";
      local_dead "__3";
      return (move{ IntOp USize } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.