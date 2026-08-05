From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
Section Box_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Box_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let Box_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "Box" [
    ("0", ((unique_Unique_sls (T_st)) : syn_type));
    ("1", A_st)] StructReprRust.
  Definition Box_st (T_st: syn_type) (A_st: syn_type) : syn_type := Box_sls T_st A_st.
End Box_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition Box_TA_from_raw_in_def (unique_Unique_T_new_unchecked_T_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("raw", void* : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Box_st (T_st) (A_st)) } "__0";
      local_live{ ((unique_Unique_sls (T_st)) : syn_type) } "__3";
      local_live{ PtrSynType } "__4";
      "__4" <-{ PtrOp } copy{ PtrOp } ("raw");
      CallS unique_Unique_T_new_unchecked_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__4")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_live{ A_st } "__5";
      "__5" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      "__0" <-{ (use_op_alg' (Box_st (T_st) (A_st))) } StructInit (Box_sls (T_st) (A_st)) [("0", move{ (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)) } ("__3") : expr); ("1", move{ (use_op_alg' A_st) } ("__5") : expr)];
      local_dead "__5";
      local_dead "__3";
      return (move{ (use_op_alg' (Box_st (T_st) (A_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Box_T_from_raw_def (Box_TA_from_raw_in_T_std_alloc_Global_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("raw", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Box_st (T_st) ((Global_sls : syn_type))) } "__0";
      local_live{ PtrSynType } "__2";
      "__2" <-{ PtrOp } copy{ PtrOp } ("raw");
      local_live{ (Global_sls : syn_type) } "__3";
      "__3" <-{ (use_op_alg' (Global_sls : syn_type)) } StructInit Global_sls [];
      CallS Box_TA_from_raw_in_T_std_alloc_Global_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__2"); move{ (use_op_alg' (Global_sls : syn_type)) } ("__3")] (Some (Na1Ord, (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))), "__0"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      local_dead "__2";
      return (move{ (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Box_T_new_def (box_new_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("x", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Box_st (T_st) ((Global_sls : syn_type))) } "__0";
      local_live{ T_st } "__2";
      "__2" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("x");
      CallS box_new_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' T_st) } ("__2")] (Some (Na1Ord, (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))), "__0"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition box_new_def (alloc_alloc_loc: loc) (dangling_T_loc: loc) (layout_Layout_new_T_loc: loc) (mem_size_of_T_loc: loc) (mut_ptr_write_T_loc: loc) (unique_Unique_T_new_unchecked_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("x", (use_layout_alg' T_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Box_st (T_st) ((Global_sls : syn_type))) } "__0";
      local_live{ BoolSynType } "__27";
      "__27" <-{ BoolOp } val_of_bool false;
      "__27" <-{ BoolOp } val_of_bool true;
      local_live{ BoolSynType } "__2";
      local_live{ (IntSynType USize) } "__3";
      CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (IntOp USize), "__3"))
      ( Goto "_bb1")
      ( StuckS)
     ]>%E $
     <[
     "_bb1" :=
      "__2" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__2") then
       Goto "_bb2"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      local_live{ PtrSynType } "ptr";
      local_live{ PtrSynType } "__5";
      local_live{ PtrSynType } "__6";
      CallS dangling_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, PtrOp, "__6"))
      ( Goto "_bb3")
      ( StuckS)
     ]>%E $
     <[
     "_bb3" :=
      "__5" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__6"));
      "ptr" <-{ PtrOp } copy{ PtrOp } ("__5");
      local_dead "__6";
      local_dead "__5";
      local_live{ UnitSynType } "__7";
      local_live{ UnitSynType } "__8";
      local_live{ PtrSynType } "__9";
      "__9" <-{ PtrOp } copy{ PtrOp } ("ptr");
      local_live{ T_st } "__10";
      "__27" <-{ BoolOp } val_of_bool false;
      "__10" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("x");
      CallS mut_ptr_write_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__9"); move{ (use_op_alg' T_st) } ("__10")] (Some (Na1Ord, (StructOp unit_sl []), "__8"))
      ( Goto "_bb4")
      ( StuckS)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      "__7" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__7";
      local_live{ ((unique_Unique_sls (T_st)) : syn_type) } "__11";
      local_live{ PtrSynType } "__12";
      "__12" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS unique_Unique_T_new_unchecked_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__12")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)), "__11"))
      ( Goto "_bb5")
      ( StuckS)
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__12";
      local_live{ (Global_sls : syn_type) } "__13";
      "__13" <-{ (use_op_alg' (Global_sls : syn_type)) } StructInit Global_sls [];
      "__0" <-{ (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))) } StructInit (Box_sls (T_st) ((Global_sls : syn_type))) [("0", move{ (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)) } ("__11") : expr); ("1", move{ (use_op_alg' (Global_sls : syn_type)) } ("__13") : expr)];
      local_dead "__13";
      local_dead "__11";
      local_dead "ptr";
      Goto "_bb11"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__3";
      local_live{ (layout_Layout_sls : syn_type) } "layout";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "layout"))
      ( Goto "_bb7")
      ( StuckS)
     ]>%E $
     <[
     "_bb7" :=
      local_live{ PtrSynType } "__15";
      local_live{ (layout_Layout_sls : syn_type) } "__16";
      "__16" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      CallS alloc_alloc_loc [] [] [@{expr} move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__16")] (Some (Na1Ord, PtrOp, "__15"))
      ( Goto "_bb8")
      ( StuckS)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__16";
      local_live{ PtrSynType } "__17";
      local_live{ PtrSynType } "__18";
      local_live{ PtrSynType } "__19";
      "__19" <-{ PtrOp } copy{ PtrOp } ("__15");
      "__18" <-{ PtrOp } UnOp (CastOp (PtrOp)) (PtrOp) (move{ PtrOp } ("__19"));
      "__17" <-{ PtrOp } copy{ PtrOp } ("__18");
      local_dead "__19";
      local_dead "__18";
      local_live{ UnitSynType } "__20";
      local_live{ UnitSynType } "__21";
      local_live{ PtrSynType } "__22";
      "__22" <-{ PtrOp } copy{ PtrOp } ("__17");
      local_live{ T_st } "__23";
      "__27" <-{ BoolOp } val_of_bool false;
      "__23" <-{ (use_op_alg' T_st) } move{ (use_op_alg' T_st) } ("x");
      CallS mut_ptr_write_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__22"); move{ (use_op_alg' T_st) } ("__23")] (Some (Na1Ord, (StructOp unit_sl []), "__21"))
      ( Goto "_bb9")
      ( StuckS)
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__23";
      local_dead "__22";
      local_dead "__21";
      "__20" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__20";
      local_live{ ((unique_Unique_sls (T_st)) : syn_type) } "__24";
      local_live{ PtrSynType } "__25";
      "__25" <-{ PtrOp } copy{ PtrOp } ("__17");
      CallS unique_Unique_T_new_unchecked_T_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__25")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)), "__24"))
      ( Goto "_bb10")
      ( StuckS)
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__25";
      local_live{ (Global_sls : syn_type) } "__26";
      "__26" <-{ (use_op_alg' (Global_sls : syn_type)) } StructInit Global_sls [];
      "__0" <-{ (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))) } StructInit (Box_sls (T_st) ((Global_sls : syn_type))) [("0", move{ (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)) } ("__24") : expr); ("1", move{ (use_op_alg' (Global_sls : syn_type)) } ("__26") : expr)];
      local_dead "__26";
      local_dead "__24";
      local_dead "__17";
      local_dead "__15";
      local_dead "layout";
      Goto "_bb11"
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__2";
      return (move{ (use_op_alg' (Box_st (T_st) ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_Box_def (BoxTAasstd_ops_Drop_drop_T_A_loc: loc) (DropGlue_A_drop_glue_loc: loc) (DropGlue_T_drop_glue_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      local_live{ RefSynType } "__2";
      local_live{ UnitSynType } "__3";
      local_live{ RefSynType } "__4";
      local_live{ UnitSynType } "__5";
      local_live{ PtrSynType } "__6";
      "__6" <-{ PtrOp } UnOp (CastOp (RefOp)) (PtrOp) (copy{ PtrOp } ((((!{ RefOp } ( "ptr" )) at{ (Box_sls (T_st) (A_st)) } "0") at{ (unique_Unique_sls (T_st)) } "pointer") at{ (nonnull_NonNull_sls (T_st)) } "pointer"));
      CallS DropGlue_T_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } (!{ PtrOp } ( "__6" ))] None
      ( Goto "_bb5")
      ( StuckS)
     ]>%E $
     <[
     "_bb2" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (Box_sls (T_st) (A_st)) } "1")] None
      ( Goto "_bb2")
      ( StuckS)
     ]>%E $
     <[
     "_bb5" :=
      "__2" <-{ RefOp } copy{ RefOp } ("ptr");
      CallS BoxTAasstd_ops_Drop_drop_T_A_loc ["_flft"] [RSTTyVar "T"; RSTTyVar "A"] [@{expr} move{ RefOp } ("__2")] (Some (Na1Ord, (StructOp unit_sl []), "__3"))
      ( Goto "_bb4")
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