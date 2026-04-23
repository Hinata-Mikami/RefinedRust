From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.range.range.generated Require Export generated_specs_range.
From rrstd.result.result.generated Require Export generated_specs_result.
Section adapters_map_Map_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition adapters_map_Map_sls (I_st: syn_type) (F_st: syn_type) : struct_layout_spec :=
    let adapters_map_Map_st (I_st: syn_type) (F_st: syn_type) := UnitSynType in
    mk_sls "adapters_map_Map" [
    ("iter", I_st);
    ("f", F_st)] StructReprRust.
  Definition adapters_map_Map_st (I_st: syn_type) (F_st: syn_type) : syn_type := adapters_map_Map_sls I_st F_st.
End adapters_map_Map_sls.

Section adapters_skip_Skip_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition adapters_skip_Skip_sls (I_st: syn_type) : struct_layout_spec :=
    let adapters_skip_Skip_st (I_st: syn_type) := UnitSynType in
    mk_sls "adapters_skip_Skip" [
    ("iter", I_st);
    ("n", (IntSynType USize))] StructReprRust.
  Definition adapters_skip_Skip_st (I_st: syn_type) : syn_type := adapters_skip_Skip_sls I_st.
End adapters_skip_Skip_sls.

Section adapters_take_Take_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition adapters_take_Take_sls (I_st: syn_type) : struct_layout_spec :=
    let adapters_take_Take_st (I_st: syn_type) := UnitSynType in
    mk_sls "adapters_take_Take" [
    ("iter", I_st);
    ("n", (IntSynType USize))] StructReprRust.
  Definition adapters_take_Take_st (I_st: syn_type) : syn_type := adapters_take_Take_sls I_st.
End adapters_take_Take_sls.

Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition Iastraits_iterator_IntoIterator_into_iter_def (I_st: syn_type) (traits_iterator_Iterator_I_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' I_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ I_st } "__0";
      "__0" <-{ (use_op_alg' I_st) } move{ (use_op_alg' I_st) } ("self");
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      return (move{ (use_op_alg' I_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition adapters_map_MapMIMFastraits_iterator_Iterator_next_def (Option_T_map_MIastraits_iterator_Iterator_Item_MB_REFmutMF_loc: loc) (traits_iterator_Iterator_MI_next_loc: loc) (MB_st: syn_type) (MI_st: syn_type) (MF_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (MB_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type) } "__2";
      local_live{ PtrSynType } "__3";
      annot{ 1 }: StartLftAnnot "llft3" ["plft6"]; (* borrow *)
      "__3" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "MI"), "llft3" } ((!{ PtrOp } ( "self" )) at{ (adapters_map_Map_sls (MI_st) (MF_st)) } "iter");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft7"; (* function_call *)
      "__2" <-{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } CallE traits_iterator_Iterator_MI_next_loc ["vlft9"] [] [@{expr} move{ PtrOp } ("__3")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__3";
      local_live{ PtrSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft4" ["plft6"]; (* borrow *)
      "__4" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "MF"), "llft4" } ((!{ PtrOp } ( "self" )) at{ (adapters_map_Map_sls (MI_st) (MF_st)) } "f");
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft8"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (MB_st)) : syn_type)) } CallE Option_T_map_MIastraits_iterator_Iterator_Item_MB_REFmutMF_loc ["vlft5"] [RSTTyVar "MB"; RSTTyVar "MF"; RSTTyVar "traits_iterator_Iterator_MI_Item"] [@{expr} move{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } ("__2"); move{ PtrOp } ("__4")];
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      local_dead "__4";
      local_dead "__2";
      return (move{ (use_op_alg' ((Option_els (MB_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition adapters_map_Map_IF_new_def (I_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("iter", (use_layout_alg' I_st) : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (adapters_map_Map_st (I_st) (F_st)) } "__0";
      local_live{ I_st } "__3";
      "__3" <-{ (use_op_alg' I_st) } move{ (use_op_alg' I_st) } ("iter");
      local_live{ F_st } "__4";
      "__4" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("f");
      "__0" <-{ (use_op_alg' (adapters_map_Map_st (I_st) (F_st))) } StructInit (adapters_map_Map_sls (I_st) (F_st)) [("iter", move{ (use_op_alg' I_st) } ("__3") : expr); ("f", move{ (use_op_alg' F_st) } ("__4") : expr)];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      return (move{ (use_op_alg' (adapters_map_Map_st (I_st) (F_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition adapters_skip_SkipMIastraits_iterator_Iterator_next_def (traits_iterator_Iterator_MI_next_loc: loc) (traits_iterator_Iterator_MI_nth_loc: loc) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ BoolSynType } "__2";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ (adapters_skip_Skip_sls (MI_st)) } "n");
      "__2" <-{ BoolOp } (move{ IntOp USize } ("__3")) >{ IntOp USize , IntOp USize , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__2") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      local_live{ (IntSynType USize) } "n";
      "n" <-{ IntOp USize } copy{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ (adapters_skip_Skip_sls (MI_st)) } "n");
      (!{ PtrOp } ( "self" )) at{ (adapters_skip_Skip_sls (MI_st)) } "n" <-{ IntOp USize } i2v (0) USize;
      local_live{ PtrSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft3" ["plft5"]; (* borrow *)
      "__5" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "MI"), "llft3" } ((!{ PtrOp } ( "self" )) at{ (adapters_skip_Skip_sls (MI_st)) } "iter");
      annot{ 1 }: CopyLftNameAnnot "plft6" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ IntOp USize } copy{ IntOp USize } ("n");
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft6"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } CallE traits_iterator_Iterator_MI_nth_loc ["vlft8"] [] [@{expr} move{ PtrOp } ("__5"); move{ IntOp USize } ("__6")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__6";
      local_dead "__5";
      local_dead "n";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__3";
      local_live{ PtrSynType } "__7";
      annot{ 1 }: StartLftAnnot "llft4" ["plft5"]; (* borrow *)
      "__7" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "MI"), "llft4" } ((!{ PtrOp } ( "self" )) at{ (adapters_skip_Skip_sls (MI_st)) } "iter");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft7"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } CallE traits_iterator_Iterator_MI_next_loc ["vlft9"] [] [@{expr} move{ PtrOp } ("__7")];
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      local_dead "__7";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__2";
      return (move{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition adapters_skip_Skip_I_new_def (I_st: syn_type) : function :=
  {|
     f_args := [
      ("iter", (use_layout_alg' I_st) : layout);
     ("n", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (adapters_skip_Skip_st (I_st)) } "__0";
      local_live{ I_st } "__3";
      "__3" <-{ (use_op_alg' I_st) } move{ (use_op_alg' I_st) } ("iter");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("n");
      "__0" <-{ (use_op_alg' (adapters_skip_Skip_st (I_st))) } StructInit (adapters_skip_Skip_sls (I_st)) [("iter", move{ (use_op_alg' I_st) } ("__3") : expr); ("n", move{ IntOp USize } ("__4") : expr)];
      local_dead "__4";
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' (adapters_skip_Skip_st (I_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition adapters_take_TakeMIastraits_iterator_Iterator_next_def (traits_iterator_Iterator_MI_next_loc: loc) (MI_st: syn_type) (traits_iterator_Iterator_MI_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__4";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ BoolSynType } "__2";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ IntOp USize } copy{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ (adapters_take_Take_sls (MI_st)) } "n");
      "__2" <-{ BoolOp } (move{ IntOp USize } ("__3")) != { IntOp USize , IntOp USize , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__2") then
       Goto "_bb1"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ (adapters_take_Take_sls (MI_st)) } "n")) -{ IntOp USize , IntOp USize } (i2v (1) USize) : expr); ("1", (copy{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ (adapters_take_Take_sls (MI_st)) } "n")) -c{ IntOp USize , IntOp USize } (i2v (1) USize) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      (!{ PtrOp } ( "self" )) at{ (adapters_take_Take_sls (MI_st)) } "n" <-{ IntOp USize } move{ IntOp USize } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_live{ PtrSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__5" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "MI"), "llft3" } ((!{ PtrOp } ( "self" )) at{ (adapters_take_Take_sls (MI_st)) } "iter");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } CallE traits_iterator_Iterator_MI_next_loc ["vlft6"] [] [@{expr} move{ PtrOp } ("__5")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__5";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      "__0" <-{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } EnumInit (Option_els (traits_iterator_Iterator_MI_Item_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "traits_iterator_Iterator_MI_Item"] [])) (StructInit (Option_None_sls (traits_iterator_Iterator_MI_Item_st)) []);
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__2";
      return (move{ (use_op_alg' ((Option_els (traits_iterator_Iterator_MI_Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition adapters_take_Take_I_new_def (I_st: syn_type) : function :=
  {|
     f_args := [
      ("iter", (use_layout_alg' I_st) : layout);
     ("n", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (adapters_take_Take_st (I_st)) } "__0";
      local_live{ I_st } "__3";
      "__3" <-{ (use_op_alg' I_st) } move{ (use_op_alg' I_st) } ("iter");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("n");
      "__0" <-{ (use_op_alg' (adapters_take_Take_st (I_st))) } StructInit (adapters_take_Take_sls (I_st)) [("iter", move{ (use_op_alg' I_st) } ("__3") : expr); ("n", move{ IntOp USize } ("__4") : expr)];
      local_dead "__4";
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' (adapters_take_Take_st (I_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition step_impltraits_iterator_Iteratorforstd_ops_RangeA_next_def (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (A_st)) : syn_type) } "__0";
      local_live{ UnitSynType } "__2";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__3";
      StuckS
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_all_def (traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1401314019_std_ops_ControlFlowunit_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType ISize) } "__8";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type) } "__3";
      local_live{ PtrSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft7"]; (* borrow *)
      "__4" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft3" } (!{ PtrOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft3"; (* post-assignment *)
      local_live{ UnitSynType } "__5";
      "__5" <-{ StructOp unit_sl [] } zst_val;
      local_live{ ((tuple1_sls (PtrSynType)) : syn_type) } "__6";
      local_live{ PtrSynType } "__7";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__7" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft4" } ("f");
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft10"; (* composite *)
      "__6" <-{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } StructInit (tuple1_sls (PtrSynType)) [("0", move{ PtrOp } ("__7") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft5"; (* post-assignment *)
      local_dead "__7";
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft9"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft8"; (* function_call *)
      "__3" <-{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } CallE traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1401314019_std_ops_ControlFlowunit_loc ["vlft6"; "vlft11"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "Item"] [@{expr} move{ PtrOp } ("__4"); move{ StructOp unit_sl [] } ("__5"); move{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } ("__6")];
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      "__8" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (UnitSynType) (UnitSynType))) ("__3");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__8")) (<[ 0%Z := 0%nat ]> $ ∅) ([Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      "__0" <-{ BoolOp } val_of_bool true;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_all_closure0_def (FnMut_F_Selfastraits_iterator_Iterator_Item_call_mut_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", void* : layout);
     ("__2", (layout_of unit_sl) : layout);
     ("b", (use_layout_alg' traits_iterator_Iterator_Self_Item_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft1"; (* initialization *)
      local_live{ BoolSynType } "__4";
      local_live{ PtrSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft6" ["vlft7"; "plft8"]; (* borrow *)
      "__5" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft6" } (!{ PtrOp } ( (!{ PtrOp } ( "__1" )) at{ (tuple1_sls (PtrSynType)) } "0" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft7"; (* post-assignment *)
      local_live{ ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type) } "__6";
      local_live{ traits_iterator_Iterator_Self_Item_st } "__7";
      "__7" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("b");
      "__6" <-{ (use_op_alg' ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type)) } StructInit (tuple1_sls (traits_iterator_Iterator_Self_Item_st)) [("0", move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__7") : expr)];
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft10"; (* function_call *)
      "__4" <-{ BoolOp } CallE FnMut_F_Selfastraits_iterator_Iterator_Item_call_mut_loc ["vlft11"] [RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__5"); move{ (use_op_alg' ((tuple1_sls (traits_iterator_Iterator_Self_Item_st)) : syn_type)) } ("__6")];
      annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__4") then
       Goto "_bb2"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb2" :=
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_live{ UnitSynType } "__8";
      "__8" <-{ StructOp unit_sl [] } zst_val;
      "__0" <-{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } EnumInit (ControlFlow_els (UnitSynType) (UnitSynType)) "Continue" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTUnit; RSTUnit] [])) (StructInit (ControlFlow_Continue_sls (UnitSynType) (UnitSynType)) [("0", move{ StructOp unit_sl [] } ("__8") : expr)]);
      local_dead "__8";
      Goto "_bb7"
     ]>%E $
     <[
     "_bb4" :=
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_live{ UnitSynType } "__9";
      "__9" <-{ StructOp unit_sl [] } zst_val;
      "__0" <-{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } EnumInit (ControlFlow_els (UnitSynType) (UnitSynType)) "Break" (RSTEnumDef ["ControlFlow_enum"] (RSTScopeInst [] [RSTUnit; RSTUnit] [])) (StructInit (ControlFlow_Break_sls (UnitSynType) (UnitSynType)) [("0", move{ StructOp unit_sl [] } ("__9") : expr)]);
      local_dead "__9";
      Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__4";
      Goto "_bb8"
     ]>%E $
     <[
     "_bb8" :=
      return (move{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_collect_def (traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_from_iter_Self_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ B_st } "__0";
      local_live{ Self_st } "__2";
      "__2" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      "__0" <-{ (use_op_alg' B_st) } CallE traits_iterator_FromIterator_B_Selfastraits_iterator_Iterator_Item_from_iter_Self_loc [] [RSTTyVar "Self"; RSTTyVar "Self"] [@{expr} move{ (use_op_alg' Self_st) } ("__2")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' B_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_fold_def (FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc: loc) (traits_iterator_Iterator_Self_next_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("init", (use_layout_alg' B_st) : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ B_st } "__0";
      local_live{ UnitSynType } "__6";
      local_live{ (IntSynType ISize) } "__9";
      local_live{ UnitSynType } "__17";
      local_live{ UnitSynType } "__19";
      local_live{ B_st } "accum";
      "accum" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("init");
      local_live{ UnitSynType } "__5";
      annot{ 1 }: StratifyContextAnnot; (* goto to loop head *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__7";
      local_live{ PtrSynType } "__8";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__8" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft2" } ("self");
      annot{ 1 }: CopyLftNameAnnot "plft4" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft4"; (* function_call *)
      "__7" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_next_loc ["vlft6"] [] [@{expr} move{ PtrOp } ("__8")];
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      local_dead "__8";
      "__9" <-{ IntOp ISize } EnumDiscriminant ((Option_els (Item_st))) ("__7");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__9")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb4"]) (Goto "_bb12")
     ]>%E $
     <[
     "_bb4" :=
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_live{ Item_st } "x";
      "x" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ((EnumData ((Option_els (Item_st))) "Some" ("__7")) at{ (Option_Some_sls (Item_st)) } "0");
      local_live{ B_st } "__12";
      local_live{ PtrSynType } "__13";
      annot{ 1 }: StartLftAnnot "llft3" ["_flft"]; (* borrow *)
      "__13" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft3" } ("f");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ ((tuple2_sls (B_st) (Item_st)) : syn_type) } "__14";
      local_live{ B_st } "__15";
      "__15" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("accum");
      local_live{ Item_st } "__16";
      "__16" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ("x");
      "__14" <-{ (use_op_alg' ((tuple2_sls (B_st) (Item_st)) : syn_type)) } StructInit (tuple2_sls (B_st) (Item_st)) [("0", move{ (use_op_alg' B_st) } ("__15") : expr); ("1", move{ (use_op_alg' Item_st) } ("__16") : expr)];
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft5"; (* function_call *)
      "__12" <-{ (use_op_alg' B_st) } CallE FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc ["vlft7"] [RSTTyVar "B"; RSTTyVar "F"; RSTTyVar "B"; RSTTyVar "Item"; RSTTyVar "B"] [@{expr} move{ PtrOp } ("__13"); move{ (use_op_alg' ((tuple2_sls (B_st) (Item_st)) : syn_type)) } ("__14")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__16";
      Goto "_bb8"
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__15";
      local_dead "__14";
      local_dead "__13";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      "accum" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("__12");
      Goto "_bb11"
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__12";
      "__6" <-{ StructOp unit_sl [] } zst_val;
      Goto "_bb14"
     ]>%E $
     <[
     "_bb12" :=
      Goto "_bb13"
     ]>%E $
     <[
     "_bb13" :=
      local_dead "__7";
      local_live{ UnitSynType } "__18";
      "__5" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__18";
      local_dead "__5";
      "__0" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("accum");
      Goto "_bb16"
     ]>%E $
     <[
     "_bb14" :=
      local_dead "x";
      Goto "_bb15"
     ]>%E $
     <[
     "_bb15" :=
      local_dead "__7";
      annot{ 1 }: StratifyContextAnnot; (* goto to loop head *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb16" :=
      local_dead "accum";
      Goto "_bb17"
     ]>%E $
     <[
     "_bb17" :=
      Goto "_bb18"
     ]>%E $
     <[
     "_bb18" :=
      Goto "_bb19"
     ]>%E $
     <[
     "_bb19" :=
      return (move{ (use_op_alg' B_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_map_def (adapters_map_Map_IF_new_Self_F_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (adapters_map_Map_st (Self_st) (F_st)) } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ F_st } "__4";
      "__4" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("f");
      "__0" <-{ (use_op_alg' (adapters_map_Map_st (Self_st) (F_st))) } CallE adapters_map_Map_IF_new_Self_F_loc [] [RSTTyVar "Self"; RSTTyVar "F"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ (use_op_alg' F_st) } ("__4")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      return (move{ (use_op_alg' (adapters_map_Map_st (Self_st) (F_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_def (traits_iterator_Iterator_Self_max_by_closuresrctraitsiteratorrs2091320919_loc: loc) (Self_st: syn_type) (Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__0";
      local_live{ Self_st } "__2";
      "__2" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ UnitSynType } "__3";
      "__3" <-{ StructOp unit_sl [] } zst_val;
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_max_by_closuresrctraitsiteratorrs2091320919_loc [] [RSTTyVar "Self"; RSTTyVar "Item"] [@{expr} move{ (use_op_alg' Self_st) } ("__2"); move{ StructOp unit_sl [] } ("__3")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      local_dead "__2";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_by_def (traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2471324719_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("compare", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ ((tuple1_sls (PtrSynType)) : syn_type) } "__4";
      local_live{ PtrSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__5" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft2" } ("compare");
      annot{ 1 }: CopyLftNameAnnot "plft6" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft6"; (* composite *)
      "__4" <-{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } StructInit (tuple1_sls (PtrSynType)) [("0", move{ PtrOp } ("__5") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      local_dead "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft5"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs2471324719_loc ["vlft4"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "Item"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } ("__4")];
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      local_dead "__4";
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      return (move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_by_closure0_def (max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", void* : layout);
     ("a", (use_layout_alg' traits_iterator_Iterator_Self_Item_st) : layout);
     ("b", (use_layout_alg' traits_iterator_Iterator_Self_Item_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ traits_iterator_Iterator_Self_Item_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft1"; (* initialization *)
      local_live{ traits_iterator_Iterator_Self_Item_st } "__4";
      "__4" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("a");
      local_live{ traits_iterator_Iterator_Self_Item_st } "__5";
      "__5" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("b");
      local_live{ PtrSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft5" ["vlft6"; "plft8"]; (* borrow *)
      "__6" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft5" } (!{ PtrOp } ( (!{ PtrOp } ( "__1" )) at{ (tuple1_sls (PtrSynType)) } "0" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft10"; (* function_call *)
      "__0" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } CallE max_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc ["vlft7"] [RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__4"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__5"); move{ PtrOp } ("__6")];
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      return (move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_closure0_def (Ord_Selfastraits_iterator_Iterator_Item_cmp_loc: loc) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", void* : layout);
     ("a", void* : layout);
     ("b", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Ordering_els : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_2"; (* initialization *)
      local_live{ PtrSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft8"; (* composite *)
      "__4" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "traits_iterator_Iterator_Self_Item"), "vlft5" } (!{ PtrOp } ( "a" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "vlft5"; (* post-assignment *)
      local_live{ PtrSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft9"; (* composite *)
      "__5" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "traits_iterator_Iterator_Self_Item"), "vlft6" } (!{ PtrOp } ( "b" ));
      annot{ 1 }: CopyLftNameAnnot "plft11" "vlft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft10"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft11"; (* function_call *)
      "__0" <-{ (use_op_alg' (Ordering_els : syn_type)) } CallE Ord_Selfastraits_iterator_Iterator_Item_cmp_loc ["vlft12"; "vlft13"] [RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__4"); move{ PtrOp } ("__5")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      return (move{ (use_op_alg' (Ordering_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_def (traits_iterator_Iterator_Self_min_by_closuresrctraitsiteratorrs2651326519_loc: loc) (Self_st: syn_type) (Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__0";
      local_live{ Self_st } "__2";
      "__2" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ UnitSynType } "__3";
      "__3" <-{ StructOp unit_sl [] } zst_val;
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_min_by_closuresrctraitsiteratorrs2651326519_loc [] [RSTTyVar "Self"; RSTTyVar "Item"] [@{expr} move{ (use_op_alg' Self_st) } ("__2"); move{ StructOp unit_sl [] } ("__3")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      local_dead "__2";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_by_def (traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs3031330319_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("compare", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ ((tuple1_sls (PtrSynType)) : syn_type) } "__4";
      local_live{ PtrSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__5" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft2" } ("compare");
      annot{ 1 }: CopyLftNameAnnot "plft6" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft6"; (* composite *)
      "__4" <-{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } StructInit (tuple1_sls (PtrSynType)) [("0", move{ PtrOp } ("__5") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      local_dead "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft5"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_reduce_closuresrctraitsiteratorrs3031330319_loc ["vlft4"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "Item"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ (use_op_alg' ((tuple1_sls (PtrSynType)) : syn_type)) } ("__4")];
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      local_dead "__4";
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      return (move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_by_closure0_def (min_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", void* : layout);
     ("a", (use_layout_alg' traits_iterator_Iterator_Self_Item_st) : layout);
     ("b", (use_layout_alg' traits_iterator_Iterator_Self_Item_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ traits_iterator_Iterator_Self_Item_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft2"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft1"; (* initialization *)
      local_live{ traits_iterator_Iterator_Self_Item_st } "__4";
      "__4" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("a");
      local_live{ traits_iterator_Iterator_Self_Item_st } "__5";
      "__5" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("b");
      local_live{ PtrSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft5" ["vlft6"; "plft8"]; (* borrow *)
      "__6" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft5" } (!{ PtrOp } ( (!{ PtrOp } ( "__1" )) at{ (tuple1_sls (PtrSynType)) } "0" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "vlft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft10"; (* function_call *)
      "__0" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } CallE min_by_Selfastraits_iterator_Iterator_Item_REFmutF_loc ["vlft7"] [RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__4"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__5"); move{ PtrOp } ("__6")];
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      return (move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_closure0_def (Ord_Selfastraits_iterator_Iterator_Item_cmp_loc: loc) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", void* : layout);
     ("a", void* : layout);
     ("b", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Ordering_els : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft3"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft9" "ulft_2"; (* initialization *)
      local_live{ PtrSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft8"; (* composite *)
      "__4" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "traits_iterator_Iterator_Self_Item"), "vlft5" } (!{ PtrOp } ( "a" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "vlft5"; (* post-assignment *)
      local_live{ PtrSynType } "__5";
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft9"; (* composite *)
      "__5" <-{ PtrOp } &ref{ Shr, Some (RSTTyVar "traits_iterator_Iterator_Self_Item"), "vlft6" } (!{ PtrOp } ( "b" ));
      annot{ 1 }: CopyLftNameAnnot "plft11" "vlft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft10"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft11"; (* function_call *)
      "__0" <-{ (use_op_alg' (Ordering_els : syn_type)) } CallE Ord_Selfastraits_iterator_Iterator_Item_cmp_loc ["vlft12"; "vlft13"] [RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__4"); move{ PtrOp } ("__5")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      return (move{ (use_op_alg' (Ordering_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_nth_def (Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc: loc) (traits_iterator_Iterator_Self_next_loc: loc) (Self_st: syn_type) (Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("n", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__0";
      local_live{ UnitSynType } "__5";
      local_live{ UnitSynType } "__15";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__16";
      local_live{ UnitSynType } "__17";
      local_live{ UnitSynType } "__19";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "i";
      "i" <-{ IntOp USize } i2v (0) USize;
      local_live{ UnitSynType } "__4";
      annot{ 1 }: StratifyContextAnnot; (* goto to loop head *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ IntOp USize } copy{ IntOp USize } ("i");
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ IntOp USize } copy{ IntOp USize } ("n");
      "__6" <-{ BoolOp } (move{ IntOp USize } ("__7")) <{ IntOp USize , IntOp USize , U8 } (move{ IntOp USize } ("__8"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb3"
      else
       Goto "_bb11"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      local_live{ UnitSynType } "__10";
      local_live{ BoolSynType } "__11";
      local_live{ PtrSynType } "__12";
      local_live{ ((Option_els (Item_st)) : syn_type) } "__13";
      local_live{ PtrSynType } "__14";
      annot{ 1 }: StartLftAnnot "llft3" ["plft6"]; (* borrow *)
      "__14" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft3" } (!{ PtrOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft8"; (* function_call *)
      "__13" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_next_loc ["vlft10"] [] [@{expr} move{ PtrOp } ("__14")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__12" <-{ PtrOp } &ref{ Shr, Some (RSTLitType ["Option_ty"] (RSTScopeInst [] [RSTTyVar "Item"] [])), "llft4" } ("__13");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft4"; (* post-assignment *)
      local_dead "__14";
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft7"; (* function_call *)
      "__11" <-{ BoolOp } CallE Option_T_is_none_Selfastraits_iterator_Iterator_Item_loc ["vlft11"] [RSTTyVar "Item"] [@{expr} move{ PtrOp } ("__12")];
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: move{ BoolOp } ("__11") then
       Goto "_bb6"
      else
       Goto "_bb8"
     ]>%E $
     <[
     "_bb6" :=
      Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__13";
      local_dead "__12";
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } EnumInit (Option_els (Item_st)) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "Item"] [])) (StructInit (Option_None_sls (Item_st)) []);
      local_dead "__11";
      local_dead "__10";
      local_dead "__6";
      local_dead "__4";
      local_dead "i";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb8" :=
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__13";
      local_dead "__12";
      "__10" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__11";
      local_dead "__10";
      "__16" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("i")) +{ IntOp USize , IntOp USize } (i2v (1) USize) : expr); ("1", (copy{ IntOp USize } ("i")) +c{ IntOp USize , IntOp USize } (i2v (1) USize) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__16") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb10"
     ]>%E $
     <[
     "_bb10" :=
      "i" <-{ IntOp USize } move{ IntOp USize } (("__16") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      "__5" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__6";
      annot{ 1 }: StratifyContextAnnot; (* goto to loop head *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__8";
      local_dead "__7";
      local_live{ UnitSynType } "__18";
      "__4" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__18";
      local_dead "__6";
      local_dead "__4";
      local_live{ PtrSynType } "__20";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__20" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft5" } (!{ PtrOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft9"; (* function_call *)
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_next_loc ["vlft12"] [] [@{expr} move{ PtrOp } ("__20")];
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      Goto "_bb12"
     ]>%E $
     <[
     "_bb12" :=
      annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
      local_dead "__20";
      local_dead "i";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb13" :=
      return (move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_position_def (ControlFlow_BC_break_value_usize_unit_loc: loc) (traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1811318119_std_ops_ControlFlowusize_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft10" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "acc";
      "acc" <-{ IntOp USize } i2v (0) USize;
      local_live{ ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) } "clos";
      local_live{ PtrSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft3" ["_flft"]; (* borrow *)
      "__5" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft3" } ("f");
      annot{ 1 }: CopyLftNameAnnot "plft13" "llft3"; (* post-assignment *)
      local_live{ PtrSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__6" <-{ PtrOp } &ref{ Mut, Some (RSTInt USize), "llft4" } ("acc");
      annot{ 1 }: CopyLftNameAnnot "plft14" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft13"; (* composite *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft14"; (* composite *)
      "clos" <-{ (use_op_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) } StructInit (tuple2_sls (PtrSynType) (PtrSynType)) [("0", move{ PtrOp } ("__5") : expr); ("1", move{ PtrOp } ("__6") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft11" "vlft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "vlft6"; (* post-assignment *)
      local_dead "__6";
      local_dead "__5";
      local_live{ ((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type) } "__7";
      local_live{ PtrSynType } "__8";
      annot{ 1 }: StartLftAnnot "llft7" ["plft10"]; (* borrow *)
      "__8" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft7" } (!{ PtrOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft15" "llft7"; (* post-assignment *)
      local_live{ UnitSynType } "__9";
      "__9" <-{ StructOp unit_sl [] } zst_val;
      local_live{ ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type) } "__10";
      "__10" <-{ (use_op_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) } move{ (use_op_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) } ("clos");
      annot{ 1 }: CopyLftNameAnnot "plft16" "plft11"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft17" "plft12"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft11" "plft16"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "plft12" "plft17"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft16"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft17"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft18" "plft15"; (* function_call *)
      "__7" <-{ (use_op_alg' ((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) } CallE traits_iterator_Iterator_Self_try_fold_unit_closuresrctraitsiteratorrs1811318119_std_ops_ControlFlowusize_loc ["vlft8"; "vlft9"; "vlft18"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "Item"] [@{expr} move{ PtrOp } ("__8"); move{ StructOp unit_sl [] } ("__9"); move{ (use_op_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) } ("__10")];
      annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      "__0" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } CallE ControlFlow_BC_break_value_usize_unit_loc [] [] [@{expr} move{ (use_op_alg' ((ControlFlow_els ((IntSynType USize)) (UnitSynType)) : syn_type)) } ("__7")];
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_dead "clos";
      local_dead "acc";
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      return (move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_reduce_def (std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc: loc) (std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc: loc) (traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc: loc) (traits_iterator_Iterator_Self_next_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (F_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ UnitSynType } "__9";
      local_live{ Item_st } "first";
      local_live{ ((ControlFlow_els (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st)) : syn_type) } "__4";
      local_live{ ((Option_els (Item_st)) : syn_type) } "__5";
      local_live{ PtrSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__6" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft2" } ("self");
      annot{ 1 }: CopyLftNameAnnot "plft3" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft3"; (* function_call *)
      "__5" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_next_loc ["vlft4"] [] [@{expr} move{ PtrOp } ("__6")];
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
      local_dead "__6";
      "__4" <-{ (use_op_alg' ((ControlFlow_els (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st)) : syn_type)) } CallE std_option_OptionTasTry_branch_Selfastraits_iterator_Iterator_Item_loc [] [RSTTyVar "Item"] [@{expr} move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__5")];
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      "__7" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st))) ("__4");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__7")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb5"; Goto "_bb4"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb3" :=
      StuckS
     ]>%E $
     <[
     "_bb4" :=
      Goto "_bb6"
     ]>%E $
     <[
     "_bb5" :=
      local_live{ Item_st } "val";
      "val" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ((EnumData ((ControlFlow_els (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st))) "Continue" ("__4")) at{ (ControlFlow_Continue_sls (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st)) } "0");
      "first" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ("val");
      Goto "_bb8"
     ]>%E $
     <[
     "_bb6" :=
      local_live{ ((Option_els ((convert_Infallible_els : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) } copy{ (use_op_alg' ((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st))) "Break" ("__4")) at{ (ControlFlow_Break_sls (((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) (Item_st)) } "0");
      local_live{ ((Option_els ((convert_Infallible_els : syn_type))) : syn_type) } "__10";
      "__10" <-{ (use_op_alg' ((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) } copy{ (use_op_alg' ((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) } ("residual");
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE std_option_OptionTasFromResidual_from_residual_Selfastraits_iterator_Iterator_Item_loc [] [RSTTyVar "Item"] [@{expr} move{ (use_op_alg' ((Option_els ((convert_Infallible_els : syn_type))) : syn_type)) } ("__10")];
      Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__10";
      local_dead "residual";
      Goto "_bb14"
     ]>%E $
     <[
     "_bb8" :=
      local_dead "val";
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__4";
      local_live{ Item_st } "__12";
      local_live{ Self_st } "__13";
      "__13" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ Item_st } "__14";
      "__14" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ("first");
      local_live{ F_st } "__15";
      "__15" <-{ (use_op_alg' F_st) } move{ (use_op_alg' F_st) } ("f");
      "__12" <-{ (use_op_alg' Item_st) } CallE traits_iterator_Iterator_Self_fold_Selfastraits_iterator_Iterator_Item_F_loc [] [RSTTyVar "F"; RSTTyVar "Item"] [@{expr} move{ (use_op_alg' Self_st) } ("__13"); move{ (use_op_alg' Item_st) } ("__14"); move{ (use_op_alg' F_st) } ("__15")];
      Goto "_bb10"
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__15";
      local_dead "__14";
      local_dead "__13";
      "__0" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } EnumInit (Option_els (Item_st)) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTTyVar "Item"] [])) (StructInit (Option_Some_sls (Item_st)) [("0", move{ (use_op_alg' Item_st) } ("__12") : expr)]);
      Goto "_bb11"
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__12";
      Goto "_bb12"
     ]>%E $
     <[
     "_bb12" :=
      local_dead "first";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb13" :=
      Goto "_bb16"
     ]>%E $
     <[
     "_bb14" :=
      local_dead "__4";
      local_dead "first";
      Goto "_bb15"
     ]>%E $
     <[
     "_bb15" :=
      Goto "_bb16"
     ]>%E $
     <[
     "_bb16" :=
      return (move{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_skip_def (adapters_skip_Skip_I_new_Self_loc: loc) (Self_st: syn_type) (Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("n", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (adapters_skip_Skip_st (Self_st)) } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("n");
      "__0" <-{ (use_op_alg' (adapters_skip_Skip_st (Self_st))) } CallE adapters_skip_Skip_I_new_Self_loc [] [RSTTyVar "Self"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ IntOp USize } ("__4")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' (adapters_skip_Skip_st (Self_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_take_def (adapters_take_Take_I_new_Self_loc: loc) (Self_st: syn_type) (Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' Self_st) : layout);
     ("n", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (adapters_take_Take_st (Self_st)) } "__0";
      local_live{ Self_st } "__3";
      "__3" <-{ (use_op_alg' Self_st) } move{ (use_op_alg' Self_st) } ("self");
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } ("n");
      "__0" <-{ (use_op_alg' (adapters_take_Take_st (Self_st))) } CallE adapters_take_Take_I_new_Self_loc [] [RSTTyVar "Self"] [@{expr} move{ (use_op_alg' Self_st) } ("__3"); move{ IntOp USize } ("__4")];
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      return (move{ (use_op_alg' (adapters_take_Take_st (Self_st))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_try_fold_def (FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc: loc) (FromResidual_R_Rasstd_ops_Try_Residual_from_residual_loc: loc) (Try_R_branch_loc: loc) (Try_R_from_output_loc: loc) (traits_iterator_Iterator_Self_next_loc: loc) (Self_st: syn_type) (Item_st: syn_type) (B_st: syn_type) (F_st: syn_type) (R_st: syn_type) (Try_R_Residual_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("init", (use_layout_alg' B_st) : layout);
     ("f", (use_layout_alg' F_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ R_st } "__0";
      local_live{ UnitSynType } "__6";
      local_live{ (IntSynType ISize) } "__9";
      local_live{ (IntSynType ISize) } "__19";
      local_live{ UnitSynType } "__21";
      local_live{ UnitSynType } "__24";
      local_live{ UnitSynType } "__26";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ B_st } "accum";
      "accum" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("init");
      local_live{ UnitSynType } "__5";
      annot{ 1 }: StratifyContextAnnot; (* goto to loop head *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb1" :=
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      local_live{ ((Option_els (Item_st)) : syn_type) } "__7";
      local_live{ PtrSynType } "__8";
      annot{ 1 }: StartLftAnnot "llft3" ["plft5"]; (* borrow *)
      "__8" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "Self"), "llft3" } (!{ PtrOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft6" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft6"; (* function_call *)
      "__7" <-{ (use_op_alg' ((Option_els (Item_st)) : syn_type)) } CallE traits_iterator_Iterator_Self_next_loc ["vlft8"] [] [@{expr} move{ PtrOp } ("__8")];
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
      local_dead "__8";
      "__9" <-{ IntOp ISize } EnumDiscriminant ((Option_els (Item_st))) ("__7");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__9")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb4"]) (Goto "_bb20")
     ]>%E $
     <[
     "_bb4" :=
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_live{ Item_st } "x";
      "x" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ((EnumData ((Option_els (Item_st))) "Some" ("__7")) at{ (Option_Some_sls (Item_st)) } "0");
      local_live{ B_st } "__12";
      local_live{ ((ControlFlow_els (Try_R_Residual_st) (B_st)) : syn_type) } "__13";
      local_live{ R_st } "__14";
      local_live{ PtrSynType } "__15";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__15" <-{ PtrOp } &ref{ Mut, Some (RSTTyVar "F"), "llft4" } ("f");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft4"; (* post-assignment *)
      local_live{ ((tuple2_sls (B_st) (Item_st)) : syn_type) } "__16";
      local_live{ B_st } "__17";
      "__17" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("accum");
      local_live{ Item_st } "__18";
      "__18" <-{ (use_op_alg' Item_st) } move{ (use_op_alg' Item_st) } ("x");
      "__16" <-{ (use_op_alg' ((tuple2_sls (B_st) (Item_st)) : syn_type)) } StructInit (tuple2_sls (B_st) (Item_st)) [("0", move{ (use_op_alg' B_st) } ("__17") : expr); ("1", move{ (use_op_alg' Item_st) } ("__18") : expr)];
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft7"; (* function_call *)
      "__14" <-{ (use_op_alg' R_st) } CallE FnMut_F_BSelfastraits_iterator_Iterator_Item_call_mut_loc ["vlft9"] [RSTTyVar "B"; RSTTyVar "F"; RSTTyVar "R"; RSTTyVar "Item"; RSTTyVar "R"] [@{expr} move{ PtrOp } ("__15"); move{ (use_op_alg' ((tuple2_sls (B_st) (Item_st)) : syn_type)) } ("__16")];
      annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      Goto "_bb7"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__18";
      Goto "_bb8"
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__17";
      local_dead "__16";
      local_dead "__15";
      "__13" <-{ (use_op_alg' ((ControlFlow_els (Try_R_Residual_st) (B_st)) : syn_type)) } CallE Try_R_branch_loc [] [RSTTyVar "R"; RSTTyVar "Try_R_Residual"] [@{expr} move{ (use_op_alg' R_st) } ("__14")];
      Goto "_bb9"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__14";
      "__19" <-{ IntOp ISize } EnumDiscriminant ((ControlFlow_els (Try_R_Residual_st) (B_st))) ("__13");
      Switch (ISize: int_type) (move{ IntOp ISize } ("__19")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb12"; Goto "_bb11"]) (Goto "_bb10")
     ]>%E $
     <[
     "_bb10" :=
      StuckS
     ]>%E $
     <[
     "_bb11" :=
      Goto "_bb13"
     ]>%E $
     <[
     "_bb12" :=
      local_live{ B_st } "val";
      "val" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ((EnumData ((ControlFlow_els (Try_R_Residual_st) (B_st))) "Continue" ("__13")) at{ (ControlFlow_Continue_sls (Try_R_Residual_st) (B_st)) } "0");
      "__12" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("val");
      Goto "_bb15"
     ]>%E $
     <[
     "_bb13" :=
      local_live{ Try_R_Residual_st } "residual";
      "residual" <-{ (use_op_alg' Try_R_Residual_st) } move{ (use_op_alg' Try_R_Residual_st) } ((EnumData ((ControlFlow_els (Try_R_Residual_st) (B_st))) "Break" ("__13")) at{ (ControlFlow_Break_sls (Try_R_Residual_st) (B_st)) } "0");
      local_live{ Try_R_Residual_st } "__22";
      "__22" <-{ (use_op_alg' Try_R_Residual_st) } move{ (use_op_alg' Try_R_Residual_st) } ("residual");
      "__0" <-{ (use_op_alg' R_st) } CallE FromResidual_R_Rasstd_ops_Try_Residual_from_residual_loc [] [] [@{expr} move{ (use_op_alg' Try_R_Residual_st) } ("__22")];
      Goto "_bb14"
     ]>%E $
     <[
     "_bb14" :=
      local_dead "__22";
      Goto "_bb27"
     ]>%E $
     <[
     "_bb15" :=
      local_dead "val";
      Goto "_bb16"
     ]>%E $
     <[
     "_bb16" :=
      "accum" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("__12");
      Goto "_bb18"
     ]>%E $
     <[
     "_bb18" :=
      local_dead "__12";
      Goto "_bb19"
     ]>%E $
     <[
     "_bb19" :=
      local_dead "__13";
      "__6" <-{ StructOp unit_sl [] } zst_val;
      Goto "_bb22"
     ]>%E $
     <[
     "_bb20" :=
      Goto "_bb21"
     ]>%E $
     <[
     "_bb21" :=
      local_dead "__7";
      local_live{ UnitSynType } "__25";
      "__5" <-{ StructOp unit_sl [] } zst_val;
      local_dead "__25";
      local_dead "__5";
      local_live{ B_st } "__27";
      "__27" <-{ (use_op_alg' B_st) } move{ (use_op_alg' B_st) } ("accum");
      "__0" <-{ (use_op_alg' R_st) } CallE Try_R_from_output_loc [] [RSTTyVar "R"; RSTTyVar "Try_R_Residual"] [@{expr} move{ (use_op_alg' B_st) } ("__27")];
      Goto "_bb24"
     ]>%E $
     <[
     "_bb22" :=
      local_dead "x";
      Goto "_bb23"
     ]>%E $
     <[
     "_bb23" :=
      local_dead "__7";
      annot{ 1 }: StratifyContextAnnot; (* goto to loop head *)
      Goto "_bb1"
     ]>%E $
     <[
     "_bb24" :=
      local_dead "__27";
      Goto "_bb25"
     ]>%E $
     <[
     "_bb25" :=
      local_dead "accum";
      Goto "_bb26"
     ]>%E $
     <[
     "_bb26" :=
      Goto "_bb33"
     ]>%E $
     <[
     "_bb27" :=
      local_dead "residual";
      local_dead "__12";
      Goto "_bb28"
     ]>%E $
     <[
     "_bb28" :=
      local_dead "__13";
      Goto "_bb29"
     ]>%E $
     <[
     "_bb29" :=
      local_dead "x";
      Goto "_bb30"
     ]>%E $
     <[
     "_bb30" :=
      local_dead "__7";
      local_dead "__5";
      Goto "_bb31"
     ]>%E $
     <[
     "_bb31" :=
      local_dead "accum";
      Goto "_bb32"
     ]>%E $
     <[
     "_bb32" :=
      Goto "_bb33"
     ]>%E $
     <[
     "_bb33" :=
      return (move{ (use_op_alg' R_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u16asstep_Step_steps_between_def  : function :=
  {|
     f_args := [
      ("start", void* : layout);
     ("end", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type) } "__10";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U16) } "__4";
      "__4" <-{ IntOp U16 } copy{ IntOp U16 } (!{ PtrOp } ( "start" ));
      local_live{ (IntSynType U16) } "__5";
      "__5" <-{ IntOp U16 } copy{ IntOp U16 } (!{ PtrOp } ( "end" ));
      "__3" <-{ BoolOp } (move{ IntOp U16 } ("__4")) ≤{ IntOp U16 , IntOp U16 , U8 } (move{ IntOp U16 } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "steps";
      local_live{ (IntSynType U16) } "__7";
      local_live{ (IntSynType U16) } "__8";
      "__8" <-{ IntOp U16 } copy{ IntOp U16 } (!{ PtrOp } ( "end" ));
      local_live{ (IntSynType U16) } "__9";
      "__9" <-{ IntOp U16 } copy{ IntOp U16 } (!{ PtrOp } ( "start" ));
      "__10" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U16)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U16)) BoolSynType) [("0", (copy{ IntOp U16 } ("__8")) -{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__9")) : expr); ("1", (copy{ IntOp U16 } ("__8")) -c{ IntOp U16 , IntOp U16 } (copy{ IntOp U16 } ("__9")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__10") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      "__7" <-{ IntOp U16 } move{ IntOp U16 } (("__10") at{ (tuple2_sls ((IntSynType U16)) (BoolSynType)) } "0");
      local_dead "__9";
      local_dead "__8";
      "steps" <-{ IntOp USize } UnOp (CastOp (IntOp USize)) (IntOp U16) (move{ IntOp U16 } ("__7"));
      local_dead "__7";
      local_live{ (IntSynType USize) } "__11";
      "__11" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__12";
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      "__12" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_Some_sls ((IntSynType USize))) [("0", move{ IntOp USize } ("__13") : expr)]);
      local_dead "__13";
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", move{ IntOp USize } ("__11") : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__12") : expr)];
      local_dead "__12";
      local_dead "__11";
      local_dead "steps";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__14";
      "__14" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_None_sls ((IntSynType USize))) []);
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", i2v (0) USize : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__14") : expr)];
      local_dead "__14";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u32asstep_Step_steps_between_def  : function :=
  {|
     f_args := [
      ("start", void* : layout);
     ("end", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type) } "__10";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U32) } "__4";
      "__4" <-{ IntOp U32 } copy{ IntOp U32 } (!{ PtrOp } ( "start" ));
      local_live{ (IntSynType U32) } "__5";
      "__5" <-{ IntOp U32 } copy{ IntOp U32 } (!{ PtrOp } ( "end" ));
      "__3" <-{ BoolOp } (move{ IntOp U32 } ("__4")) ≤{ IntOp U32 , IntOp U32 , U8 } (move{ IntOp U32 } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "steps";
      local_live{ (IntSynType U32) } "__7";
      local_live{ (IntSynType U32) } "__8";
      "__8" <-{ IntOp U32 } copy{ IntOp U32 } (!{ PtrOp } ( "end" ));
      local_live{ (IntSynType U32) } "__9";
      "__9" <-{ IntOp U32 } copy{ IntOp U32 } (!{ PtrOp } ( "start" ));
      "__10" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U32)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U32)) BoolSynType) [("0", (copy{ IntOp U32 } ("__8")) -{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__9")) : expr); ("1", (copy{ IntOp U32 } ("__8")) -c{ IntOp U32 , IntOp U32 } (copy{ IntOp U32 } ("__9")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__10") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      "__7" <-{ IntOp U32 } move{ IntOp U32 } (("__10") at{ (tuple2_sls ((IntSynType U32)) (BoolSynType)) } "0");
      local_dead "__9";
      local_dead "__8";
      "steps" <-{ IntOp USize } UnOp (CastOp (IntOp USize)) (IntOp U32) (move{ IntOp U32 } ("__7"));
      local_dead "__7";
      local_live{ (IntSynType USize) } "__11";
      "__11" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__12";
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      "__12" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_Some_sls ((IntSynType USize))) [("0", move{ IntOp USize } ("__13") : expr)]);
      local_dead "__13";
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", move{ IntOp USize } ("__11") : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__12") : expr)];
      local_dead "__12";
      local_dead "__11";
      local_dead "steps";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__14";
      "__14" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_None_sls ((IntSynType USize))) []);
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", i2v (0) USize : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__14") : expr)];
      local_dead "__14";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u64asstep_Step_steps_between_def  : function :=
  {|
     f_args := [
      ("start", void* : layout);
     ("end", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type) } "__10";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U64) } "__4";
      "__4" <-{ IntOp U64 } copy{ IntOp U64 } (!{ PtrOp } ( "start" ));
      local_live{ (IntSynType U64) } "__5";
      "__5" <-{ IntOp U64 } copy{ IntOp U64 } (!{ PtrOp } ( "end" ));
      "__3" <-{ BoolOp } (move{ IntOp U64 } ("__4")) ≤{ IntOp U64 , IntOp U64 , U8 } (move{ IntOp U64 } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "steps";
      local_live{ (IntSynType U64) } "__7";
      local_live{ (IntSynType U64) } "__8";
      "__8" <-{ IntOp U64 } copy{ IntOp U64 } (!{ PtrOp } ( "end" ));
      local_live{ (IntSynType U64) } "__9";
      "__9" <-{ IntOp U64 } copy{ IntOp U64 } (!{ PtrOp } ( "start" ));
      "__10" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (copy{ IntOp U64 } ("__8")) -{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__9")) : expr); ("1", (copy{ IntOp U64 } ("__8")) -c{ IntOp U64 , IntOp U64 } (copy{ IntOp U64 } ("__9")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__10") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      "__7" <-{ IntOp U64 } move{ IntOp U64 } (("__10") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
      local_dead "__9";
      local_dead "__8";
      "steps" <-{ IntOp USize } UnOp (CastOp (IntOp USize)) (IntOp U64) (move{ IntOp U64 } ("__7"));
      local_dead "__7";
      local_live{ (IntSynType USize) } "__11";
      "__11" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__12";
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      "__12" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_Some_sls ((IntSynType USize))) [("0", move{ IntOp USize } ("__13") : expr)]);
      local_dead "__13";
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", move{ IntOp USize } ("__11") : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__12") : expr)];
      local_dead "__12";
      local_dead "__11";
      local_dead "steps";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__14";
      "__14" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_None_sls ((IntSynType USize))) []);
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", i2v (0) USize : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__14") : expr)];
      local_dead "__14";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition u8asstep_Step_steps_between_def  : function :=
  {|
     f_args := [
      ("start", void* : layout);
     ("end", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type) } "__0";
      local_live{ ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type) } "__10";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType U8) } "__4";
      "__4" <-{ IntOp U8 } copy{ IntOp U8 } (!{ PtrOp } ( "start" ));
      local_live{ (IntSynType U8) } "__5";
      "__5" <-{ IntOp U8 } copy{ IntOp U8 } (!{ PtrOp } ( "end" ));
      "__3" <-{ BoolOp } (move{ IntOp U8 } ("__4")) ≤{ IntOp U8 , IntOp U8 , U8 } (move{ IntOp U8 } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "steps";
      local_live{ (IntSynType U8) } "__7";
      local_live{ (IntSynType U8) } "__8";
      "__8" <-{ IntOp U8 } copy{ IntOp U8 } (!{ PtrOp } ( "end" ));
      local_live{ (IntSynType U8) } "__9";
      "__9" <-{ IntOp U8 } copy{ IntOp U8 } (!{ PtrOp } ( "start" ));
      "__10" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U8)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U8)) BoolSynType) [("0", (copy{ IntOp U8 } ("__8")) -{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__9")) : expr); ("1", (copy{ IntOp U8 } ("__8")) -c{ IntOp U8 , IntOp U8 } (copy{ IntOp U8 } ("__9")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__10") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      "__7" <-{ IntOp U8 } move{ IntOp U8 } (("__10") at{ (tuple2_sls ((IntSynType U8)) (BoolSynType)) } "0");
      local_dead "__9";
      local_dead "__8";
      "steps" <-{ IntOp USize } UnOp (CastOp (IntOp USize)) (IntOp U8) (move{ IntOp U8 } ("__7"));
      local_dead "__7";
      local_live{ (IntSynType USize) } "__11";
      "__11" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__12";
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      "__12" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_Some_sls ((IntSynType USize))) [("0", move{ IntOp USize } ("__13") : expr)]);
      local_dead "__13";
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", move{ IntOp USize } ("__11") : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__12") : expr)];
      local_dead "__12";
      local_dead "__11";
      local_dead "steps";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__14";
      "__14" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_None_sls ((IntSynType USize))) []);
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", i2v (0) USize : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__14") : expr)];
      local_dead "__14";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition usizeasstep_Step_steps_between_def  : function :=
  {|
     f_args := [
      ("start", void* : layout);
     ("end", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__9";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_2"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ IntOp USize } copy{ IntOp USize } (!{ PtrOp } ( "start" ));
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ IntOp USize } copy{ IntOp USize } (!{ PtrOp } ( "end" ));
      "__3" <-{ BoolOp } (move{ IntOp USize } ("__4")) ≤{ IntOp USize , IntOp USize , U8 } (move{ IntOp USize } ("__5"));
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ (IntSynType USize) } "steps";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ IntOp USize } copy{ IntOp USize } (!{ PtrOp } ( "end" ));
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ IntOp USize } copy{ IntOp USize } (!{ PtrOp } ( "start" ));
      "__9" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ IntOp USize } ("__7")) -{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__8")) : expr); ("1", (copy{ IntOp USize } ("__7")) -c{ IntOp USize , IntOp USize } (copy{ IntOp USize } ("__8")) : expr)];
      assert{ BoolOp }: (move{ BoolOp } (("__9") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
      Goto "_bb2"
     ]>%E $
     <[
     "_bb2" :=
      "steps" <-{ IntOp USize } move{ IntOp USize } (("__9") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__8";
      local_dead "__7";
      local_live{ (IntSynType USize) } "__10";
      "__10" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__11";
      local_live{ (IntSynType USize) } "__12";
      "__12" <-{ IntOp USize } copy{ IntOp USize } ("steps");
      "__11" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_Some_sls ((IntSynType USize))) [("0", move{ IntOp USize } ("__12") : expr)]);
      local_dead "__12";
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", move{ IntOp USize } ("__10") : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__11") : expr)];
      local_dead "__11";
      local_dead "__10";
      local_dead "steps";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__13";
      "__13" <-{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } EnumInit (Option_els ((IntSynType USize))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTInt USize] [])) (StructInit (Option_None_sls ((IntSynType USize))) []);
      "__0" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) [("0", i2v (0) USize : expr); ("1", move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__13") : expr)];
      local_dead "__13";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (((Option_els ((IntSynType USize))) : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
Program Definition traits_iterator_Iterator_all_closure0_call_once_code (traits_iterator_Iterator_all_closure0_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((tuple1_sls (PtrSynType)) : syn_type)) : layout);
     ("args", (use_layout_alg' ((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type) } "__0";
      local_live{ PtrSynType } "__1";
      annot{ 1 }: StartLftAnnot "_mk_ref_lft" ["_flft"];
      "__1" <-{ PtrOp } &ref{ Mut, None, "_mk_ref_lft" } ("self");
      "__0" <-{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } CallE traits_iterator_Iterator_all_closure0_loc ["ulft1"; "_mk_ref_lft"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ StructOp unit_sl [] } (("args") at{ (tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) } "0"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) } "1")];
      annot{ 2 }: EndLftAnnot "_mk_ref_lft";
      return (move{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_all_closure0_call_mut_code (traits_iterator_Iterator_all_closure0_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("args", (use_layout_alg' ((tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type) } "__0";
      local_live{ PtrSynType } "__1";
      "__1" <-{ PtrOp } move{ PtrOp } ("self");
      "__0" <-{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } CallE traits_iterator_Iterator_all_closure0_loc ["ulft1"; "_ref_lft"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ StructOp unit_sl [] } (("args") at{ (tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) } "0"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (UnitSynType) (traits_iterator_Iterator_Self_Item_st)) } "1")];
      return (move{ (use_op_alg' ((ControlFlow_els (UnitSynType) (UnitSynType)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_closure0_call_once_code (traits_iterator_Iterator_max_closure0_loc: loc) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (layout_of unit_sl) : layout);
     ("args", (use_layout_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Ordering_els : syn_type) } "__0";
      local_live{ PtrSynType } "__1";
      annot{ 1 }: StartLftAnnot "_mk_ref_lft" ["_flft"];
      "__1" <-{ PtrOp } &ref{ Mut, None, "_mk_ref_lft" } ("self");
      "__0" <-{ (use_op_alg' (Ordering_els : syn_type)) } CallE traits_iterator_Iterator_max_closure0_loc ["ulft_1"; "ulft_2"; "_mk_ref_lft"] [RSTTyVar "Self"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "0"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "1")];
      annot{ 2 }: EndLftAnnot "_mk_ref_lft";
      return (move{ (use_op_alg' (Ordering_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_closure0_call_mut_code (traits_iterator_Iterator_max_closure0_loc: loc) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("args", (use_layout_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Ordering_els : syn_type) } "__0";
      local_live{ PtrSynType } "__1";
      "__1" <-{ PtrOp } move{ PtrOp } ("self");
      "__0" <-{ (use_op_alg' (Ordering_els : syn_type)) } CallE traits_iterator_Iterator_max_closure0_loc ["ulft_1"; "ulft_2"; "_ref_lft"] [RSTTyVar "Self"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "0"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "1")];
      return (move{ (use_op_alg' (Ordering_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_by_closure0_call_once_code (traits_iterator_Iterator_max_by_closure0_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((tuple1_sls (PtrSynType)) : syn_type)) : layout);
     ("args", (use_layout_alg' ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ traits_iterator_Iterator_Self_Item_st } "__0";
      local_live{ PtrSynType } "__1";
      annot{ 1 }: StartLftAnnot "_mk_ref_lft" ["_flft"];
      "__1" <-{ PtrOp } &ref{ Mut, None, "_mk_ref_lft" } ("self");
      "__0" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } CallE traits_iterator_Iterator_max_by_closure0_loc ["ulft1"; "_mk_ref_lft"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "0"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "1")];
      annot{ 2 }: EndLftAnnot "_mk_ref_lft";
      return (move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_max_by_closure0_call_mut_code (traits_iterator_Iterator_max_by_closure0_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("args", (use_layout_alg' ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ traits_iterator_Iterator_Self_Item_st } "__0";
      local_live{ PtrSynType } "__1";
      "__1" <-{ PtrOp } move{ PtrOp } ("self");
      "__0" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } CallE traits_iterator_Iterator_max_by_closure0_loc ["ulft1"; "_ref_lft"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "0"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "1")];
      return (move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_closure0_call_once_code (traits_iterator_Iterator_min_closure0_loc: loc) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (layout_of unit_sl) : layout);
     ("args", (use_layout_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Ordering_els : syn_type) } "__0";
      local_live{ PtrSynType } "__1";
      annot{ 1 }: StartLftAnnot "_mk_ref_lft" ["_flft"];
      "__1" <-{ PtrOp } &ref{ Mut, None, "_mk_ref_lft" } ("self");
      "__0" <-{ (use_op_alg' (Ordering_els : syn_type)) } CallE traits_iterator_Iterator_min_closure0_loc ["ulft_1"; "ulft_2"; "_mk_ref_lft"] [RSTTyVar "Self"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "0"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "1")];
      annot{ 2 }: EndLftAnnot "_mk_ref_lft";
      return (move{ (use_op_alg' (Ordering_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_closure0_call_mut_code (traits_iterator_Iterator_min_closure0_loc: loc) (Self_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("args", (use_layout_alg' ((tuple2_sls (PtrSynType) (PtrSynType)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (Ordering_els : syn_type) } "__0";
      local_live{ PtrSynType } "__1";
      "__1" <-{ PtrOp } move{ PtrOp } ("self");
      "__0" <-{ (use_op_alg' (Ordering_els : syn_type)) } CallE traits_iterator_Iterator_min_closure0_loc ["ulft_1"; "ulft_2"; "_ref_lft"] [RSTTyVar "Self"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "0"); move{ PtrOp } (("args") at{ (tuple2_sls (PtrSynType) (PtrSynType)) } "1")];
      return (move{ (use_op_alg' (Ordering_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_by_closure0_call_once_code (traits_iterator_Iterator_min_by_closure0_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((tuple1_sls (PtrSynType)) : syn_type)) : layout);
     ("args", (use_layout_alg' ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ traits_iterator_Iterator_Self_Item_st } "__0";
      local_live{ PtrSynType } "__1";
      annot{ 1 }: StartLftAnnot "_mk_ref_lft" ["_flft"];
      "__1" <-{ PtrOp } &ref{ Mut, None, "_mk_ref_lft" } ("self");
      "__0" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } CallE traits_iterator_Iterator_min_by_closure0_loc ["ulft1"; "_mk_ref_lft"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "0"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "1")];
      annot{ 2 }: EndLftAnnot "_mk_ref_lft";
      return (move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition traits_iterator_Iterator_min_by_closure0_call_mut_code (traits_iterator_Iterator_min_by_closure0_loc: loc) (Self_st: syn_type) (F_st: syn_type) (traits_iterator_Iterator_Self_Item_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("args", (use_layout_alg' ((tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ traits_iterator_Iterator_Self_Item_st } "__0";
      local_live{ PtrSynType } "__1";
      "__1" <-{ PtrOp } move{ PtrOp } ("self");
      "__0" <-{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } CallE traits_iterator_Iterator_min_by_closure0_loc ["ulft1"; "_ref_lft"] [RSTTyVar "Self"; RSTTyVar "F"; RSTTyVar "traits_iterator_Iterator_Self_Item"] [@{expr} move{ PtrOp } ("__1"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "0"); move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } (("args") at{ (tuple2_sls (traits_iterator_Iterator_Self_Item_st) (traits_iterator_Iterator_Self_Item_st)) } "1")];
      return (move{ (use_op_alg' traits_iterator_Iterator_Self_Item_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.




End code.