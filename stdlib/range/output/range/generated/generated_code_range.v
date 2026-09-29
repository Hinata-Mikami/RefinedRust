From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.option.option.generated Require Export generated_specs_option.
Section Range_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Range_sls (Idx_st: syn_type) : struct_layout_spec :=
    let Range_st (Idx_st: syn_type) := UnitSynType in
    mk_sls "Range" [
    ("start", Idx_st);
    ("end", Idx_st)] StructReprRust.
  Definition Range_st (Idx_st: syn_type) : syn_type := Range_sls Idx_st.
End Range_sls.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition Range_Idx_is_empty_def (PartialOrd_Idx_Idx_lt_loc: loc) (Idx_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ BoolSynType } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft5"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Idx"), "vlft3" } ((!{ RefOp } ( "self" )) at{ (Range_sls (Idx_st)) } "start");
      annot{ 1 }: CopyLftNameAnnot "plft6" "vlft3"; (* post-assignment *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft5"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "Idx"), "vlft4" } ((!{ RefOp } ( "self" )) at{ (Range_sls (Idx_st)) } "end");
      annot{ 1 }: CopyLftNameAnnot "plft7" "vlft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft6"; (* function_call *)
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft7"; (* function_call *)
      CallS PartialOrd_Idx_Idx_lt_loc ["vlft8"; "vlft9"] [RSTTyVar "Idx"] [@{expr} move{ RefOp } ("__3"); move{ RefOp } ("__4")] (Some (Na1Ord, BoolOp, "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      "__0" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (move{ BoolOp } ("__2"));
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_Range_def (DropGlue_Idx_drop_glue_loc: loc) (Idx_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_Idx_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (Range_sls (Idx_st)) } "start")] None
      ( Goto "_bb4")
      ( Goto "_bb3")
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
     <[
     "_bb3" :=
      CallS DropGlue_Idx_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (Range_sls (Idx_st)) } "end")] None
      ( Goto "_bb2")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_Idx_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (Range_sls (Idx_st)) } "end")] None
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.