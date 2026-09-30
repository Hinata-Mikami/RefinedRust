From radium Require Import lang notation.
From refinedrust Require Import typing shims.
Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition REFmutFasFnOnceA_call_once_def (FnMut_F_A_call_mut_loc: loc) (A_st: syn_type) (F_st: syn_type) (FnOnce_F_A_Output_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("args", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ FnOnce_F_A_Output_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__3" <-{ RefOp } &ref{ Mut, Some (RSTTyVar "F"), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ A_st } "__4";
      "__4" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("args");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS FnMut_F_A_call_mut_loc ["vlft6"] [RSTTyVar "A"; RSTTyVar "F"; RSTTyVar "FnOnce_F_A_Output"; RSTTyVar "FnOnce_F_A_Output"] [@{expr} move{ RefOp } ("__3"); move{ (use_op_alg' A_st) } ("__4")] (Some (Na1Ord, (use_op_alg' FnOnce_F_A_Output_st), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' FnOnce_F_A_Output_st) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.