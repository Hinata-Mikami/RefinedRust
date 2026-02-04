From caesium Require Import lang notation.
From refinedrust Require Import typing.

Program Definition box_new `{!LayoutAlg} (ptr_dangling_T_loc : loc) (mem_size_of_T_loc : loc) (T_st : syn_type) : function := {|
 f_args := [("x", use_layout_alg' T_st)];
 f_code :=
  <["_bb0" :=
    local_live{IntSynType usize} "size";
   (* check if the size is 0 *)
   "size" <-{IntOp USize} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
   if{BoolOp}: copy{IntOp USize} "size" = {IntOp USize, IntOp USize, U8} i2v 0 USize
   then Goto "_bb1"
   else Goto "_bb2"
  ]>%E $
  <["_bb2" :=
   local_live{PtrSynType} "__0";
   (* non-ZST, do an actual allocation *)
   (* TODO maybe call alloc_alloc here? *)
   "__0" <-{ PtrOp } box{ T_st };
   !{ PtrOp } "__0" <-{ use_op_alg' T_st } (move{use_op_alg' T_st} "x");
   return (move{ PtrOp } ("__0"))
  ]>%E $
  <["_bb1" :=
    local_live{PtrSynType} "__0";
    (* ZST, use a dangling pointer *)
    "__0" <-{PtrOp} CallE ptr_dangling_T_loc [] [RSTTyVar "T"] [@{expr} ];
    annot: StopAnnot;
    (* do a zero-sized write - this is fine *)
    !{ PtrOp } "__0" <-{ use_op_alg' T_st } (move{use_op_alg' T_st} "x");
    return (move{PtrOp} "__0")
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.
