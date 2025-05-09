From caesium Require Import lang notation.
From refinedrust Require Import typing.

Definition box_new `{!LayoutAlg} (T_st : syn_type) (mem_size_of_T_loc : loc) (ptr_dangling_T_loc : loc) : function := {|
 f_args := [("x", use_layout_alg' T_st)];
 f_local_vars := [
   ("__0", void* : layout);
   ("size", USize : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* check if the size is 0 *)
   "size" <-{IntOp USize} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
   if{BoolOp}: use{IntOp USize} "size" = {IntOp USize, IntOp USize, U8} i2v 0 USize
   then Goto "_bb1"
   else Goto "_bb2"
  ]>%E $
  <["_bb2" :=
   (* non-ZST, do an actual allocation *)
   (* TODO maybe call alloc_alloc here? *)
   "__0" <-{ PtrOp } box{ T_st };
   !{ PtrOp } "__0" <-{ use_op_alg' T_st } (use{use_op_alg' T_st} "x");
   return (use{ PtrOp } ("__0"))
  ]>%E $
  <["_bb1" :=
    (* ZST, use a dangling pointer *)
    "__0" <-{PtrOp} CallE ptr_dangling_T_loc [] [RSTTyVar "T"] [@{expr} ];
    annot: StopAnnot;
    (* do a zero-sized write - this is fine *)
    !{ PtrOp } "__0" <-{ use_op_alg' T_st } (use{use_op_alg' T_st} "x");
    return (use{PtrOp} "__0")
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.
