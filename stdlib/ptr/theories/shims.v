From caesium Require Import lang notation.
From refinedrust Require Import annotations.

Definition ptr_write `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("dst", void* ); ("src", use_layout_alg' T_st)];
  f_local_vars := [("_0", use_layout_alg' UnitSynType); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
      (* NOTE: the rust impl uses copy_nonoverlapping and then asserts with an intrinsic that the validity invariant for T holds,
          but we don't have such a thing and should simply use a typed copy *)
      !{PtrOp} "dst" <-{use_op_alg' T_st} use{use_op_alg' T_st} "src";
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.


Definition ptr_read `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* )];
  f_local_vars := [("tmp", use_layout_alg' T_st); ("_0", use_layout_alg' UnitSynType); ("_1", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
      "tmp" <-{use_op_alg' T_st} use{use_op_alg' T_st} (!{PtrOp} "src");
      return (use{use_op_alg' T_st} "tmp")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

(* Our implementation does not actually do anything with the type parameter, it's just there to mirror the Rust API. *)
Definition ptr_invalid `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("align", USize : layout)];
  f_local_vars := [("ret", use_layout_alg' PtrSynType); ("_0", use_layout_alg' UnitSynType); ("_1", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
      "ret" <-{PtrOp} (UnOp (CastOp PtrOp) (IntOp USize) (UnOp EraseProv (UntypedOp USize) (use{IntOp USize} "align")));
      return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition ptr_dangling `{!LayoutAlg} (T_st : syn_type) (mem_align_of_loc : loc) (ptr_invalid_loc : loc) : function := {|
  f_args := [];
  f_local_vars := [("align", USize : layout)];
  f_code :=
    <["_bb0" :=
      "align" <-{IntOp USize} CallE mem_align_of_loc [] [RSTTyVar "T"] [@{expr} ];
      return (CallE ptr_invalid_loc [] [RSTTyVar "T"] [@{expr} use{IntOp USize} "align"])
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.


(** copy_nonoverlapping *)
(*
  This just does a bytewise untyped copy, matching the intended Rust semantics. The sequence of bytes does not have to be a valid representation at any type.

  fn copy_nonoverlapping<T>(size, src, dst) {
    let mut count: usize = 0;

    assert_unsafe_precondition!(
        is_aligned_and_not_null(src)
            && is_aligned_and_not_null(dst)
            && is_nonoverlapping(src, dst, count)
    );

    let src = src as *const U8;
    let dst = dst as *mut U8;
    // do a bytewise copy
    while count < size {
      // uses untyped read + assignment, NOT the typed assignment in surface Rust!
      *(dst.add(count)) = *src.add(count);
      count+=1;
    }
  }
 *)
Definition ptr_copy_nonoverlapping `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* ); ("dst", void* ); ("size", USize : layout)];
  f_local_vars := [("_0", use_layout_alg' UnitSynType); ("_1", use_layout_alg' UnitSynType); ("count", USize : layout); ("_3", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
      "count" <-{IntOp USize} i2v 0 USize;
      (* TODO: add safety checks *)
      annot: StopAnnot;
      Goto "_bb_loop_head"
    ]>%E $
    <["_bb_loop_head" :=

      if{BoolOp}:
        (use{IntOp USize} "count") <{IntOp USize, IntOp USize, U8} (use{IntOp USize} "size")
      then
        Goto "_bb_loop_body"
      else
        Goto "_bb_loop_exit"
    ]>%E $
    <["_bb_loop_body" :=
        ((!{PtrOp} "dst") at_offset{use_layout_alg' T_st, PtrOp, IntOp USize} use{IntOp USize} "count")
      <-{UntypedOp (use_layout_alg' T_st)}
        use{UntypedOp (use_layout_alg' T_st)} (
          ((!{PtrOp} "src") at_offset{use_layout_alg' T_st, PtrOp, IntOp USize} use{IntOp USize} "count"));
      "count" <-{IntOp USize} (use{IntOp USize} "count") +{IntOp USize, IntOp USize} (i2v 1 USize);
      Goto "_bb_loop_head"
    ]>%E $
    <["_bb_loop_exit" :=
      annot: StopAnnot;
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.

Definition ptr_offset `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", ISize : layout)];
  f_local_vars := [("ret", void* : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} ((use{PtrOp} "self") at_offset{use_layout_alg' T_st, PtrOp, IntOp ISize} (use{IntOp ISize} "count"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.

Definition ptr_sub `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", USize : layout)];
  f_local_vars := [("ret", void* : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} ((use{PtrOp} "self") at_neg_offset{use_layout_alg' T_st, PtrOp, IntOp USize} (use{IntOp USize} "count"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.


Definition ptr_wrapping_offset `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", ISize : layout)];
  f_local_vars := [("ret", void* : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} ((use{PtrOp} "self") at_wrapping_offset{use_layout_alg' T_st, PtrOp, IntOp ISize} (use{IntOp ISize} "count"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.

Definition ptr_wrapping_add `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", USize : layout)];
  f_local_vars := [("ret", void* : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} ((use{PtrOp} "self") at_wrapping_offset{use_layout_alg' T_st, PtrOp, IntOp USize} (use{IntOp USize} "count"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.

Definition ptr_wrapping_sub `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", USize : layout)];
  f_local_vars := [("ret", void* : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} ((use{PtrOp} "self") at_wrapping_neg_offset{use_layout_alg' T_st, PtrOp, IntOp USize} (use{IntOp USize} "count"));
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.

Definition ptr_with_addr `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("addr", USize : layout)];
  f_local_vars := [("ret", void* : layout); ("_1", use_layout_alg' UnitSynType); ("_2", use_layout_alg' UnitSynType)];
  f_code :=
    <["_bb0" :=
        "ret" <-{PtrOp} CopyAllocId (IntOp USize) (use{IntOp USize} "addr") (use{PtrOp} "self");
        return (use{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
