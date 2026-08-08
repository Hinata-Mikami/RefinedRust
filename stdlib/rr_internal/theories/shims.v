From radium Require Import lang notation.
From refinedrust Require Import typing shims.

From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.


(** Allocator API *)
(*
  how do we specify allocations?
  - option 1: have an owned_ptr type (essentially box, but without the deallocation permission) and keep the deallocation permission external
  - option 2: just return a box (this is a bit of a red herring, since it really would not be a Rust Box)
  - option 3: have an allocation_t type that also deals with the additional flexibility for freeable permissions we will need for gathering stuff for reallocation.
      + we need this anyways, but can we also use it here?
      => work this out in detail first, then decide here.
  - option 4: use ofty + value
    => Going with this.
 *)


(**
  fn alloc_realloc(old_size, align, new_size, ptr) -> *mut U8 {
    let new_ptr = alloc::alloc(new_size, align);
    copy_nonoverlapping(ptr, new_ptr, min(old_size, new_size));
    alloc::dealloc(old_size, align, ptr);
    new_ptr
  }
*)
Program Definition alloc_realloc_def `{!LayoutAlg} (alloc_alloc_loc : loc) (copy_nonoverlapping_loc : loc) (alloc_dealloc_loc : loc) : function := {|
  f_args := [("old_size", USize : layout); ("align", USize : layout); ("new_size", USize : layout); ("ptr", void* )];
  f_code :=
    <["_bb0" :=
      local_live{PtrSynType} "new_ptr";
      local_live{IntSynType USize} "min_size";
      CallS alloc_alloc_loc [] [] [@{expr} copy{IntOp USize} "new_size"; copy{IntOp USize} "align"]
        (Some (Na1Ord, PtrOp, "new_ptr"))
        ("min_size" <-{IntOp USize} (IfE BoolOp (copy{IntOp USize} "new_size" <{IntOp USize, IntOp USize, U8} copy{IntOp USize} "old_size") (copy{IntOp USize} "new_size") (copy{IntOp USize} "old_size"));
         annot{0}: StopAnnot;
         CallS copy_nonoverlapping_loc [] [RSTInt U8] [@{expr} copy{PtrOp} "ptr"; copy{PtrOp} "new_ptr"; copy{IntOp USize} "min_size"] None
           (CallS alloc_dealloc_loc [] [] [@{expr} copy{IntOp USize} "old_size"; copy{IntOp USize} "align"; copy{PtrOp} "ptr"] None
             (return (move{PtrOp} "new_ptr")) StuckS) StuckS) StuckS
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.


#[global] Typeclasses Opaque layout_wf.

Definition type_of_alloc_realloc `{RRGS : !refinedrustGS Σ} :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | (old_size, align_log2, new_size, ptr_old, v) : (Z * Z * Z * loc * val), (λ ϝ, []); old_size :@: int USize, align_log2 :@: int USize, new_size :@: int USize, ptr_old :@: alias_ptr_t; λ π,
    (* TODO restriction of the spec: we cannot shrink it *)
    ⌜(old_size ≤ new_size)%Z⌝ ∗
    ⌜(0 < old_size)%Z⌝ ∗
    ⌜new_size ≤ MaxInt ISize⌝ ∗
    (* TODO: restriction placed by our syntype model, not required in Rust *)
    ⌜layout_wf (Layout (Z.to_nat new_size) (Z.to_nat align_log2))⌝ ∗
    (*⌜ly_align_in_bounds (Layout (Z.to_nat new_size) (Z.to_nat align_log2))⌝ ∗*)
    (*⌜layout_wf (Layout (Z.to_nat old_size) (Z.to_nat align_log2))⌝ ∗*)
    ptr_old ◁ₗ[π, Owned ] PlaceIn v @ (◁ value_t false (LiteralSynType (Layout (Z.to_nat old_size) (Z.to_nat align_log2)))) ∗
    freeable_nz ptr_old (Z.to_nat old_size) 1 HeapAlloc) →
  ∃ (ptr_new, v') : (loc * val), ptr_new @ alias_ptr_t; λ π,
    freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc ∗
    ptr_new ◁ₗ[π, Owned] #(v ++ v' : val) @ (◁ value_t false (LiteralSynType (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))) ∗
    ⌜v' `has_layout_val` (Layout (Z.to_nat (new_size - old_size)) (Z.to_nat align_log2))⌝ |
  False
.
#[global] Typeclasses Opaque Z.divide.
Lemma alloc_realloc_typed `{RRGS : !refinedrustGS Σ} π (alloc_alloc_loc copy_nonoverlapping_loc alloc_dealloc_loc : loc) :
  alloc_alloc_loc ◁ᵥ{π, MetaNone} alloc_alloc_loc @ function_ptr [IntSynType USize; IntSynType USize] (<tag_type> type_of_alloc_alloc_internal) -∗
  copy_nonoverlapping_loc ◁ᵥ{π, MetaNone} copy_nonoverlapping_loc @ function_ptr [PtrSynType; PtrSynType; IntSynType USize] (<tag_type> type_of_copy_nonoverlapping Z (IntSynType U8)) -∗
  alloc_dealloc_loc ◁ᵥ{π, MetaNone} alloc_dealloc_loc @ function_ptr [IntSynType USize; IntSynType USize; PtrSynType] (<tag_type> type_of_alloc_dealloc_internal) -∗
  typed_function π (alloc_realloc_def alloc_alloc_loc copy_nonoverlapping_loc alloc_dealloc_loc) (<tag_type> type_of_alloc_realloc).
Proof.
  start_function "alloc_realloc" ϝ ( () ) ( () ) ( [[[[old_size align_log2] new_size] ptr_old] v_old] ) ( ) => l_old_size l_align_log2 l_new_size l_ptr_old.
  init_lfts ∅.
  init_tyvars ∅.
  set (old_ly := Layout (Z.to_nat old_size) (Z.to_nat align_log2)).
  set (new_ly := Layout (Z.to_nat new_size) (Z.to_nat align_log2)).
  repeat liRStep. liShow.
  fold old_ly new_ly.
  (* augment context with layout well-formedness info *)
  iRename select (ptr_old ◁ₗ[_, _] _ @ _)%I into "Hold".
  rename x' into l_new.
  iRename select (l_new ◁ₗ[_, _] _ @ _)%I into "Hnew".
  iPoseProof (ltype_own_has_layout with "Hold") as "(%ly_old & %Halg_old & %)".
  iPoseProof (ltype_own_has_layout with "Hnew") as "(%ly_new & %Halg_new & %)".
  simp_ltypes in Halg_old.
  apply syn_type_has_layout_untyped_inv in Halg_old.
  apply syn_type_has_layout_literal_inv in Halg_old as (-> & ? & ?).
  simp_ltypes in Halg_new.
  apply syn_type_has_layout_untyped_inv in Halg_new.
  apply syn_type_has_layout_literal_inv in Halg_new as (-> & _ & _).

  iApply typed_annot_stmt_skip.
  liRStepUntil (typed_call).
  (* make into value, because the part not affected by the memcpy will be returned *)
  (*iRename select (l_new ◁ₗ[_, _] .@ _)%I into "Hnew".*)

  (* The copy_nonoverlapping does a bytewise copy, so we need to convert it into an "array" of bytes *)
  iApply fupd_typed_call.
  iMod (ofty_uninit_to_untyped_value with "Hnew") as "(%vn & Hnew)"; first done.
  iMod (ofty_value_has_length with "Hnew") as "(%Hlen & Hnew)"; [done | | ].
  { eapply syn_type_has_layout_literal; [done.. | rewrite /ly_size/=; lia | ].
    open_cache. done. }
  iPoseProof (ofty_value_untyped_to_byte_array with "Hnew") as "Hnew".
  iMod (ofty_value_array_split _ _ _ _ (take (ly_size old_ly) vn) (drop (ly_size old_ly) vn) _ (ly_size old_ly) (ly_size new_ly - ly_size old_ly)  with "Hnew") as "(Hnew1 & Hnew2)"; first done.
  { rewrite take_drop//. }
  { simpl. lia. }
  { by apply syn_type_has_layout_int. }
  { rewrite length_take. simpl.
    rewrite /bytes_per_int/it_byte_size_log/=.
    simpl. rewrite Hlen. subst new_ly. simpl. lia. }
  { rewrite length_drop. simpl.
    rewrite /bytes_per_int/it_byte_size_log/=.
    simpl. rewrite Hlen. subst new_ly. simpl. lia. }
  iModIntro.
  iPoseProof (ofty_value_untyped_to_byte_array with "Hold") as "Hold".
  rep <-! liRStep; liShow.
  (* merge the two array chunks again and reshape the layout *)
  iRename select (l_new ◁ₗ[_, _] #v_old @ _)%I into "Hnew".
  iApply fupd_typed_val_expr.
  iMod (ofty_value_array_merge _ _ _ _ _ _ _ _ _ _ _  with "Hnew Hnew2") as "Hnew"; [done | done | | ].
  { solve_layout_alg. }
  iPoseProof (ofty_value_untyped_to_literal with "Hnew") as "Hnew".
  { solve_layout_alg. }
  iPoseProof (ofty_value_untyped_update_layout new_ly with "Hnew") as "Hnew"; [sidecond_hammer.. | ].
  iModIntro.
  rep <-! liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite /has_layout_val length_drop/=. rewrite Hlen/new_ly/ly_size/=.  lia.  }
Qed.

(** ** Array allocator shims *)

(** alloc_array *)
Program Definition alloc_array `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_alloc_loc : loc) : function := {|
  f_args := [("len", USize : layout)];
  f_code :=
    <["bb0" :=
      local_live{IntSynType USize} "align_log2";
      local_live{IntSynType USize} "size_of_T";
      local_live{IntSynType USize} "bytes";
      local_live{PtrSynType} "__0";
      CallS mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
        (Some (Na1Ord, IntOp USize, "align_log2"))
        (CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
          (Some (Na1Ord, IntOp USize, "size_of_T"))
          ("bytes" <-{ IntOp USize } ((copy{IntOp USize} "len") ×{IntOp USize, IntOp USize} (copy{IntOp USize} "size_of_T"));
           CallS alloc_alloc_loc [] [] [@{expr} copy{IntOp USize} "bytes"; copy{IntOp USize} "align_log2"]
             (Some (Na1Ord, PtrOp, "__0"))
             (return (move{PtrOp} "__0")) StuckS) StuckS) StuckS
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.
Next Obligation. solve_fn_vars_nodup. Qed.


Definition trait_incl_of_alloc_array `{RRGS : !refinedrustGS Σ} (T_rt: RT) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).
Definition type_of_alloc_array `{RRGS : !refinedrustGS Σ} (T_rt : RT) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (size) : (Z), (λ ϝ, []); size :@: int USize; λ π,
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ ISize⌝ ∗
    ⌜(size > 0)%Z⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ l : loc, l @ alias_ptr_t; λ π,
      l ◁ₗ[π, Owned ] .@ (◁ (uninit (ArraySynType T_st (Z.to_nat size)))) ∗
      freeable_nz l ((size_of_array_in_bytes T_st (Z.to_nat size))) 1 HeapAlloc | False.

Lemma alloc_array_layout_wf T_st_ly size :
  layout_wf T_st_ly →
  layout_wf
  {|
    ly_size := Z.to_nat size * ly_size T_st_ly;
    ly_align_log := ly_align_log T_st_ly
  |}.
Proof.
  intros (x & Hwf).
  exists (Z.to_nat size * x)%Z.
  simpl. rewrite {1}/ly_align {1}/ly_align_log. simpl.
  fold (ly_align T_st_ly). lia.
Qed.
Lemma alloc_array_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_alloc_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π, MetaNone} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗


  mem_size_of_T_loc ◁ᵥ{π, MetaNone} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  alloc_alloc_loc ◁ᵥ{π, MetaNone} alloc_alloc_loc @ function_ptr [IntSynType USize; IntSynType USize] (<tag_type> type_of_alloc_alloc_internal) -∗
  typed_function π (alloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_alloc_loc) (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_alloc_array T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "alloc_array" ϝ ( () ) ( [T_ty []] ) ( size ) ( ) => arg_len.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  all: unfold size_of_array_in_bytes in *; simplify_layout_assum; sidecond_hammer.
  1: apply alloc_array_layout_wf; sidecond_hook.
Qed.

(** realloc_array *)
Program Definition realloc_array `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_realloc_loc : loc) : function := {|
  f_args := [
    ("old_len", USize : layout);
    ("ptr", void* : layout);
    ("new_len", USize : layout)
  ];
  f_code :=
    <["bb0" :=
      local_live{IntSynType USize} "align_log2";
      local_live{IntSynType USize} "size_of_T";
      local_live{IntSynType USize} "old_bytes";
      local_live{IntSynType USize} "new_bytes";
      local_live{PtrSynType} "__0";
      CallS mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
        (Some (Na1Ord, IntOp USize, "align_log2"))
        (CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
          (Some (Na1Ord, IntOp USize, "size_of_T"))
          ("old_bytes" <-{ IntOp USize } ((copy{IntOp USize} "old_len") ×{IntOp USize, IntOp USize} (copy{IntOp USize} "size_of_T"));
           "new_bytes" <-{ IntOp USize } ((copy{IntOp USize} "new_len") ×{IntOp USize, IntOp USize} (copy{IntOp USize} "size_of_T"));
           CallS alloc_realloc_loc [] [] [@{expr} copy{IntOp USize} "old_bytes"; copy{IntOp USize} "align_log2"; copy{IntOp USize} "new_bytes"; copy{PtrOp} "ptr"]
             (Some (Na1Ord, PtrOp, "__0"))
             (return (move{PtrOp} "__0")) StuckS) StuckS) StuckS
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.
Next Obligation. solve_fn_vars_nodup. Qed.


Definition trait_incl_of_realloc_array `{RRGS : !refinedrustGS Σ} (T_rt: RT) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).
(* Spec is using UntypedSynType (instead of ArraySynType) because this is using untyped copies *)
Definition type_of_realloc_array `{RRGS : !refinedrustGS Σ} (T_rt : RT) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (old_size, new_size, l, v) : (Z * Z * loc * val), (λ ϝ, []);
    old_size :@: int USize, l :@: alias_ptr_t, new_size :@: int USize; λ π,
    freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat old_size)) 1 HeapAlloc ∗
    l ◁ₗ[π, Owned ] #v @ (◁ value_t false (ArraySynType T_st (Z.to_nat old_size))) ∗
    ⌜(old_size ≤ new_size)%Z⌝ ∗
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat new_size)) ∈ ISize⌝ ∗
    ⌜(old_size > 0)%Z⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ (l', v') : (loc * val), l' @ alias_ptr_t; λ π,
    l' ◁ₗ[π, Owned ] #(v ++ v' : val) @ (◁ (value_t false (ArraySynType T_st (Z.to_nat new_size)))) ∗
    v' ◁ᵥ{π, MetaNone} .@ uninit (ArraySynType T_st (Z.to_nat (new_size - old_size))) ∗
      freeable_nz l' ((size_of_array_in_bytes T_st (Z.to_nat new_size))) 1 HeapAlloc | False.

Lemma realloc_array_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_realloc_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π, MetaNone} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  mem_size_of_T_loc ◁ᵥ{π, MetaNone} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  alloc_realloc_loc ◁ᵥ{π, MetaNone} alloc_realloc_loc @ function_ptr [IntSynType USize; IntSynType USize; IntSynType USize; PtrSynType] (<tag_type> type_of_alloc_realloc_internal) -∗
  typed_function π (realloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_realloc_loc) (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_realloc_array T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "realloc_array" ϝ ( () ) ( [T_ty []] ) ( [[[old_size new_size] l] v] ) ( ) => arg_old_len arg_ptr arg_new_len.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.

  rep <-! liRStep; liShow.
  iRename select (l ◁ₗ[_, _] #v @ _)%I into "Hold".
  iPoseProof (ofty_value_untyped_to_literal with "Hold") as "Hold".
  { solve_layout_alg. }

  rep <-! liRStep; liShow.

  iAssert (x'0 ◁ᵥ{π, MetaNone} .@ uninit (ArraySynType (st_of T_ty MetaNone) (Z.to_nat (new_size - old_size))))%I as "Ha".
  { rewrite uninit_own_spec. iR. iExists _.
    { iSplitR.
      { iPureIntro. solve_layout_alg. }
      iPureIntro. rewrite /has_layout_val.
      match goal with | H : x'0 `has_layout_val` _ |- _ => rename H into Hlen end.
      rewrite Hlen.
      solve_goal.
   }
  }
  iRename select (x' ◁ₗ[_, _] _ @ _)%I into "Hnew".
  iPoseProof (ofty_value_untyped_from_literal (ArraySynType (st_of T_ty MetaNone) (Z.to_nat new_size)) with "Hnew") as "Hnew".
  { solve_layout_alg. }
  rep liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: unfold size_of_array_in_bytes in *; simplify_layout_assum.
  all: rewrite Nat.mul_comm; (try done); apply array_layout_wf; sidecond_hook.
Qed.


(** dealloc_array *)
Program Definition dealloc_array `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_dealloc_loc : loc) : function := {|
  f_args := [
    ("len", USize : layout);
    ("ptr", void* : layout)
  ];
  f_code :=
    <["bb0" :=
      local_live{IntSynType USize} "align_log2";
      local_live{IntSynType USize} "size_of_T";
      local_live{IntSynType USize} "bytes";
      local_live{UnitSynType} "__0";
      CallS mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
        (Some (Na1Ord, IntOp USize, "align_log2"))
        (CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
          (Some (Na1Ord, IntOp USize, "size_of_T"))
          ("bytes" <-{ IntOp USize } ((copy{IntOp USize} "len") ×{IntOp USize, IntOp USize} (copy{IntOp USize} "size_of_T"));
           CallS alloc_dealloc_loc [] [] [@{expr} copy{IntOp USize} "bytes"; copy{IntOp USize} "align_log2"; copy{PtrOp} "ptr"] None
             ("__0" <-{use_op_alg' UnitSynType} zst_val;
              return (move{use_op_alg' UnitSynType} "__0")) StuckS) StuckS) StuckS
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.
Next Obligation. solve_fn_vars_nodup. Qed.


Definition trait_incl_of_dealloc_array `{RRGS : !refinedrustGS Σ} (T_rt: RT) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).
Definition type_of_dealloc_array `{RRGS : !refinedrustGS Σ} (T_rt : RT) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (size, l) : (Z * loc), (λ ϝ, []);
    size :@: int USize, l :@: alias_ptr_t; λ π,
    freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat size)) 1 HeapAlloc ∗
    l ◁ₗ[π, Owned ] .@ (◁ uninit (ArraySynType T_st (Z.to_nat size))) ∗
    ⌜(size > 0)%Z⌝ ∗
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ ISize⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ () : unit, () @ unit_t; λ π, True | False.


Lemma dealloc_array_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_dealloc_loc : loc) :
  syn_type_is_layoutable T_st →

  mem_align_log_of_T_loc ◁ᵥ{π, MetaNone} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  mem_size_of_T_loc ◁ᵥ{π, MetaNone} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  alloc_dealloc_loc ◁ᵥ{π, MetaNone} alloc_dealloc_loc @ function_ptr [IntSynType USize; IntSynType USize; PtrSynType] (<tag_type> type_of_alloc_dealloc_internal) -∗
  typed_function π (dealloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_dealloc_loc) (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_dealloc_array T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "dealloc_array" ϝ ( () ) ( [T_ty []] ) ( [size l] ) ( ) => arg_len arg_ptr.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rewrite Nat.mul_comm.
  all: apply array_layout_wf; sidecond_hook.
Qed.

(** check_array_layoutable *)
Program Definition check_array_layoutable `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) : function := {|
  f_args := [
    ("len", USize : layout)
  ];
  f_code :=
    <["bb0" :=
      local_live{BoolSynType} "__0";
      local_live{IntSynType USize} "align_log2";
      local_live{IntSynType USize} "size_of_T";
      local_live{IntSynType USize} "bytes";
      local_live{BoolSynType} "check";
      CallS mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
        (Some (Na1Ord, IntOp USize, "align_log2"))
        (CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ]
          (Some (Na1Ord, IntOp USize, "size_of_T"))
          ("check" <-{ BoolOp } ((copy{IntOp USize} "len") ×c{IntOp USize, IntOp USize} (copy{IntOp USize} "size_of_T"));
           if{BoolOp}: (copy{BoolOp} "check") then Goto "bb2" else Goto "bb1") StuckS) StuckS ]>%E $
    <["bb1" :=
      (* result fits into usize *)
      "bytes" <-{ IntOp USize } ((copy{IntOp USize} "len") ×{IntOp USize, IntOp USize} (copy{IntOp USize} "size_of_T"));
      "__0" <-{use_op_alg' BoolSynType} ((copy{IntOp USize} "bytes") ≤{IntOp USize, IntOp USize, U8} (i2v (MaxInt ISize) USize));
      return (move{use_op_alg' BoolSynType} "__0")
    ]>%E $
    <["bb2" :=
      (* result does not fit into usize *)
      return (Val (val_of_bool false))
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.
Next Obligation. solve_fn_vars_nodup. Qed.


Definition trait_incl_of_check_array_layoutable `{RRGS : !refinedrustGS Σ} (T_rt: RT) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (True).
Definition type_of_check_array_layoutable `{RRGS : !refinedrustGS Σ} (T_rt : RT) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (size) : (Z), (λ ϝ, []); size :@: int USize; λ π, True) →
  ∃ () : unit, (bool_decide (size_of_array_in_bytes T_st (Z.to_nat size) ≤ MaxInt ISize)%Z) @ bool_t; λ π, True | False.

Lemma check_array_layoutable_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π, MetaNone} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗
  mem_size_of_T_loc ◁ᵥ{π, MetaNone} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗
  typed_function π (check_array_layoutable T_st mem_align_log_of_T_loc mem_size_of_T_loc) (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_check_array_layoutable T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "check_array_layoutable" ϝ ( () ) ( [T_ty []] ) ( size ) ( ) => arg_len.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.
