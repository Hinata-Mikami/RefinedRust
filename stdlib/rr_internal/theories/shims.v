From caesium Require Import lang notation.
From refinedrust Require Import typing shims.

From stdlib.ptr.ptr.generated Require Export generated_specs_ptr.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.

(** ** Ptr API *)

Definition ptr_is_null `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* )];
  f_local_vars := [];
  f_code :=
    <["_bb0" :=
      return (use{PtrOp} "self" = {PtrOp, PtrOp, u8} NULL)
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_ptr_is_null `{RRGS : !refinedrustGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (l) : loc, (λ ϝ, []); l :@: alias_ptr_t; λ π, True) → ∃ b : bool, b @ bool_t; λ π, ⌜b = bool_decide (l.2 = 0)⌝.
(* TODO should maybe adapt pointer comparison semantics beforehand, because Caesium currently requires the loc_in_bounds stuff for comparison. *)
(* TODO should also have some automation to learn things - i.e. gain knowledge that b = false in case we actually have ownership *)




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
  fn alloc_realloc(old_size, align, new_size, ptr) -> *mut u8 {
    let new_ptr = alloc::alloc(new_size, align);
    copy_nonoverlapping(ptr, new_ptr, min(old_size, new_size));
    alloc::dealloc(old_size, align, ptr);
    new_ptr
  }
*)
Definition alloc_realloc_def `{!LayoutAlg} (alloc_alloc_loc : loc) (copy_nonoverlapping_loc : loc) (alloc_dealloc_loc : loc) : function := {|
  f_args := [("old_size", usize_t : layout); ("align", usize_t : layout); ("new_size", usize_t : layout); ("ptr", void* )];
  f_local_vars := [("new_ptr", void* ); ("min_size", usize_t : layout)];
  f_code :=
    <["_bb0" :=
      "new_ptr" <-{PtrOp} CallE alloc_alloc_loc [] [] [@{expr} use{IntOp usize_t} "new_size"; use{IntOp usize_t} "align"];
      "min_size" <-{IntOp usize_t} (IfE BoolOp (use{IntOp usize_t} "new_size" <{IntOp usize_t, IntOp usize_t, u8} use{IntOp usize_t} "old_size") (use{IntOp usize_t} "new_size") (use{IntOp usize_t} "old_size"));
      annot: StopAnnot;
      expr: CallE copy_nonoverlapping_loc [] [RSTInt U8] [@{expr} use{PtrOp} "ptr"; use{PtrOp} "new_ptr"; use{IntOp usize_t} "min_size"];
      expr: CallE alloc_dealloc_loc [] [] [@{expr} use{IntOp usize_t} "old_size"; use{IntOp usize_t} "align"; use{PtrOp} "ptr"];
      return (use{PtrOp} "new_ptr")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.


#[global] Typeclasses Opaque layout_wf.

Definition type_of_alloc_realloc `{RRGS : !refinedrustGS Σ} :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | (old_size, align_log2, new_size, ptr_old, v) : (Z * Z * Z * loc * val), (λ ϝ, []); old_size :@: int usize_t, align_log2 :@: int usize_t, new_size :@: int usize_t, ptr_old :@: alias_ptr_t; λ π,
    (* TODO restriction of the spec: we cannot shrink it *)
    ⌜(old_size ≤ new_size)%Z⌝ ∗
    ⌜(0 < old_size)%Z⌝ ∗
    ⌜new_size ≤ MaxInt isize_t⌝ ∗
    (* TODO: restriction placed by our syntype model, not required in Rust *)
    ⌜layout_wf (Layout (Z.to_nat new_size) (Z.to_nat align_log2))⌝ ∗
    (*⌜ly_align_in_bounds (Layout (Z.to_nat new_size) (Z.to_nat align_log2))⌝ ∗*)
    (*⌜layout_wf (Layout (Z.to_nat old_size) (Z.to_nat align_log2))⌝ ∗*)
    ptr_old ◁ₗ[π, Owned false] PlaceIn v @ (◁ value_t (UntypedSynType (Layout (Z.to_nat old_size) (Z.to_nat align_log2)))) ∗
    freeable_nz ptr_old (Z.to_nat old_size) 1 HeapAlloc) →
  ∃ (ptr_new, v') : (loc * val), ptr_new @ alias_ptr_t; λ π,
    freeable_nz ptr_new (Z.to_nat new_size) 1 HeapAlloc ∗
    ptr_new ◁ₗ[π, Owned false] #(v ++ v') @ (◁ value_t (UntypedSynType (Layout (Z.to_nat new_size) (Z.to_nat align_log2)))) ∗
    ⌜v' `has_layout_val` (Layout (Z.to_nat (new_size - old_size)) (Z.to_nat align_log2))⌝
.
#[global] Typeclasses Opaque Z.divide.
Lemma alloc_realloc_typed `{RRGS : !refinedrustGS Σ} π alloc_alloc_loc copy_nonoverlapping_loc alloc_dealloc_loc :
  alloc_alloc_loc ◁ᵥ{π} alloc_alloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t] (<tag_type> type_of_alloc_alloc_internal) -∗
  copy_nonoverlapping_loc ◁ᵥ{π} copy_nonoverlapping_loc @ function_ptr [PtrSynType; PtrSynType; IntSynType usize_t] (<tag_type> type_of_copy_nonoverlapping Z (IntSynType u8)) -∗
  alloc_dealloc_loc ◁ᵥ{π} alloc_dealloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t; PtrSynType] (<tag_type> type_of_alloc_dealloc_internal) -∗
  typed_function π (alloc_realloc_def alloc_alloc_loc copy_nonoverlapping_loc alloc_dealloc_loc) [PtrSynType; IntSynType usize_t] (<tag_type> type_of_alloc_realloc).
Proof.
  start_function "alloc_realloc" ϝ ( () ) ( () ) ( [[[[old_size align_log2] new_size] ptr_old] v_old] ) ( ) => l_old_size l_align_log2 l_new_size l_ptr_old l_ptr_new l_min_size.
  init_lfts ∅.
  init_tyvars ∅.
  set (old_ly := Layout (Z.to_nat old_size) (Z.to_nat align_log2)).
  set (new_ly := Layout (Z.to_nat new_size) (Z.to_nat align_log2)).
  repeat liRStep. liShow.
  fold old_ly new_ly.
  (* augment context with layout well-formedness info *)
  iRename select (ptr_old ◁ₗ[_, _] _ @ _)%I into "Hold".
  iRename select (x' ◁ₗ[_, _] _ @ _)%I into "Hnew".
  iPoseProof (ltype_own_has_layout with "Hold") as "(%ly_old & %Halg_old & %)".
  iPoseProof (ltype_own_has_layout with "Hnew") as "(%ly_new & %Halg_new & %)".
  simp_ltypes in Halg_old. apply syn_type_has_layout_untyped_inv in Halg_old as (-> & ? & ?).
  simp_ltypes in Halg_new. apply syn_type_has_layout_untyped_inv in Halg_new as (-> & _ & _).

  iApply typed_stmt_annot_skip.
  liRStepUntil (typed_call).
  (* make into value, because the part not affected by the memcpy will be returned *)
  iRename select (x' ◁ₗ[_, _] .@ _)%I into "Hnew".

  (* The copy_nonoverlapping does a bytewise copy, so we need to convert it into an "array" of bytes *)
  iApply fupd_typed_call.
  iMod (ofty_uninit_to_value with "Hnew") as "(%vn & Hnew)"; first done.
  iMod (ofty_value_has_length with "Hnew") as "(%Hlen & Hnew)"; [done | | ].
  { eapply syn_type_has_layout_untyped; [done.. | | done]. rewrite /ly_size/=. lia. }
  iPoseProof (ofty_value_untyped_to_bytes with "Hnew") as "Hnew".
  iMod (ofty_value_untyped_split_app_array _ _ _ _ (ly_size new_ly - ly_size old_ly) (ly_size old_ly)  with "Hnew") as "(Hnew1 & Hnew2)"; first done.
  { simpl. lia. }
  { rewrite /layout_wf/ly_align/it_layout. simpl. apply Z.divide_1_l. }
  simpl. rewrite !Nat.add_0_r.
  iModIntro.
  rep liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite /has_layout_loc/layout_wf/aligned_to /ly_align/u8/=. destruct caesium_config.enforce_alignment; last done. apply Z.divide_1_l. }
  { rewrite /has_layout_loc/layout_wf/aligned_to /ly_align/u8/=. destruct caesium_config.enforce_alignment; last done. apply Z.divide_1_l. }
  { rewrite /has_layout_val length_drop/=. rewrite Hlen/new_ly/ly_size/=.  lia.  }
Qed.




(** Box API *)
Definition box_new `{!LayoutAlg} (T_st : syn_type) (mem_size_of_T_loc : loc) (ptr_dangling_T_loc : loc) : function := {|
 f_args := [("x", use_layout_alg' T_st)];
 f_local_vars := [
   ("__0", void* : layout);
   ("size", usize_t : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* check if the size is 0 *)
   "size" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
   if{BoolOp}: use{IntOp usize_t} "size" = {IntOp usize_t, IntOp usize_t, u8} I2v 0 USize
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

Definition type_of_box_new `{RRGS : !refinedrustGS Σ} T_rt T_st :=
  fn(∀ ( *[]) : 0 | ( *[T]) : [(T_rt, T_st)] | (x) : _, (λ ϝ, []); x :@: T; λ π, True)
    → ∃ () : (), x @ box T; λ π, True.
Lemma box_new_typed `{RRGS : !refinedrustGS Σ} π T_st (T_rt : Type) (mem_size_of_T_loc ptr_dangling_T_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗
  ptr_dangling_T_loc ◁ᵥ{π} ptr_dangling_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_dangling T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗
  typed_function π (box_new T_st mem_size_of_T_loc ptr_dangling_T_loc) [PtrSynType; IntSynType usize_t] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_box_new T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "box_new" ϝ ( () ) ( [T []] ) ( x ) ( ) => arg_x local_0 local_size.
  init_tyvars (<["T" := existT _ T]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.
  - (* zero branch *)
    (* TODO maybe use place instance for alias_ptr instead of manually wrapping up the pointsto *)
    iRename select (credit_store _ _) into "Hstore".
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hcl_store)".

    iApply (typed_stmt_annot_credits with "Hat").
    iIntros "Hat Hcred".
    rewrite lc_succ. iDestruct "Hcred" as "(Hcred1 & Hcred)".
    rewrite (additive_time_receipt_succ 1). iDestruct "Hat" as "(Hat1 & Hat)".
    iPoseProof ("Hcl_store" with "Hat") as "Hstore".

    (* make a box type out of the alias_ptr *)
    iSelect (_ ◁ₗ[_, _] _ @ ◁ (uninit UnitSynType))%I (fun H => iRename H into "H_pts").
    iSelect (local_0 ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "H_0").
    iAssert (local_0 ◁ₗ[π, Owned false] #(#())  @ ◁ box (uninit (ty_syn_type T)))%I with "[H_pts H_0 Hcred Hat1]" as "H_0".
    { iApply (ofty_owned_subtype_aligned with "[-H_0] H_0").
      { solve_layout_alg. }
      { done. }
      iSplitR. { iPureIntro. intros ly1 ly2 Hptr1 Hptr2. simpl in *. f_equiv. by eapply syn_type_has_layout_inj. }
      iSplitR. { simpl. eauto. }
      iIntros (v2) "Hv".
      iEval (rewrite /ty_own_val/=) in "Hv".
      iDestruct "Hv" as "(-> & %)".
      iEval (rewrite /ty_own_val/=).
      iExists x', _. iR. iR. iR.
      iPoseProof (ltype_own_loc_in_bounds with "H_pts") as "#Hlb".
      { simp_ltypes. solve_layout_alg. }
      simpl.
      unfold_no_enrich. inv_layout_alg.
      rename select (ly_size _ = 0%nat) into Hsz. rewrite Hsz. iFrame "Hlb".
      iFrame. iExists tt. iR. iNext.
      rewrite ltype_own_ofty_unfold/lty_of_ty_own.
      iDestruct "H_pts" as "(%ly & % & % & _ & _ & _ & %r' & <- & >(%v2 & Hpt & Hb))".
      iModIntro. iExists v2. iFrame.
      rewrite {3 4}/ty_own_val/=.
      iDestruct "Hb" as "(%ly' & %Hstly' & %Hlyv & ?)".
      iExists _. iR. iFrame. iPureIntro.
      apply syn_type_has_layout_unit_inv in Hstly'; subst.
      move: Hlyv. rewrite /has_layout_val => ->. rewrite Hsz. done.
    }
    repeat liRStep.
  - (* non-zero branch, do the allocation *)
    rewrite /typed_val_expr.
    iIntros (?) "#CTX #HE HL Hcont".
    rewrite /Box.
    unfold_no_enrich. inv_layout_alg.
    match goal with | H: Z.of_nat (ly_size ?Hly) ≠ 0%Z |- _ => rename Hly into T_st_ly end.
    have: (Z.of_nat $ ly_size T_st_ly) ∈ usize_t by done.
    opose proof* (ly_align_log_in_usize T_st_ly) as Ha; first done.
    move: Ha. rewrite int_elem_of_it_iff int_elem_of_it_iff.
    intros [? Halign]%(val_of_Z_is_Some None) [? Hsz]%(val_of_Z_is_Some None).
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iSelect (credit_store _ _) ltac:(fun H => iRename H into "Hstore").
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hstore)".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (wp_alloc_credits with "TIME Hat Hp").
    { done. }
    { simplify_layout_goal. rewrite /i2v Hsz /=. by eapply val_to_of_Z. }
    { simplify_layout_goal. rewrite /i2v Halign /=. by eapply val_to_of_Z. }
    { case_bool_decide; [done | lia]. }
    iIntros "!> %l Hl Hfree %Hly [Hcred1 Hcred] Hat".
    iEval (rewrite (additive_time_receipt_succ 1)) in "Hat".
    iDestruct "Hat" as "[Hat1 Hat]".
    iPoseProof ("Hstore" with "Hat1") as "Hstore".
    iApply ("Hcont" $! _ π _ _ (box (uninit (ty_syn_type T))) (# ()) with "HL [Hfree Hl Hcred Hat]").
    { iExists _, _. iSplitR; first done. iSplitR; first done.
      match goal with | H : CACHED (use_layout_alg (ty_syn_type T) = Some ?ly) |- _ => rename ly into T_ly; rename H into H_T end.
      iR.
      iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
      rewrite length_replicate. iFrame "Hlb". simpl. iSplitR; first done. iFrame.
      iSplitL "Hfree". { by iApply freeable_freeable_nz. }
      iExists (). iSplitR; first done. iNext. iModIntro.
      rewrite uninit_own_spec. iExists T_ly.
      iSplitR; first done. rewrite /has_layout_val length_replicate //. }
    iSplitR; first done.
    repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.

(* Drop functions receive a pointer to the thing to drop, just like drop_in_place *)

(* Drop for box *)
Definition drop_box_T (T_ly : layout) (drop_T_loc : loc) : function := {|
 f_args := [("x", void*)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
    (* TODO: have a path for ZST *)
   (* drop T in-place, pass a pointer to the T *)
   expr: Call drop_T_loc [&raw{Mut} (!{PtrOp} (!{PtrOp} "x"))];
   (* now free the memory *)
   (* TODO: use alloc_dealloc here? *)
   (*Free (use{ PtrOp } (!{PtrOp} "x"));*)
   (* return *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.


(* Drop for integer types *)
Definition drop_int (it : int_type) : function := {|
  f_args := [("x", void* : layout)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* do nothing *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

(* Drop for mutable references *)
Definition drop_mutref : function := {|
 f_args := [("x", void*)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* do nothing, but on the ghost level, do a ghost drop *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

(* Drop for shared references *)
Definition drop_shrref : function := {|
 f_args := [("x", void*)];
 f_local_vars := [
  ("__0", unit_sl : layout)
 ];
 f_code :=
  <["_bb0" :=
   (* do nothing *)
   "__0" <-{ UntypedOp (unit_sl) } zst_val;
   return (use{ UntypedOp (unit_sl) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.



(** ** Array allocator shims *)

Definition size_of_array_in_bytes `{!LayoutAlg} (st : syn_type) (len : nat) : nat :=
  let ly := use_layout_alg' st in
  ly.(ly_size) * len.
Global Hint Unfold size_of_array_in_bytes : core.

(** alloc_array *)
Definition alloc_array (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_alloc_loc : loc) : function := {|
  f_args := [("len", usize_t : layout)];
  f_local_vars := [
    ("__0", void* : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("bytes", usize_t : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "__0" <-{PtrOp} CallE alloc_alloc_loc [] [] [@{expr} use{IntOp usize_t} "bytes"; use{IntOp usize_t} "align_log2"];
      return (use{PtrOp} "__0")
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.


Definition trait_incl_of_alloc_array `{RRGS : !refinedrustGS Σ} (T_rt: Type) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list Type), (True).
Definition type_of_alloc_array `{RRGS : !refinedrustGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (size) : (Z), (λ ϝ, []); size :@: int usize_t; λ π,
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ isize_t⌝ ∗
    ⌜(size > 0)%Z⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ l : loc, l @ alias_ptr_t; λ π,
      l ◁ₗ[π, Owned false] .@ (◁ (uninit (ArraySynType T_st (Z.to_nat size)))) ∗
      freeable_nz l ((size_of_array_in_bytes T_st (Z.to_nat size))) 1 HeapAlloc.

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
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗


  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  alloc_alloc_loc ◁ᵥ{π} alloc_alloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t] (<tag_type> type_of_alloc_alloc_internal) -∗
  typed_function π (alloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_alloc_loc) [PtrSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_alloc_array T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "alloc_array" ϝ ( () ) ( [T_ty []] ) ( size ) ( ) => arg_len local_0 local_align_log2 local_size_of_T local_bytes.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: by apply alloc_array_layout_wf.
Qed.

(** realloc_array *)
Definition realloc_array (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_realloc_loc : loc) : function := {|
  f_args := [
    ("old_len", usize_t : layout);
    ("ptr", void* : layout);
    ("new_len", usize_t : layout)
  ];
  f_local_vars := [
    ("__0", void* : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("old_bytes", usize_t : layout);
    ("new_bytes", usize_t : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "old_bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "old_len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "new_bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "new_len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "__0" <-{PtrOp} CallE alloc_realloc_loc [] [] [@{expr} use{IntOp usize_t} "old_bytes"; use{IntOp usize_t} "align_log2"; use{IntOp usize_t} "new_bytes"; use{PtrOp} "ptr"];
      return (use{PtrOp} "__0")
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.


Definition trait_incl_of_realloc_array `{RRGS : !refinedrustGS Σ} (T_rt: Type) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list Type), (True).
(* Spec is using UntypedSynType (instead of ArraySynType) because this is using untyped copies *)
Definition type_of_realloc_array `{RRGS : !refinedrustGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (old_size, new_size, l, v) : (Z * Z * loc * val), (λ ϝ, []);
    old_size :@: int usize_t, l :@: alias_ptr_t, new_size :@: int usize_t; λ π,
    freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat old_size)) 1 HeapAlloc ∗
    l ◁ₗ[π, Owned false] #v @ (◁ value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat old_size)))) ∗
    ⌜(old_size ≤ new_size)%Z⌝ ∗
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat new_size)) ∈ isize_t⌝ ∗
    ⌜(old_size > 0)%Z⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ (l', v') : (loc * val), l' @ alias_ptr_t; λ π,
    l' ◁ₗ[π, Owned false] #(v ++ v') @ (◁ (value_t (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat new_size))))) ∗
    v' ◁ᵥ{π} .@ uninit (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat (new_size - old_size)))) ∗
      freeable_nz l' ((size_of_array_in_bytes T_st (Z.to_nat new_size))) 1 HeapAlloc.

Lemma realloc_array_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_realloc_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  alloc_realloc_loc ◁ᵥ{π} alloc_realloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t; IntSynType usize_t; PtrSynType] (<tag_type> type_of_alloc_realloc_internal) -∗
  typed_function π (realloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_realloc_loc) [PtrSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_realloc_array T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "realloc_array" ϝ ( () ) ( [T_ty []] ) ( [[[old_size new_size] l] v] ) ( ) => arg_old_len arg_ptr arg_new_len local_0 local_align_log2 local_size_of_T local_old_bytes local_new_bytes.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.

  iAssert (x'0 ◁ᵥ{π} .@ uninit (UntypedSynType (mk_array_layout T_st_ly (Z.to_nat (new_size - old_size)))))%I as "Ha".
  { rewrite uninit_own_spec. iExists _.
    { iSplitR.
      { iPureIntro. solve_layout_alg. }
      iPureIntro. rewrite /has_layout_val.
      match goal with | H : x'0 `has_layout_val` _ |- _ => rename H into Hlen end.
      rewrite Hlen.
      solve_goal.
   }
  }
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal.
  all: try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  all: rewrite Nat.mul_comm; by apply array_layout_wf.
Qed.


(** dealloc_array *)
Definition dealloc_array `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) (alloc_dealloc_loc : loc) : function := {|
  f_args := [
    ("len", usize_t : layout);
    ("ptr", void* : layout)
  ];
  f_local_vars := [
    ("__0", use_layout_alg' UnitSynType : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("bytes", usize_t : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      expr: CallE alloc_dealloc_loc [] [] [@{expr} use{IntOp usize_t} "bytes"; use{IntOp usize_t} "align_log2"; use{PtrOp} "ptr"];
      "__0" <-{use_op_alg' UnitSynType} zst_val;
      return (use{use_op_alg' UnitSynType} "__0")
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.


Definition trait_incl_of_dealloc_array `{RRGS : !refinedrustGS Σ} (T_rt: Type) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list Type), (True).
Definition type_of_dealloc_array `{RRGS : !refinedrustGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (size, l) : (Z * loc), (λ ϝ, []);
    size :@: int usize_t, l :@: alias_ptr_t; λ π,
    freeable_nz l (size_of_array_in_bytes T_st (Z.to_nat size)) 1 HeapAlloc ∗
    l ◁ₗ[π, Owned false] .@ (◁ uninit (UntypedSynType (mk_array_layout (use_layout_alg' T_st) (Z.to_nat size)))) ∗
    ⌜(size > 0)%Z⌝ ∗
    ⌜Z.of_nat (size_of_array_in_bytes T_st (Z.to_nat size)) ∈ isize_t⌝ ∗
    ⌜(size_of_st T_st > 0)%Z⌝) →
  ∃ () : unit, () @ unit_t; λ π, True.


Lemma dealloc_array_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc alloc_dealloc_loc : loc) :
  syn_type_is_layoutable T_st →

  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗

  alloc_dealloc_loc ◁ᵥ{π} alloc_dealloc_loc @ function_ptr [IntSynType usize_t; IntSynType usize_t; PtrSynType] (<tag_type> type_of_alloc_dealloc_internal) -∗
  typed_function π (dealloc_array T_st mem_align_log_of_T_loc mem_size_of_T_loc alloc_dealloc_loc) [UnitSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_dealloc_array T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "dealloc_array" ϝ ( () ) ( [T_ty []] ) ( [size l] ) ( ) => arg_len arg_ptr local_0 local_align_log2 local_size_of_T local_bytes.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.
  Unshelve. all: unshelve_sidecond; sidecond_hook.
  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; try (unfold_common_defs; solve_goal); unsolved_sidecond_hook.
  rewrite Nat.mul_comm.
  by apply array_layout_wf.
Qed.

(** check_array_layoutable *)
Definition check_array_layoutable `{!LayoutAlg} (T_st : syn_type) (mem_align_log_of_T_loc : loc) (mem_size_of_T_loc : loc) : function := {|
  f_args := [
    ("len", usize_t : layout)
  ];
  f_local_vars := [
    ("__0", use_layout_alg' BoolSynType : layout);
    ("align_log2", usize_t : layout);
    ("size_of_T", usize_t : layout);
    ("bytes", usize_t : layout);
    ("check", use_layout_alg' BoolSynType : layout)
  ];
  f_code :=
    <["bb0" :=
      "align_log2" <-{ IntOp usize_t } CallE mem_align_log_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "size_of_T" <-{IntOp usize_t} CallE mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ];
      "check" <-{ BoolOp } CheckBinOp MulOp (IntOp usize_t) (IntOp usize_t) (use{IntOp usize_t} "len") (use{IntOp usize_t} "size_of_T");
      if{BoolOp}: (use{BoolOp} "check") then Goto "bb1" else Goto "bb2" ]>%E $
    <["bb1" :=
      (* result fits into usize *)
      "bytes" <-{ IntOp usize_t } ((use{IntOp usize_t} "len") ×c{IntOp usize_t, IntOp usize_t} (use{IntOp usize_t} "size_of_T"));
      "__0" <-{use_op_alg' BoolSynType} ((use{IntOp usize_t} "bytes") ≤{IntOp usize_t, IntOp usize_t, u8} (I2v (MaxInt isize_t) USize));
      return (use{use_op_alg' BoolSynType} "__0")
    ]>%E $
    <["bb2" :=
      (* result does not fit into usize *)
      return (Val (val_of_bool false))
    ]>%E $
    ∅;
  f_init := "bb0";
 |}.


Definition trait_incl_of_check_array_layoutable `{RRGS : !refinedrustGS Σ} (T_rt: Type) (T_st: syn_type) : spec_with _ _ Prop :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list Type), (True).
Definition type_of_check_array_layoutable `{RRGS : !refinedrustGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (size) : (Z), (λ ϝ, []); size :@: int usize_t; λ π, True) →
  ∃ () : unit, (bool_decide (size_of_array_in_bytes T_st (Z.to_nat size) ≤ MaxInt isize_t)%Z) @ bool_t; λ π, True.

Lemma check_array_layoutable_typed `{RRGS : !refinedrustGS Σ} π T_rt (T_st : syn_type) (mem_align_log_of_T_loc mem_size_of_T_loc : loc) :
  syn_type_is_layoutable T_st →
  mem_align_log_of_T_loc ◁ᵥ{π} mem_align_log_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_align_log_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗
  mem_size_of_T_loc ◁ᵥ{π} mem_size_of_T_loc @ function_ptr [] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_mem_size_of T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)) -∗
  typed_function π (check_array_layoutable T_st mem_align_log_of_T_loc mem_size_of_T_loc) [BoolSynType; IntSynType usize_t; IntSynType usize_t; IntSynType usize_t; BoolSynType] (<tag_type>
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
        fn_spec_add_late_pre
        (type_of_check_array_layoutable T_rt T_st <TY> T_ty <INST!>)
        (λ π, typaram_wf T_rt T_st T_ty)).
Proof.
  start_function "check_array_layoutable" ϝ ( () ) ( [T_ty []] ) ( size ) ( ) => arg_len local_0 local_align_log2 local_size_of_T local_bytes local_check.
  init_tyvars (<["T" := existT _ T_ty]> ∅).
  init_lfts ∅.
  repeat liRStep; liShow.

  typed_val_expr_bind.
  repeat liRStep; liShow.
  typed_val_expr_bind.
  repeat liRStep; liShow.
  rewrite /typed_val_expr.
  iIntros (?) "#CTX #HE HL HC".
  iRename select (_ ◁ᵥ{_} size @ int usize_t)%I into "Hv1".
  iRename select (_ ◁ᵥ{_} ly_size T_st_ly @ int usize_t)%I into "Hv2".
  iPoseProof (ty_own_int_in_range with "Hv1") as "%Hsz". destruct Hsz.
  iEval (rewrite /ty_own_val/=) in "Hv1".
  iEval (rewrite /ty_own_val/=) in "Hv2".
  iDestruct "Hv1" as "(%Hsize &_)".
  iDestruct "Hv2" as "(%HTsize & _)".
  iApply (wp_check_int_arithop _ _ _ _ _ _ (bool_decide ((size * ly_size T_st_ly ∈ usize_t)))); [done.. | | ].
  { simpl. rewrite /check_arith_bin_op. simpl. f_equiv.
    rewrite /elem_of/int_elem_of_it/int_elem_of_it' MinInt_eq MaxInt_eq//. }
  iNext. iIntros "_".
  iApply ("HC" $! _ π _ _ (bool_t) with "HL"). { iApply type_val_bool'. }

  repeat liRStep.

  Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
  Unshelve. all: unfold_common_defs; solve_goal.
Qed.
