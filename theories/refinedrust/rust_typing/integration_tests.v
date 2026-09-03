From refinedrust Require Import typing.

Module test.

Lemma effective_unwind_condition_unwind (P : Prop) :
  @effective_unwind_condition panic_unwind_config P ↔ P.
Proof. done. Qed.

Lemma effective_unwind_condition_abort (P : Prop) :
  @effective_unwind_condition panic_abort_config P ↔ False.
Proof. done. Qed.

Lemma effective_unwind_condition_known_abort `{!RadiumConfig} (P : Prop) :
  radium_panic_strategy_of = PanicAbort →
  effective_unwind_condition P → False.
Proof. sidecond_hammer. Qed.

Lemma effective_unwind_condition_generic `{!RadiumConfig} (P : Prop) :
  effective_unwind_condition P →
  P ∧ radium_panic_strategy_of = PanicUnwind.
Proof. sidecond_hammer. Qed.

Definition bla0 `{typeGS Σ} :=
  (fn(∀ ( *[κ'; κ]) : 2 | ( *[]) : [] | (x) : unit, (λ f, [(κ', κ)]); (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; λ π, ⌜ (4 > y)%Z⌝ | False).
Definition bla1 `{typeGS Σ} :=
  (fn(∀ ( *[]) : 0 | ( *[]) : [] | x : unit, (λ _, []); (() :@: (uninit PtrSynType)) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝) | False).
Definition bla2 `{typeGS Σ} :=
  (fn(∀ ( *[]) : 0 | ( *[]) : [] | x : unit, (λ _, []); () :@: (uninit PtrSynType), () :@: (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝) | False).
Definition bla3 `{typeGS Σ} T_st T_rt :=
  (fn(∀ ( *[]) : 0 | ( *[ T_ty]) : [ (T_rt, T_st) ] | (x) : _, (λ _, []); x :@: T_ty, () :@: (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝) | False).

(** Testing exceptional function exits. *)
Program Definition always_unwind : function := {|
  f_args := [("arg", unit_sl)];
  f_code := <["_bb0" := Unwind]>%E $ ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Definition always_unwind_type `{typeGS Σ} :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : unit, (λ _, []);
      () :@: unit_t; (λ _, True)) → ∃ () : unit, () @ unit_t; (λ _, True) | True.

Lemma always_unwind_typed `{!typeGS Σ} π :
  radium_panic_strategy_of = PanicUnwind →
  ⊢ typed_function π always_unwind (<tag_type> always_unwind_type).
Proof.
  intros Hstrategy.
  start_function "always_unwind" ϝ fid ( [] ) ( [] ) ( [] ) ( ).
  repeat liRStep; liShow.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.

Program Definition always_terminate : function := {|
  f_args := [("arg", unit_sl)];
  f_code := <["_bb0" := UnwindTerminate]>%E $ ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Definition always_terminate_type `{typeGS Σ} :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : unit, (λ _, []);
      () :@: unit_t; (λ _, True)) → ∃ () : unit, () @ unit_t; (λ _, True) | False.

Lemma always_terminate_typed `{!typeGS Σ} π :
  ⊢ typed_function π always_terminate (<tag_type> always_terminate_type).
Proof.
  start_function "always_terminate" ϝ fid ( [] ) ( [] ) ( [] ) ( ).
  repeat liRStep; liShow.
  Unshelve. all: try iFrame. all: sidecond_solver.
Qed.

Program Definition always_abort : function := {|
  f_args := [("arg", unit_sl)];
  f_code := <["_bb0" := AbortS]>%E $ ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Definition always_abort_type `{typeGS Σ} :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : unit, (λ _, []);
      () :@: unit_t; (λ _, True)) → ∃ () : unit, () @ unit_t; (λ _, True) | False.

Lemma always_abort_typed `{!typeGS Σ} π :
  ⊢ typed_function π always_abort (<tag_type> always_abort_type).
Proof.
  start_function "always_abort" ϝ fid ( [] ) ( [] ) ( [] ) ( ).
  repeat liRStep; liShow.
  Unshelve. all: try iFrame. all: sidecond_solver.
Qed.

(** Testing type parameter instantiation *)
Program Definition ptr_write `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("dst", void* ); ("src", use_layout_alg' T_st)];
  f_code :=
    <["_bb0" :=
      !{PtrOp} "dst" <-{use_op_alg' T_st} move{use_op_alg' T_st} "src";
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

(* Maybe this should also be specced in terms of value? *)
Definition type_of_ptr_write `{!typeGS Σ} (T_rt : RT) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (l, r) : (loc * _), (λ ϝ, []);
      l :@: alias_ptr_t, r :@: T_ty; λ π, (l ◁ₗ[π, Owned] .@ (◁ uninit (T_ty.(ty_syn_type) MetaNone))))
    → ∃ () : unit, () @ unit_t; λ π,
        l ◁ₗ[π, Owned] (#$# r) @ ◁ T_ty | False.

Lemma ptr_write_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_write T_st) (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
    (fn_spec_add_late_pre (type_of_ptr_write T_rt T_st <TY> T_ty <INST!>) (λ π, typaram_wf T_rt T_st T_ty))).
Proof.
  start_function "ptr_write" ϝ fid ( [] ) ( [T_ty []] ) ( [l r] ) ( ).

  match goal with
  | |- ∀ x : loc, ?P =>
      change (∀ x : name_hint_ty "ls1" loc, P)
  end.

  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: try solve_goal.
Qed.

(** If we specialize the type to [int I32], the proof should still work. *)
Definition type_of_ptr_write_int `{!typeGS Σ} :=
  spec_instantiate_typaram [_] 0 eq_refl (int I32) (type_of_ptr_write Z (IntSynType I32)).
Lemma ptr_write_typed_int `{!typeGS Σ} π :
  ⊢ typed_function π (ptr_write (IntSynType I32)) (<tag_type> type_of_ptr_write_int).
Proof.
  start_function "ptr_write" ϝ fid ( [] ) ( [] ) ( [l r] ) ( ).
  intros ls_dst ls_src.
  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.

(** Same for shared references *)
Definition type_of_ptr_write_shrref `{!typeGS Σ} (U_rt : RT) (U_st : syn_type) :=
  (* First add a new type parameter and a new lifetime *)
  spec! ( *[κ]) : 1 | ( *[U_ty]) : [U_rt],
    (* Then instantiate the existing type parameter with shr_ref U_ty κ *)
    fn_spec_add_late_pre ((type_of_ptr_write (place_rfnRT U_rt) (RefSynType) <TY> shr_ref κ U_ty) <INST!>)
    (λ π, typaram_wf U_rt U_st U_ty)%I
.

Lemma ptr_write_typed_shrref `{!typeGS Σ} π U_rt U_st :
  ⊢ typed_function π (ptr_write RefSynType) (<tag_type> type_of_ptr_write_shrref U_rt U_st).
Proof.
  start_function "ptr_write" ϝ fid ( [ulft_a []]  ) ( [U_ty []] ) ( [l r] ) ( ).

  intros ls_dst ls_src.
  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: try solve_goal.
Qed.

Program Definition ptr_read `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* )];
  f_code :=
    <["_bb0" :=
      local_live{T_st} "tmp";
      local_live{T_st} "bla";
      "tmp" <-{use_op_alg' T_st} copy{use_op_alg' T_st} (!{PtrOp} "src");
      local_dead "bla";
      return (move{use_op_alg' T_st} "tmp")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

Definition type_of_ptr_read `{!typeGS Σ} (T_rt: RT) (T_st: syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) |
      (* params....... *) (src, r) : (_ * _),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, Owned] #($# r) @ ◁ T_ty)
        ∗ (⌜(Copyable T_ty)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, r @ T_ty;
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, Owned] # ($# r) @ ◁ T_ty)) |
      (* unwind post... *) False.

Lemma ptr_read_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_read T_st) (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
    (fn_spec_add_late_pre (type_of_ptr_read T_rt T_st <TY> T_ty <INST!>) (λ π, typaram_wf T_rt T_st T_ty))).
Proof.
  start_function "ptr_read" ϝ fid ( [] ) ( [T_ty []] ) ( [src r] ) ( ).

  repeat liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: try solve_goal.
Qed.

Lemma test_context_fold_none `{!typeGS Σ} π l :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal 4 ks ∧ ks = [l]).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.
Lemma test_context_fold_extract_1 `{!typeGS Σ} π l (κ : lft) :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldExtractAllInit κ) ks ∧ ks = []).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.
Lemma test_context_fold_extract_2 `{!typeGS Σ} π l l2 γ (κ : lft) :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    l2 ◁ₗ[π, Owned] #(#42%Z, γ) @ (◁ mut_ref κ (int i32)) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldExtractAllInit κ) ks ∧ ks = [l2]).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.
Lemma test_context_fold_extract_3 `{!typeGS Σ} π l l2 γ (κ : lft) :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    l2 ◁ₗ[π, Owned] #(#42%Z, γ) @ (MutLtype (◁ int i32) κ) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldExtractAllInit κ) ks ∧ ks = [l2]).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.

Lemma test_context_fold_closeinv_1 `{!typeGS Σ} π l (κ : lft) :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldCloseInvAllInit [κ]) ks ∧ ks = []).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.
Lemma test_context_fold_closeinv_2 `{!typeGS Σ} π l l2 γ (κ : lft) :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    l2 ◁ₗ[π, Owned] #(#42%Z, γ) @ (MutLtype (OpenedLtype (◁ int i32) (◁ int i32) (◁ int i32) (λ _ _, True%I) (λ _ _, True%I)) κ) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldCloseInvAllInit [κ]) ks ∧ ks = [l2]).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.

Lemma test_context_fold_resolve_1 `{!typeGS Σ} π l :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldResolveAllInit) ks ∧ ks = []).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.
Lemma test_context_fold_resolve_2 `{!typeGS Σ} π l l2 γ γ2 (κ : lft) :
  ⊢ l ◁ₗ[π, Owned] #42%Z @ (◁ int i32) -∗
    l2 ◁ₗ[π, Owned] #(👻 γ2, γ) @ (◁ mut_ref κ (int i32)) -∗
    True ∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  liRStep.
  assert (∃ ks : list loc, find_spatial_locs_pure_goal (CtxFoldResolveAllInit) ks ∧ ks = [l2]).
  { eexists. split.
    { solve_find_spatial_locs. }
    reflexivity.
  }
Abort.

Local Lemma test_destruct_hint `{!typeGS Σ} (x : option nat) E L A :
  if_iNone x (False) ∗ if_iSome x (λ x, ⌜x = 5%nat⌝)
  ⊢@{iProp Σ} prove_with_subtype E L false ProveDirect (⌜destruct_hint x (λ x, x = Some 5%nat)⌝) A (λ _ _ _, True).
Proof.
  iStartProof. repeat liRStep.
Qed.

Local Lemma test_name_hint_ex `{!typeGS Σ} (x : option nat) :
   ⊢@{iProp Σ} ⌜name_hint "x" (∃ x : nat, x = 5%nat)⌝ -∗ True ∗ True.
Proof.
  iStartProof.
  repeat liRStep.
Qed.

Local Lemma test_introduce_ex_named `{!typeGS Σ} :
  ⊢ introduce_with_hooks [] [] (∃ foo : nat, ⌜foo = 4%nat⌝) (λ L2, True).
Proof.
  iStartProof.
  liRStep. liRStep.
  rep liRStep.
Qed.
Local Lemma test_introduce_boringly_ex_named `{!typeGS Σ} :
  ⊢ introduce_with_hooks [] [] (☒ ∃ foo : nat, ⌜foo = 4%nat⌝) (λ L2, True).
Proof.
  iStartProof.
  liRStep. liRStep.
  rep liRStep.
Qed.
Local Lemma test_prove_with_subtype_ex `{!typeGS Σ} A :
  ⊢ prove_with_subtype [] [] false ProveDirect (∃ foo : nat, ⌜foo = 4%nat⌝) A (λ L2 _ _, True).
Proof.
  iStartProof.
  liRStep. liRStep.
  liRStep. liRStep.
  rep liRStep.
Qed.
Local Lemma test_introduce_all_named `{!typeGS Σ} :
  ⊢ introduce_with_hooks [] [] (∀ foo : nat, ⌜foo ≥ 0%nat⌝) (λ L2, True).
Proof.
  iStartProof.
  liRStep. liRStep.
  rep liRStep.
Qed.

(** Ghost drop unfolding *)
Lemma test_ghost_drop `{!typeGS Σ} π :
  ⊢ ty_ghost_drop (int I32) π 5 -∗ True.
Proof.
  iStartProof.
  liRStep.
  liRStep.
  liRStep.
  done.
Abort.
Lemma test_ghost_drop `{!typeGS Σ} {rt} (ty : type rt) r π :
  ⊢ ty_ghost_drop ty π r -∗ True.
Proof.
  iStartProof.
  liRStep.
  done.
Abort.

Section test.
  Context `{!typeGS Σ}.

  (* The subtype of positive integers *)
  Local Definition P_a := λ (x : Z) (y : Z), (∃ z : Z, ⌜x = (y + z)%Z⌝ ∗ ⌜(0 < x)%Z⌝)%I : iProp Σ.
  Local Program Definition Pdef := mk_pers_ex_inv_def P_a true _ _ _.
  Next Obligation. intros. iIntros "$". iPureIntro. intros _. eexists. done. Qed.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_t_solve_timeless. Qed.
  Local Definition Pty := (∃; Pdef, int I32)%I.

  Local Lemma Pty_copy : Copyable Pty.
  Proof. apply _. Qed.

  Local Definition P_b := λ (π : thread_id) (x : Z) (y : Z), (∃ (z : Z) (l : loc), ⌜x = (y + z)%Z⌝ ∗ ⌜(0 < x)%Z⌝ ∗ guarded true (l ◁ₗ[π, Owned] #42%Z @ (◁ int I32)))%I : iProp Σ.
  Local Definition S_b := λ (π : thread_id) (κ : lft) (x : Z) (y : Z), (∃ (z : Z) (l : loc), ⌜x = (y + z)%Z⌝ ∗ ⌜(0 < x)%Z⌝ ∗ guarded false (l ◁ₗ[π, Shared κ] #42%Z @ (◁ int I32)))%I : iProp Σ.

  Local Program Definition Adef := mk_ex_inv_def_auto_ghost_drop P_b S_b _ false _ [] [] _ _ _.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_plain_t_solve_is_xrfn. Qed.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. rewrite /S_b. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. rewrite /P_b /S_b. ex_plain_t_solve_shr. Qed.

  Local Program Definition Bdef := mk_auto_ex_inv_def P_b false _ [] [] _ _ _ _.
  Next Obligation. ex_plain_t_solve_is_xrfn. Qed.
  Next Obligation. ex_plain_t_solve_shr_auto. Defined.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
End test.


Section enum.
Context `{!typeGS Σ}.
(* Example enum spec: option *)
Section std_option_Option_els.
  Definition std_option_Option_None_sls  : struct_layout_spec := mk_sls "std_option_Option_None" [] StructReprRust.

  Definition std_option_Option_Some_sls T_st : struct_layout_spec := mk_sls "std_option_Option_Some" [
    ("0", T_st)] StructReprRust.

  Program Definition std_option_Option_els (T_st : syn_type): enum_layout_spec := mk_els "std_option_Option" ISize [
    ("None", std_option_Option_None_sls  : syn_type);
    ("Some", std_option_Option_Some_sls T_st : syn_type)] EnumReprRust [("None", 0); ("Some", 1)] _ _ _ _.
  Next Obligation.  solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation.  solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.

Global Typeclasses Opaque std_option_Option_els.
End std_option_Option_els.
(* maybe we should represent this with a gmap for easy lookup? *)

Section std_option_Option_ty.
  Context {T_rt : RT}.
  Context (T_ty : type (T_rt)).

  Definition std_option_Option_None_ty : type (plist place_rfnRT [] : RT) := struct_t std_option_Option_None_sls +[].
  Definition std_option_Option_None_rt : RT := rt_of std_option_Option_None_ty.
  Global Typeclasses Transparent std_option_Option_None_ty.

  Definition std_option_Option_Some_ty : type (plist place_rfnRT [T_rt : RT]) := struct_t (std_option_Option_Some_sls (ty_syn_type T_ty MetaNone)) +[
    T_ty].
  Definition std_option_Option_Some_rt : RT := rt_of std_option_Option_Some_ty.
  Global Typeclasses Transparent std_option_Option_Some_ty.

  Definition std_option_Option_enum_rt := (λ rfn : (option (place_rfnRT T_rt)), match rfn with | None => std_option_Option_None_rt | Some x => std_option_Option_Some_rt end).
  Definition std_option_Option_enum_ty : ∀ x, type (std_option_Option_enum_rt x) := (λ rfn, match rfn with | None => std_option_Option_None_ty | Some x => std_option_Option_Some_ty end).
  Program Definition std_option_Option_enum : enum (option (place_rfnRT T_rt)) := mk_enum
    _
    ((std_option_Option_els (ty_syn_type T_ty MetaNone)))
    (λ rfn, match rfn with | None => Some "None" | Some x => Some "Some" end)
    std_option_Option_enum_rt
    std_option_Option_enum_ty
    (λ rfn, match rfn with | None => -[] | Some x => -[x] end)
    ([("None", mk_enum_tag_sem _ std_option_Option_None_ty (λ _, None)); ("Some", mk_enum_tag_sem _ std_option_Option_Some_ty (λ '( *[x]), Some x))])
    _
    _
    _
  .
  Next Obligation.
    solve_inhabited.
  Defined.
  Next Obligation.
    solve_enum_is_xrfn_congr.
  Qed.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    solve_mk_enum_tag_consistent.
  Defined.
  Next Obligation.
    solve_mk_enum_tag_inj_roundtrip.
  Defined.

  Definition std_option_Option_ty : type _ := enum_t std_option_Option_enum.
  Global Typeclasses Transparent std_option_Option_ty.
End std_option_Option_ty.

  Example option_none_ghost_drop_can_simplify {T_rt : RT} (T_ty : type T_rt) :
    TyGhostDropCanSimplify (std_option_Option_ty T_ty) None.
  Proof. apply _. Qed.

  Example option_some_ghost_drop_can_simplify {T_rt : RT} (T_ty : type T_rt) (x : T_rt) :
    TyGhostDropCanSimplify (std_option_Option_ty T_ty) (Some (#x)).
  Proof. apply _. Qed.

  Goal ∀ {T_rt : RT} (T_ty : type T_rt) (r : option (place_rfnRT T_rt)),
    TyGhostDropCanSimplify (std_option_Option_ty T_ty) r.
  Proof.
    intros. Fail apply _.
  Abort.

  Goal ∀ b : bool, IsConcreteEnumTag (if b then "Some" else "None").
  Proof.
    intros. Fail apply _.
  Abort.

  Lemma option_owned_subtype_none_infer π E L {rt1 rt2}
      (ty1 : type rt1) (ty2 : type rt2) :
    ty_syn_type ty1 MetaNone = ty_syn_type ty2 MetaNone →
    ⊢ ∃ r2 : option (place_rfnRT rt2),
      owned_subtype π E L false None r2
        (std_option_Option_ty ty1) (std_option_Option_ty ty2)
        (λ _, ⌜r2 = None⌝ ∗ True).
  Proof.
    intros Hst. iStartProof. repeat liRStep.
    Unshelve. all: unfold fast_syntype_eq_hint; by rewrite Hst.
  Qed.

  Lemma option_weak_subtype_some_infer E L {rt} (ty : type rt)
      (x : rt) :
    ⊢ ∃ r2 : option (place_rfnRT rt),
      weak_subtype E L (Some (#x)) r2
        (std_option_Option_ty ty) (std_option_Option_ty ty)
        (⌜r2 = Some (#x)⌝ ∗ True).
  Proof.
    iStartProof. repeat liRStep.
    Unshelve. all: sidecond_solver.
  Qed.

  Lemma option_weak_subtype_symbolic_infer E L {rt} (ty : type rt)
      (r : option (place_rfnRT rt)) :
    ⊢ ∃ r2 : option (place_rfnRT rt),
      weak_subtype E L r r2
        (std_option_Option_ty ty) (std_option_Option_ty ty)
        (⌜r2 = r⌝ ∗ True).
  Proof.
    iStartProof. repeat liRStep.
    Unshelve. all: sidecond_solver.
  Qed.

  Lemma option_mut_subtype_shared E L {rt} (ty : type rt) κ1 κ2 :
    ⌜lctx_lft_incl E L κ2 κ1⌝ ⊢
      mut_subtype E L
        (std_option_Option_ty (shr_ref κ1 ty))
        (std_option_Option_ty (shr_ref κ2 ty)) True.
  Proof.
    iIntros "%Hincl". repeat liRStep.
    Unshelve. all: intros []; eexists; done.
  Qed.

  (* The unique place condition permits a blocked payload, although that
     payload cannot yet be fully folded back to its type. *)
  Lemma option_prove_uniq_blocked_payload E L {rt} (ty : type rt) κ :
    lctx_place_update_kind_outlives E L (UpdUniq [κ]) [κ] →
    ⊢ prove_place_cond E L (UpdUniq [κ])
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _ (OfTy (std_option_Option_Some_ty ty)) None)))
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _
          (BlockedLtype (std_option_Option_Some_ty ty) κ) None)))
      (λ upd, ⌜upd.(puk_res_k) = UpdUniq [κ]⌝ ∗ True).
  Proof.
    intros Hout. iStartProof. repeat liRStep.
  Qed.

  Lemma option_prove_uniq_blocked_payload_canonical E L {rt} (ty : type rt) κ :
    lctx_place_update_kind_outlives E L (UpdUniq [κ]) [κ] →
    ⊢ prove_place_cond E L (UpdUniq [κ])
      (EnumLtype (std_option_Option_enum ty) None)
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _
          (BlockedLtype (std_option_Option_Some_ty ty) κ) None)))
      (λ upd, ⌜upd.(puk_res_k) = UpdUniq [κ]⌝ ∗ True).
  Proof.
    intros Hout. iStartProof. repeat liRStep.
  Qed.

  Lemma option_prove_uniq_blocked_payload_ofty E L {rt} (ty : type rt) κ :
    lctx_place_update_kind_outlives E L (UpdUniq [κ]) [κ] →
    ⊢ prove_place_cond E L (UpdUniq [κ])
      (OfTy (std_option_Option_ty ty))
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _
          (BlockedLtype (std_option_Option_Some_ty ty) κ) None)))
      (λ upd, ⌜upd.(puk_res_k) = UpdUniq [κ]⌝ ∗ True).
  Proof.
    intros Hout. iStartProof. repeat liRStep.
  Qed.

  (* Exercise rule selection and closing with a different payload refinement,
     then fold the resulting enum through the registered cast rule. *)
  Definition option_uniq_update_cont {rt} (ty : type rt) (y : rt) κ :
      place_cont_t (option (place_rfnRT rt)) UpdStrong :=
    (λ L' _ _ _ bmin rti lti _ updcx,
      ∃ Heq : std_option_Option_Some_rt ty = rti,
      updcx L' (mkPUpd _ bmin rti lti
        (eq_rect (std_option_Option_Some_rt ty) (λ rt : RT, place_rfn rt) (#(-[#y])) _ Heq)
        True (UpdUniq [κ]) opt_place_update_eq_refl opt_place_update_eq_refl)
        (λ upd, ∃ Hout : (option (place_rfnRT rt) : RT) = upd.(pupd_rt),
          ⌜upd.(pupd_rfn) = eq_rect _ (λ rt : RT, place_rfn rt) (#(Some (#y))) _ Hout⌝ ∗
          ⌜upd.(pupd_performed) = UpdUniq [κ]⌝ ∗
          cast_ltype_to_type [] [] upd.(pupd_lt) (λ _, True)))%I.
  Arguments option_uniq_update_cont _ _ _ /.

  Lemma option_uniq_override_update E L L' κs f l {rt} (ty : type rt) (x y : rt) κ γ :
    lctx_lft_alive_count E L κ κs L' →
    ⊢ typed_place E L f l
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _ (OfTy (std_option_Option_Some_ty ty)) None)))
      (#(Some (#x))) UpdStrong (Uniq κ γ)
      [EnumDataPCtx (std_option_Option_els (ty_syn_type ty MetaNone)) "Some"]
      (option_uniq_update_cont ty y κ).
  Proof.
    intros Hal. iStartProof. repeat liRStep.
  Qed.

  Lemma option_uniq_canonical_update E L L' κs f l {rt} (ty : type rt) (x y : rt) κ γ :
    lctx_lft_alive_count E L κ κs L' →
    ⊢ typed_place E L f l (EnumLtype (std_option_Option_enum ty) None)
      (#(Some (#x))) UpdStrong (Uniq κ γ)
      [EnumDataPCtx (std_option_Option_els (ty_syn_type ty MetaNone)) "Some"]
      (option_uniq_update_cont ty y κ).
  Proof.
    intros Hal. iStartProof. repeat liRStep.
  Qed.

  (* A strong payload update cannot be reflected through the unique enum
     contract, so the enum is returned as an OpenedLtype at its old outer
     refinement. *)
  Definition option_uniq_open_cont {rt} (ty : type rt) (x y : rt) :
      place_cont_t (option (place_rfnRT rt)) UpdStrong :=
    (λ L' _ _ _ bmin rti lti _ updcx,
      ∃ Heq : std_option_Option_Some_rt ty = rti,
      updcx L' (mkPUpd _ bmin rti lti
        (eq_rect (std_option_Option_Some_rt ty) (λ rt : RT, place_rfn rt) (#(-[#y])) _ Heq)
        True UpdStrong I opt_place_update_eq_refl)
        (λ upd, ∃ Hout : (option (place_rfnRT rt) : RT) = upd.(pupd_rt),
          ⌜upd.(pupd_rfn) = eq_rect _ (λ rt : RT, place_rfn rt) (#(Some (#x))) _ Hout⌝ ∗
          ⌜upd.(pupd_performed) = UpdStrong⌝ ∗ True))%I.
  Arguments option_uniq_open_cont _ _ _ /.

  Lemma option_uniq_override_open E L L' κs f l {rt} (ty : type rt) (x y : rt) κ γ :
    lctx_lft_alive_count E L κ κs L' →
    ⊢ typed_place E L f l
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _ (OfTy (std_option_Option_Some_ty ty)) None)))
      (#(Some (#x))) UpdStrong (Uniq κ γ)
      [EnumDataPCtx (std_option_Option_els (ty_syn_type ty MetaNone)) "Some"]
      (option_uniq_open_cont ty x y).
  Proof.
    intros Hal. iStartProof. repeat liRStep.
  Qed.

  Lemma option_uniq_canonical_open E L L' κs f l {rt} (ty : type rt) (x y : rt) κ γ :
    lctx_lft_alive_count E L κ κs L' →
    ⊢ typed_place E L f l (EnumLtype (std_option_Option_enum ty) None)
      (#(Some (#x))) UpdStrong (Uniq κ γ)
      [EnumDataPCtx (std_option_Option_els (ty_syn_type ty MetaNone)) "Some"]
      (option_uniq_open_cont ty x y).
  Proof.
    intros Hal. iStartProof. repeat liRStep.
  Qed.

  Lemma option_stratify_owned_explicit_normalize π E L l {rt}
      (ty : type rt) (x y : rt) :
    ⊢ stratify_ltype π E L StratNoUnfold StratNoRefold StratifyUnblockOp l
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _
          (OfTy (std_option_Option_Some_ty ty)) (Some (-[#y])))))
      (#(Some (#x))) Owned
      (λ L2 _ rt2 lt2 r2,
        cast_ltype_to_type E L2 lt2 (λ ty2,
          ∃ Hout : (option (place_rfnRT rt) : RT) = rt2,
            ⌜ty2 = eq_rect _ type (std_option_Option_ty ty) _ Hout⌝ ∗
            ⌜r2 = eq_rect _ (λ rt : RT, place_rfn rt)
              (#(Some (#y))) _ Hout⌝ ∗ True)).
  Proof.
    iStartProof. repeat liRStep.
  Qed.

  Lemma option_stratify_owned_ofty π E L l {rt}
      (ty : type rt) (x : rt) :
    ⊢ stratify_ltype π E L StratDoUnfold StratNoRefold StratifyUnblockOp l
      (OfTy (std_option_Option_ty ty)) (#(Some (#x))) Owned
      (λ L2 _ rt2 lt2 r2,
        cast_ltype_to_type E L2 lt2 (λ ty2,
          ∃ Hout : (option (place_rfnRT rt) : RT) = rt2,
            ⌜ty2 = eq_rect _ type (std_option_Option_ty ty) _ Hout⌝ ∗
            ⌜r2 = eq_rect _ (λ rt : RT, place_rfn rt)
              (#(Some (#x))) _ Hout⌝ ∗ True)).
  Proof.
    iStartProof.
    rep liRStep.
  Qed.

  Lemma option_stratify_uniq_refold π E L L' κs l {rt}
      (ty : type rt) (x : rt) κ γ :
    lctx_lft_alive_count E L κ κs L' →
    ⊢ stratify_ltype π E L StratNoUnfold StratRefoldFull StratifyUnblockOp l
      (EnumLtype (std_option_Option_enum ty)
        (Some (mk_enum_ltype_variant "Some" _
          (OfTy (std_option_Option_Some_ty ty)) None)))
      (#(Some (#x))) (Uniq κ γ)
      (λ _ _ _ _ _, True).
  Proof.
    intros Hal. iStartProof. repeat liRStep.
  Qed.

  Lemma option_stratify_uniq_canonical π E L L' κs l {rt}
      (ty : type rt) (x : rt) κ γ :
    lctx_lft_alive_count E L κ κs L' →
    ⊢ stratify_ltype π E L StratNoUnfold StratNoRefold StratifyUnblockOp l
      (EnumLtype (std_option_Option_enum ty) None)
      (#(Some (#x))) (Uniq κ γ)
      (λ _ _ _ _ _, True).
  Proof.
    intros Hal. iStartProof. rep liRStep.
  Qed.

  Lemma alias_stratify_owned_no_refold π E L l l2 rt st r :
    ⊢ stratify_ltype π E L StratNoUnfold StratNoRefold StratifyUnblockOp l
      (AliasLtype rt st l2) r Owned
      (λ _ _ rt' lt' _, ∃ Heq : rt = rt',
        ⌜lt' = eq_rect rt ltype (AliasLtype rt st l2) rt' Heq⌝).
  Proof.
    iStartProof. liRStep. iExists eq_refl. done.
  Qed.

  Lemma addr_of_mut_opened_uniq_keeps_alias_current π E L l
      {rt_cur rt_inner rt_full}
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r κ γ :
    ⊢ typed_addr_of_mut_end PRaw π E L l
      (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Uniq κ γ) UpdStrong
      (λ _ _ _ _ rt' lt' _ rt_moved lt_moved _,
        ∃ Heq : rt_cur = rt',
          ⌜lt' = eq_rect rt_cur ltype
            (OpenedLtype (AliasLtype rt_cur (ltype_st lt_cur) l)
              lt_inner lt_full Cpre Cpost) rt' Heq⌝ ∗
        ∃ Heq_moved : rt_cur = rt_moved,
          ⌜lt_moved = eq_rect rt_cur ltype lt_cur rt_moved Heq_moved⌝).
  Proof.
    iStartProof. liRStep.
    iExists eq_refl. iSplit; first done. iExists eq_refl. done.
  Qed.

  Instance option_contr {rt1 T_rt} (T : type rt1 → type T_rt) :
    TypeContractive T →
    TypeContractive (λ ty, std_option_Option_ty (T ty)).
  Proof.
    intros ?.
    apply enum_t_contr.
    unshelve econstructor.
    - enum_contractive_solve_eq.
    - intros. simpl. by erewrite type_ctr_syn_type.
    - enum_contractive_solve_eq.
    - enum_contractive_solve_eq.
    - intros. Arguments enum_ty : simpl never. simpl.
      admit.
    - admit.
    - solve_enum_t_contr_op_type.
  Abort.
  Global Instance option_ne {rt1 T_rt} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, std_option_Option_ty (T ty)).
  Proof.
    intros ?.
    apply enum_t_ne.
    unshelve econstructor.
    - enum_contractive_solve_eq.
    - intros. simpl. by erewrite type_ne_syn_type.
    - enum_contractive_solve_eq.
    - enum_contractive_solve_eq.
    - intros. simpl.
      (*eapply (type_dist_use_ne _ _ _ (λ ty, enum_ty (Option_enum -[] -[T ty]) r)); last done.*)
      (*destruct r; simpl.*)
      (*+ apply struct_t_ne; last apply _.*)
        (*intros. by erewrite type_ne_syn_type.*)
      (*+ apply _.*)
      admit.
    - intros. simpl.
      (*eapply (type_dist2_use_ne _ _ _ (λ ty, enum_ty (Option_enum -[] -[T ty]) r)); last done.*)
      (*destruct r; simpl.*)
      (*+ apply struct_t_ne; last apply _.*)
        (*intros. by erewrite type_ne_syn_type.*)
      (*+ apply _.*)
      admit.
    - solve_enum_t_ne_op_type.
  Abort.
End enum.
End test.

Section test_struct.
  Context `{!typeGS Σ}.

  Definition test_rt : list RT := [Z: RT; Z : RT].
  Definition test_lts : hlist ltype test_rt := (◁ int I32)%I +:: (◁ int I32)%I +:: +[].
  Definition test_rfn : plist place_rfnRT test_rt := #32 -:: #22 -:: -[].

  Lemma bla : hnth (UninitLtype UnitSynType) test_lts 1 = (◁ int I32)%I.
  Proof. simpl. done. Abort.
  Lemma bla : pnth (#()) test_rfn 1 = #22.
  Proof. simpl. done. Abort.

  Lemma bla : hlist_insert_id (unit : RT) _ test_lts 1 (◁ int I32)%I = test_lts.
  Proof.
    simpl. rewrite /hlist_insert_id. simpl.
    (*rewrite /list_insert_lnth. *)
    (*generalize (list_insert_lnth test_rt unit 1).*)
    (*simpl. intros ?. rewrite (UIP_refl _ _ e). done.*)
  Abort.

  Lemma bla : hlist_insert _ test_lts 1 _ (◁ int I32)%I = test_lts.
  Proof.
    simpl. done.
  Abort.

  Lemma bla : plist_insert _ test_rfn 1 _ (#22) = test_rfn.
  Proof.
    simpl. done.
  Abort.

  Lemma bla : plist_insert_id (unit : RT) _ test_rfn 1 (#22) = test_rfn.
  Proof.
    simpl. cbn. done.
    (*rewrite /plist_insert_id. cbn. *)
    (*generalize (list_insert_lnth test_rt unit 1).*)
    (*simpl. intros ?. rewrite (UIP_refl _ _ e). done.*)
  Abort.

  (* Options:
     - some simplification machinery via tactic support
        li_tactic. should just rewrite a bit.
     - some simplification machinery via SimplifyHyp instances or so?
        not the right way to do it. Rather specialized SimplifyHypVal or so.
     - some simplification machinery via a new SimplifyLtype thing and have rules for judgments for that?
        How do we capture a progress condition? via .. try to simplify, then require that it is Some. This is like SimplifyHyp
       This seems unnecessarily expensive, since we usually need not be able to do it.


   *)
End test_struct.

Section test_box.
  Context `{RRGS : !typeGS Σ}.

  Section Box_ty.
    Definition Box_sls (T_st: syn_type) : struct_layout_spec :=
      let Box_st (T_st: syn_type) := UnitSynType in
      mk_sls "Box" [
      ("0", (PtrSynType : syn_type))] StructReprRust.
    Definition Box_st (T_st: syn_type) : syn_type := Box_sls T_st.

    Context (T_rt : RT).

    Definition Box_ty : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [loc : RT])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (Box_sls ((T_ty.(ty_syn_type) (MetaNone))) ) +[alias_ptr_t]))).
    Defined.

    Definition Box_rt  : RT.
    Proof using T_rt.
      let __a := (normalized_rt_of_spec_ty (Box_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent Box_ty.
    #[global] Typeclasses Transparent Box_rt.
  End Box_ty.
  Global Arguments Box_rt : clear implicits.
  Section Box_inv_t.
    Context (T_rt : RT).

    Program Definition Box_inv_t_inv_spec  : spec_with 0 [T_rt] (ex_inv_def ((Box_rt (T_rt)))%type ((place_rfn (T_rt)))%type) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_ex_inv_def_auto_shr
      (λ π inner_rfn (_ty_rfn : RT_rt ((place_rfn (T_rt))%type : RT)),
              let 'x := _ty_rfn in ∃ (l: name_hint_ty "l" ((loc))%Z) , ⌜inner_rfn = -[#(l)]⌝ ∗ guarded true (l ◁ₗ[π, Owned] x @ ◁ T_ty) ∗ True)%I
      (λ π _ (_rfn_binder : RT_rt ((place_rfn (T_rt))%type : RT)),
              let 'x := _rfn_binder in (∃ r, place_rfn_interp_owned x r ∗ ty_ghost_drop T_ty π r) ∗ True)%I
      (false)
      _
      ([] ++ ty_lfts T_ty)
      ([] ++ ty_wf_E T_ty)
      _ _ _ _
    .
    Next Obligation. ex_plain_t_solve_is_xrfn. Qed.
    Next Obligation. ex_plain_t_solve_shr_auto. Defined.
    Next Obligation. ex_t_solve_persistent. Qed.
    Next Obligation. intros ?; ex_plain_t_solve_shr_mono. Qed.
    Next Obligation. intros ?; ex_plain_t_solve_ghost_drop. Qed.

    Definition Box_inv_t  : spec_with 0 [T_rt] (type ((place_rfn (T_rt)))%type) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (Box_inv_t_inv_spec -[] -[T_ty]) (((Box_ty (T_rt) )) -[] -[T_ty]).
  Global Arguments Box_inv_t_inv_spec : simpl never.
  Global Arguments Box_inv_t : simpl never.
    Global Typeclasses Transparent Box_inv_t.
    Definition Box_inv_t_rt : RT.
    Proof using T_rt . let __a := normalized_rt_of_spec_ty Box_inv_t in exact __a. Defined.
    Global Typeclasses Transparent Box_inv_t_rt.
  End Box_inv_t.
  Global Arguments Box_inv_t_rt : clear implicits.


  Global Instance Box_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, Box_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper_prepare.
        repeat solve_proper_step.
      + solve_proper_prepare.
        repeat solve_proper_step.
    - cbn; apply _.
  Qed.
  Global Instance Box_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, Box_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.

  Global Program Instance Box_inv_t_dep_lft_mor rts (rt : RT) (T : mut_types rts → type rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, Box_inv_t rt *[] *[(T x)]) :=
    λ Ht,
      dep_lft_morph_make_id _ _ _ Ht _ _.
  Next Obligation.
    intros. rewrite /lifecycle_lfts/=.
    repeat rewrite !ty_lfts_unfold/=.
    rewrite right_id//.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    rewrite right_id//.
  Qed.
End test_box.

Section test_rectypes.
  Context `{!typeGS Σ}.

  Local Program Definition unit_abs_inv {X : RT} : ex_inv_def X unitRT :=
    mk_ex_inv_def (λ _ x _, ⌜is_xrfn x⌝)%I (λ _ _ x _, ⌜is_xrfn x⌝)%I (λ _ _ _, True)%I
      true _ [] [] _ _ _ _.
  Next Obligation.
    intros. iIntros "%Hxr". iSplit; first done.
    iPureIntro. intros _. exact Hxr.
  Qed.
  Next Obligation. intros. unfold TCNoResolve. apply _. Qed.
  Next Obligation. eauto. Qed.
  Next Obligation.
    simpl. intros X F tid κ x y q ?.
    intros _.
    iIntros "#CTX _ Htok Hxr". iDestruct "CTX" as "(LFT & LLCTX)".
    iApply fupd_logical_step. rewrite right_id.
    iMod (bor_persistent with "LFT Hxr Htok") as "(>Hxr & Htok)"; first done.
    iApply logical_step_intro. iFrame.
    iModIntro. done.
  Qed.
  Next Obligation.
    simpl. intros X F tid x y ? ?.
    iIntros "_".
    iApply logical_step_intro. done.
  Qed.

  Local Definition Boo_sls : struct_layout_spec :=
    mk_sls "Boo" [("x", PtrSynType)] StructReprRust.

  Local Definition Boo_rts : list RT := [unitRT].

  Local Definition Boo_F (tys : mut_types Boo_rts) : mut_types Boo_rts :=
    let Boo_ty := mut_type_project tys 0 eq_refl in
    let Boo_inner := struct_t Boo_sls +[
      Box_inv_t unitRT -[] -[Boo_ty]] in
    ex_plain_t _ _ unit_abs_inv Boo_inner +::
    +[].

  Program Definition Boo_tys : mut_types Boo_rts :=
    @mut_fixpoint _ _ _ Boo_F _ _ _.
  Next Obligation. solve_fixpoint_ne. Qed.
  Next Obligation. solve_fixpoint_contr. Qed.
End test_rectypes.

Section rectypes_List_ty.
  Context `{RRGS : !(typeGS Σ)}.

  Section rectypes_List_els.

    Definition rectypes_List_Nil_sls (T_st: syn_type) : struct_layout_spec :=
      let rectypes_List_Nil_st (T_st: syn_type) := UnitSynType in
      let rectypes_List_st (T_st: syn_type) := UnitSynType in
      mk_sls "rectypes_List_Nil" [] StructReprRust.
    Definition rectypes_List_Nil_st (T_st: syn_type) : syn_type := rectypes_List_Nil_sls T_st.

    Definition rectypes_List_Cons_sls (T_st: syn_type) : struct_layout_spec :=
      let rectypes_List_Cons_st (T_st: syn_type) := UnitSynType in
      let rectypes_List_st (T_st: syn_type) := UnitSynType in
      mk_sls "rectypes_List_Cons" [
      ("0", T_st);
      ("1", ((Box_sls ((rectypes_List_st (T_st))) ) : syn_type))] StructReprRust.
    Definition rectypes_List_Cons_st (T_st: syn_type) : syn_type := rectypes_List_Cons_sls T_st.

    Program Definition rectypes_List_els (T_st: syn_type) : enum_layout_spec := mk_els "rectypes_List" ISize [
      ("Nil", rectypes_List_Nil_st (T_st: syn_type));
      ("Cons", rectypes_List_Cons_st (T_st: syn_type))] EnumReprRust [("Nil", 0); ("Cons", 1)] _ _ _ _.
    Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
    Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
    Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
    Next Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
    Global Typeclasses Opaque rectypes_List_els.
    Definition rectypes_List_st (T_st: syn_type) : syn_type := rectypes_List_els T_st.
  End rectypes_List_els.

  Context {T_rt : RT}.
  Section components.
    Let rectypes_List_rt (_T_rt : RT) := (list (place_rfn (T_rt))).
    Context (_rectypes_List_ty : type (list (place_rfn (T_rt)))).
    Let rectypes_List_ty (T_rt : RT) := spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), _rectypes_List_ty.

    Definition rectypes_List_Nil_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [])))).
    Proof using _rectypes_List_ty.
      exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (rectypes_List_Nil_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[]))).
    Defined.

    Definition rectypes_List_Nil_rt  : RT.
    Proof using T_rt .
      let __a := (normalized_rt_of_spec_ty (rectypes_List_Nil_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent rectypes_List_Nil_ty.
    #[global] Typeclasses Transparent rectypes_List_Nil_rt.
    Definition rectypes_List_Cons_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [(T_rt) : RT; ((((Box_inv_t_rt)) (((rectypes_List_rt ((T_rt))))) )) : RT])))).
    Proof using _rectypes_List_ty.
      exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((struct_t (rectypes_List_Cons_sls ((T_ty.(ty_syn_type) (MetaNone)))) +[(T_ty); ((Box_inv_t (((rectypes_List_rt ((T_rt)))))  -[] -[(rectypes_List_ty ((T_rt)) -[] -[T_ty])]))]))).
    Defined.

    Definition rectypes_List_Cons_rt  : RT.
    Proof using T_rt .
      let __a := (normalized_rt_of_spec_ty (rectypes_List_Cons_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent rectypes_List_Cons_ty.
    #[global] Typeclasses Transparent rectypes_List_Cons_rt.
    Program Definition rectypes_List_Cons_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def (rectypes_List_Cons_rt)%type (((place_rfn (T_rt)) * (list (place_rfn (T_rt)))))%type))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
            (λ π inner_rfn (_ty_rfn : RT_rt (((place_rfn (T_rt)) * (list (place_rfn (T_rt))))%type : RT)),
                    let '(x, xs) := _ty_rfn in ⌜(inner_rfn : RT_rt rectypes_List_Cons_rt)  = -[(x); #(#xs)]⌝ ∗ True)%I
            (true)
            _
            ([])
            ([])
            _ _ _ _
          .
    Next Obligation.
      ex_plain_t_solve_is_xrfn.
    Qed.
    Next Obligation.
      ex_plain_t_solve_shr_auto.
    Defined.

    Next Obligation.
      ex_plain_t_solve_ghost_drop_auto.
    Defined.

    Next Obligation.
      ex_t_solve_persistent.
    Qed.

    Next Obligation.
      ex_plain_t_solve_shr_mono.
    Qed.

    Definition rectypes_List_Cons_inv_t  : (spec_with 0 [(T_rt)] ((type ((((place_rfn (T_rt)) * (list (place_rfn (T_rt)))))%type)))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (rectypes_List_Cons_inv_t_inv_spec  -[] -[T_ty]) (rectypes_List_Cons_ty -[] -[T_ty]).
    #[global] Arguments rectypes_List_Cons_inv_t_inv_spec : simpl never.

    #[global] Arguments rectypes_List_Cons_inv_t : simpl never.

    #[global] Typeclasses Transparent rectypes_List_Cons_inv_t.
    Definition rectypes_List_Cons_inv_t_rt  : RT.
    Proof using T_rt .
      let __a := (normalized_rt_of_spec_ty (rectypes_List_Cons_inv_t)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent rectypes_List_Cons_inv_t_rt.

    Definition rectypes_List_enum_rt  :=
      λ rfn : (list (place_rfn (T_rt))), match rfn with | [] => rectypes_List_Nil_rt| (cons (x) (xs)) => rectypes_List_Cons_inv_t_rt end.
    Definition rectypes_List_enum_ty  : (spec_with 0 [(T_rt)] (∀ (x: _), (type (rectypes_List_enum_rt (x))))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), λ rfn, match rfn as x return type (rectypes_List_enum_rt x) with | [] => rectypes_List_Nil_ty -[] -[T_ty]| (cons (x) (xs)) => rectypes_List_Cons_inv_t -[] -[T_ty] end.
    Program Definition rectypes_List_enum_pre  : (spec_with 0 [(T_rt)] ((enum ((list (place_rfn (T_rt))))))) :=
      spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_enum
        _
        ((rectypes_List_els ((ty_syn_type T_ty MetaNone))))
        (λ rfn, Some (match rfn with | [] => "Nil" | (cons (x) (xs)) => "Cons" end))
        (rectypes_List_enum_rt)
        (rectypes_List_enum_ty -[] -[T_ty])
        (λ rfn, match rfn with | [] => *[]| (cons (x) (xs)) => (x, xs) end)
        ([("Nil", mk_enum_tag_sem _ (rectypes_List_Nil_ty -[] -[T_ty]) (λ '( *[]), [])); ("Cons", mk_enum_tag_sem _ (rectypes_List_Cons_inv_t -[] -[T_ty]) (λ '( (x, xs)), (cons (x) (xs))))])
        _
        _
        _.
    Next Obligation.
      solve_inhabited.
    Defined.
    Next Obligation.
      solve_enum_is_xrfn_congr.
    Qed.
    Next Obligation.
      done.
    Qed.
    Next Obligation.
      solve_mk_enum_tag_consistent.
    Defined.
    Next Obligation.
      solve_mk_enum_tag_inj_roundtrip.
    Defined.

    #[global] Arguments rectypes_List_enum_pre : simpl never.

  End components.

  Arguments enum_ty : simpl never.

  Definition rectypes_List_ty  : (spec_with 0 [(T_rt)] ((type _))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), type_fixpoint (λ rectypes_List_ty, enum_t (rectypes_List_enum_pre rectypes_List_ty -[] -[T_ty])).
  Definition rectypes_List_rt  : RT.
  Proof using T_rt.
    let __a := (normalized_rt_of_spec_ty (rectypes_List_ty)) in exact __a.
  Defined.

  Definition rectypes_List_enum  : (spec_with 0 [(T_rt)] ((enum ((list (place_rfn (T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), rectypes_List_enum_pre (rectypes_List_ty -[] -[T_ty]) -[] -[T_ty].
  #[global] Typeclasses Transparent rectypes_List_ty.
  #[global] Typeclasses Transparent rectypes_List_rt.
End rectypes_List_ty.

Section test_mutual_rectypes.
  Context `{!typeGS Σ}.

  Local Definition Foo_sls : struct_layout_spec :=
    mk_sls "Foo" [("x", PtrSynType); ("y", PtrSynType)] StructReprRust.

  Local Definition Bar_sls : struct_layout_spec :=
    mk_sls "Bar" [("x", Foo_sls : syn_type)] StructReprRust.

  Local Definition FooBar_rts : list RT := [unitRT; unitRT].

  Local Definition FooBar_F (tys : mut_types FooBar_rts) : mut_types FooBar_rts :=
    let Foo_ty := mut_type_project tys 0 eq_refl in
    let Bar_ty := mut_type_project tys 1 eq_refl in
    let Foo_inner := struct_t Foo_sls +[
      Box_inv_t unitRT -[] -[Foo_ty];
      Box_inv_t unitRT -[] -[Bar_ty]] in
    let Bar_inner := struct_t Bar_sls +[
      Foo_ty] in
    ex_plain_t _ _ unit_abs_inv Foo_inner +::
    ex_plain_t _ _ unit_abs_inv Bar_inner +::
    +[].

  Program Definition FooBar_tys : mut_types FooBar_rts :=
    @mut_fixpoint _ _ _ FooBar_F _ _ _.
  Next Obligation. solve_fixpoint_ne. Qed.
  Next Obligation. solve_fixpoint_contr. Qed.

  Definition Foo_ty : type unitRT := mut_type_project FooBar_tys 0 eq_refl.
  Definition Bar_ty : type unitRT := mut_type_project FooBar_tys 1 eq_refl.
End test_mutual_rectypes.
