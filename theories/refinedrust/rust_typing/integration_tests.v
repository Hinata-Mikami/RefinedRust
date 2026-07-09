From refinedrust Require Import typing.

Module test.
Definition bla0 `{typeGS Σ} :=
  (fn(∀ ( *[κ'; κ]) : 2 | ( *[]) : [] | (x) : unit, (λ f, [(κ', κ)]); (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; λ π, ⌜ (4 > y)%Z⌝).
Definition bla1 `{typeGS Σ} :=
  (fn(∀ ( *[]) : 0 | ( *[]) : [] | x : unit, (λ _, []); (() :@: (uninit PtrSynType)) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).
Definition bla2 `{typeGS Σ} :=
  (fn(∀ ( *[]) : 0 | ( *[]) : [] | x : unit, (λ _, []); () :@: (uninit PtrSynType), () :@: (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).
Definition bla3 `{typeGS Σ} T_st T_rt :=
  (fn(∀ ( *[]) : 0 | ( *[ T_ty]) : [ (T_rt, T_st) ] | (x) : _, (λ _, []); x :@: T_ty, () :@: (uninit PtrSynType) ; (λ π, True)) → ∃ y : Z, () @ (uninit PtrSynType) ; (λ π, ⌜ (4 > y)%Z⌝)).

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
        l ◁ₗ[π, Owned] (#$# r) @ ◁ T_ty.

Lemma ptr_write_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_write T_st) (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
    (fn_spec_add_late_pre (type_of_ptr_write T_rt T_st <TY> T_ty <INST!>) (λ π, typaram_wf T_rt T_st T_ty))).
Proof.
  start_function "ptr_write" ϝ ( [] ) ( [T_ty []] ) ( [l r] ) ( ).

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
  start_function "ptr_write" ϝ ( [] ) ( [] ) ( [l r] ) ( ).
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
    fn_spec_add_late_pre ((type_of_ptr_write (place_rfnRT U_rt) (PtrSynType) <TY> shr_ref κ U_ty) <INST!>)
    (λ π, typaram_wf U_rt U_st U_ty)%I
.

Lemma ptr_write_typed_shrref `{!typeGS Σ} π U_rt U_st :
  ⊢ typed_function π (ptr_write (PtrSynType)) (<tag_type> type_of_ptr_write_shrref U_rt U_st).
Proof.
  start_function "ptr_write" ϝ ( [ulft_a []]  ) ( [U_ty []] ) ( [l r] ) ( ).

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
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, Owned] # ($# r) @ ◁ T_ty)).

Lemma ptr_read_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π (ptr_read T_st) (<tag_type>
      spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
    (fn_spec_add_late_pre (type_of_ptr_read T_rt T_st <TY> T_ty <INST!>) (λ π, typaram_wf T_rt T_st T_ty))).
Proof.
  start_function "ptr_read" ϝ ( [] ) ( [T_ty []] ) ( [src r] ) ( ).

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
  Local Program Definition Pdef := mk_pers_ex_inv_def P_a true _ _.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_t_solve_timeless. Qed.
  Local Definition Pty := (∃; Pdef, int I32)%I.

  Local Lemma Pty_copy : Copyable Pty.
  Proof. apply _. Qed.

  Local Definition P_b := λ (π : thread_id) (x : Z) (y : Z), (∃ (z : Z) (l : loc), ⌜x = (y + z)%Z⌝ ∗ ⌜(0 < x)%Z⌝ ∗ guarded true (l ◁ₗ[π, Owned] #42%Z @ (◁ int I32)))%I : iProp Σ.
  Local Definition S_b := λ (π : thread_id) (κ : lft) (x : Z) (y : Z), (∃ (z : Z) (l : loc), ⌜x = (y + z)%Z⌝ ∗ ⌜(0 < x)%Z⌝ ∗ guarded false (l ◁ₗ[π, Shared κ] #42%Z @ (◁ int I32)))%I : iProp Σ.

  Local Program Definition Adef := mk_ex_inv_def_auto_ghost_drop P_b S_b _ false [] [] _ _ _.
  Next Obligation. ex_plain_t_solve_ghost_drop_auto. Defined.
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. rewrite /S_b. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. rewrite /P_b /S_b. ex_plain_t_solve_shr. Qed.

  Local Program Definition Bdef := mk_auto_ex_inv_def P_b false [] [] _ _ _ _.
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
  Next Obligation. admit. Admitted.
  Next Obligation. done. Qed.
  Next Obligation. admit. Admitted.
  Next Obligation. admit. Admitted.

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
  .
  Next Obligation.
    solve_inhabited.
  Defined.
  Next Obligation.
    done.
  Qed.
  Next Obligation.
    solve_mk_enum_tag_consistent.
  Defined.

  Definition std_option_Option_ty : type _ := enum_t std_option_Option_enum.
  Global Typeclasses Transparent std_option_Option_ty.
End std_option_Option_ty.
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
      ([] ++ ty_lfts T_ty)
      ([] ++ ty_wf_E T_ty)
      _ _ _ _
    .
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
    mk_ex_inv_def (λ _ _ _, True)%I (λ _ _ _ _, True)%I (λ _ _ _, True)%I
      true [] [] _ _ _ _.
  Next Obligation. intros. unfold TCNoResolve. apply _. Qed.
  Next Obligation. eauto. Qed.
  Next Obligation.
    simpl. intros X F tid κ x y q ?.
    iIntros "_ _ Htok _".
    iApply logical_step_intro. iFrame.
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
            ([])
            ([])
            _ _ _ _
          .
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
        _.
    Next Obligation.
      solve_inhabited.
    Defined.
    Next Obligation.
      done.
    Qed.

    Next Obligation.
      solve_mk_enum_tag_consistent.
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
