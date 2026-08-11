From refinedrust Require Import typing.


(** * Panic shim *)

(** The frontend erases panic formatting arguments when calling this shim. Until
    panic-handler linkage is modeled explicitly, the abort branch is trusted to
    represent terminal execution of the configured panic runtime. *)
Program Definition panic_shim_def `{!RadiumConfig} : function :=
  {|
     f_args := [];
     f_code :=
       <[
     "_bb0" :=
       match radium_panic_strategy_of with
       | PanicUnwind => Unwind
       | PanicAbort => AbortS
       end
     ]>%E $
       ∅;
     f_init := "_bb0";
  |}.
Next Obligation. solve_fn_vars_nodup. Qed.

Definition type_of_panic_shim `{RRGS : !refinedrustGS Σ} :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : (), (λ _, []); (λ _, True)) →
    ∃ () : (), () @ unit_t; (λ _, False) | True.

Lemma panic_shim_typed `{RRGS : !refinedrustGS Σ} π :
  ⊢ typed_function π panic_shim_def (<tag_type> type_of_panic_shim).
Proof.
  start_function "panic_shim" ϝ ( [] ) ( [] ) ( [] ) ( ).
  repeat liRStep; liShow.
  destruct radium_panic_strategy_of eqn:Hstrategy.
  all: rep liRStep; liShow. done.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.


(** * Built-in shims for low-level pointer operations *)

(** Tuple defs *)
(* Since the frontend doesn't generate them for now, we just provide a few pre-defined ones for reasonable sizes. *)
Definition tuple1_sls (T0_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple1" [("0", T0_st)] StructReprRust.
Definition tuple1_st (T0_st : syn_type) : syn_type := tuple1_sls T0_st.
Definition tuple1_rt (T0_rt : RT) : RT :=
  plist place_rfnRT [T0_rt].
Definition tuple1_ty `{!refinedrustGS Σ} (T0_rt : RT) : spec_with 0 [T0_rt] (type (tuple1_rt _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty]) : [T0_rt], struct_t (tuple1_sls (st_of T0_ty MetaNone)) +[T0_ty].

Definition tuple2_sls (T0_st T1_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple2" [("0", T0_st); ("1", T1_st)] StructReprRust.
Definition tuple2_st (T0_st T1_st : syn_type) : syn_type := tuple2_sls T0_st T1_st.
Definition tuple2_rt (T0_rt : RT) (T1_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt].
Definition tuple2_ty `{!refinedrustGS Σ} (T0_rt T1_rt : RT) : spec_with 0 [T0_rt; T1_rt] (type (tuple2_rt _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : [T0_rt; T1_rt], struct_t (tuple2_sls (st_of T0_ty MetaNone) (st_of T1_ty MetaNone)) +[T0_ty; T1_ty].

Definition tuple3_sls (T0_st T1_st T2_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple3" [("0", T0_st); ("1", T1_st); ("2", T2_st)] StructReprRust.
Definition tuple3_st (T0_st T1_st T2_st : syn_type) : syn_type := tuple3_sls T0_st T1_st T2_st.
Definition tuple3_rt (T0_rt : RT) (T1_rt : RT) (T2_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt; T2_rt].
Definition tuple3_ty `{!refinedrustGS Σ} (T0_rt T1_rt T2_rt : RT) : spec_with 0 [T0_rt; T1_rt; T2_rt] (type (tuple3_rt _ _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : [T0_rt; T1_rt; T2_rt], struct_t (tuple3_sls (st_of T0_ty MetaNone) (st_of T1_ty MetaNone) (st_of T2_ty MetaNone)) +[T0_ty; T1_ty; T2_ty].

Definition tuple4_sls (T0_st T1_st T2_st T3_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple4" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st)] StructReprRust.
Definition tuple4_st (T0_st T1_st T2_st T3_st : syn_type) : syn_type := tuple4_sls T0_st T1_st T2_st T3_st.
Definition tuple4_rt (T0_rt : RT) (T1_rt : RT) (T2_rt : RT) (T3_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt; T2_rt; T3_rt].
Definition tuple4_ty `{!refinedrustGS Σ} (T0_rt T1_rt T2_rt T3_rt : RT) : spec_with 0 [T0_rt; T1_rt; T2_rt; T3_rt] (type (tuple4_rt _ _ _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : [T0_rt; T1_rt; T2_rt; T3_rt], struct_t (tuple4_sls (st_of T0_ty MetaNone) (st_of T1_ty MetaNone) (st_of T2_ty MetaNone) (st_of T3_ty MetaNone)) +[T0_ty; T1_ty; T2_ty; T3_ty].

Definition tuple5_sls (T0_st T1_st T2_st T3_st T4_st : syn_type) : struct_layout_spec :=
  mk_sls "tuple5" [("0", T0_st); ("1", T1_st); ("2", T2_st); ("3", T3_st); ("4", T4_st)] StructReprRust.
Definition tuple5_st (T0_st T1_st T2_st T3_st T4_st : syn_type) : syn_type := tuple5_sls T0_st T1_st T2_st T3_st T4_st.
Definition tuple5_rt (T0_rt : RT) (T1_rt : RT) (T2_rt : RT) (T3_rt : RT) (T4_rt : RT) : RT :=
  plist place_rfnRT [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt].
Definition tuple5_ty `{!refinedrustGS Σ} (T0_rt T1_rt T2_rt T3_rt T4_rt : RT) : spec_with 0 [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] (type (tuple5_rt _ _ _ _ _)) :=
  spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : [T0_rt; T1_rt; T2_rt; T3_rt; T4_rt], struct_t (tuple5_sls (st_of T0_ty MetaNone) (st_of T1_ty MetaNone) (st_of T2_ty MetaNone) (st_of T3_ty MetaNone) (st_of T4_ty MetaNone)) +[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty].

(** ** PhantomData *)
(** Encoded manually, as rustc only allows unused type parameters on the special PhantomData lang item in core *)
Definition core_marker_PhantomData_sls (T_st : syn_type) : struct_layout_spec :=
  mk_sls "core_marker_PhantomData" [] StructReprRust.
Definition core_marker_PhantomData_st (T_st : syn_type) : syn_type := core_marker_PhantomData_sls T_st.

Section def.
  Context `{!refinedrustGS Σ}.

  Program Definition core_marker_PhantomData_inv {T_rt : RT} (T_ty : type T_rt) : ex_inv_def (plist place_rfnRT []) unitRT :=
    mk_ex_inv_def (λ  _ _ _, True)%I (λ _ _ _ _, True)%I (λ _ _ _, True)%I true (ty_lfts T_ty) (ty_wf_E T_ty) _ _ _ _.
  Next Obligation. intros. unfold TCNoResolve. apply _. Qed.
  Next Obligation. eauto. Qed.
  Next Obligation. simpl. intros ??. ex_plain_t_solve_shr. Qed.
  Next Obligation. simpl. intros ??. ex_plain_t_solve_ghost_drop. Qed.

  Definition core_marker_PhantomData_rt (T_rt : RT) := unitRT.
  Definition core_marker_PhantomData_ty (T_rt : RT) : spec_with 0 [T_rt] (type unitRT) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : [T_rt],
      ex_plain_t _ _ (core_marker_PhantomData_inv T_ty) (struct_t (core_marker_PhantomData_sls (st_of T_ty MetaNone)) +[]).

  Global Instance core_marker_PhantomData_inv_contractive {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, core_marker_PhantomData_ty T_rt <TY> (T ty) <INST!>).
  Proof.
    intros ?.
    apply ex_plain_t_contr.
    - unfold core_marker_PhantomData_inv. simpl.
      constructor.
      + solve_type_proper.
      + solve_type_proper.
    - unfold core_marker_PhantomData_sls. apply _.
  Qed.
  Global Instance core_marker_PhantomData_inv_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, core_marker_PhantomData_ty T_rt <TY> (T ty) <INST!>).
  Proof.
    intros ?.
    apply ex_plain_t_ne.
    - unfold core_marker_PhantomData_inv. simpl.
      constructor.
      + solve_type_proper.
      + solve_type_proper.
    - unfold core_marker_PhantomData_sls. apply _.
  Qed.

  Global Program Instance core_marker_PhantomData_ty_dep_lft_mor rts (rt : RT) (T : mut_types rts → type rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, core_marker_PhantomData_ty rt *[] *[(T x)]) :=
    λ Ht,
      dep_lft_morph_make_id _ _ _ Ht _ _.
  Next Obligation.
    intros. rewrite /lifecycle_lfts/=.
    repeat rewrite !ty_lfts_unfold/=.
    rewrite !right_id//.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    rewrite !right_id//.
  Qed.
End def.


(** Drop glue *)
Record DropGlue_spec `{RRGS : !(refinedrustGS Σ)} `{T_rt : !RT} : Type := mk_DropGlue_spec {
  DropGlue_drop_glue_spec  : (spec_with 0 [] fn_spec);
}.
#[global] Arguments DropGlue_spec : clear implicits.
#[global] Arguments DropGlue_spec {_ _}.


Section DropGlue.
Context `{RRGS : !refinedrustGS Σ}.
Definition DropGlue_spec_incl `{T_rt : !RT} (spec1: ((DropGlue_spec (T_rt)))) (spec2: ((DropGlue_spec (T_rt)))) : Prop :=
  ((function_subtype (spec1.(DropGlue_drop_glue_spec)) (spec2.(DropGlue_drop_glue_spec)))).
Instance DropGlue_spec_incl_preorder `{T_rt : !RT} : (PreOrder (DropGlue_spec_incl (T_rt := T_rt))).
Proof.
  split. all: apply _.
Qed.

Definition scope_bindable_DropGlue_spec `{T_rt : !RT} : (ScopeBindable ((DropGlue_spec (T_rt)))) :=
  {|
    scope_add_typarams (rts: (list RT)) (tys: (plist type rts)) (s: ((DropGlue_spec (T_rt)))) :=
      {|
        DropGlue_drop_glue_spec  :=
          (scope_add_typarams (rts) (tys) (s.(DropGlue_drop_glue_spec)));
      |}
      ;
    scope_add_elctx (E: (lft → elctx)) (s: ((DropGlue_spec (T_rt)))) :=
      {|
        DropGlue_drop_glue_spec  :=
          (scope_add_elctx (E) (s.(DropGlue_drop_glue_spec)));
      |}
      ;
  |}
.
#[global] Existing Instance scope_bindable_DropGlue_spec.

Definition DropGlue_drop_glue_base_spec `{RRGS : !refinedrustGS Σ} (T_rt : RT) (T_st : syn_type) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (x, l) : (RT_xt T_rt * loc), (λ ϝ, []); l :@: alias_ref_t; λ π,
    (l ◁ₗ[π, Owned] #($# x) @ ◁ T_ty)%I) →
  ∃ () : (), () @ unit_t; λ π,
    ty_ghost_drop T_ty π ($# x) ∗
    (l ◁ₗ[π, Owned] .@ ◁ typed_value_t T_st) |
  False
.

Definition DropGlue_base_spec (T_rt: RT) (T_st: syn_type) : (spec_with _ _ (DropGlue_spec ((T_rt)))) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
      DropGlue_drop_glue_spec  :=
        (DropGlue_drop_glue_base_spec ((T_rt)) (T_st))
           <TY> T_ty : (spec_with 0 [] fn_spec);
    |}
.

End DropGlue.

Section DropGlue_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition trait_incl_of_DropGlue_drop_glue (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st -[] -[T_ty])))).
End DropGlue_trait_req_incls.

(*
Options here:
- have a new custom mutable reference type that doesn't require returning ownership?
  this is somewhat difficult, and the benefit is unclear.
- take a raw pointer + extra unsafe ownership.
  This seems much more straightforward.
  Physically, the layout is the same, we are just interpreting the safety contract differently.
  Since this is also exclusive, it should be fine.
  Also potentially validity invariants.
*)

(*

pub(crate) const unsafe fn drop_glue<T: PointeeSized>(_: &mut T)
where
    T: [const] Destruct,
{ }

*)

(** Tuple drop glue shims *)

Section TupleDropGlue_code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Program Definition drop_glue_tuple1_def (DropGlue_T0_drop_glue_loc: loc) (T0_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
       CallS DropGlue_T0_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple1_sls (T0_st)) } "0")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb2") (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
       Unwind
     ]>%E $
     <[
     "_bb2" :=
      return (zst_val)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

Program Definition drop_glue_tuple2_def (DropGlue_T0_drop_glue_loc: loc) (DropGlue_T1_drop_glue_loc: loc) (T0_st: syn_type) (T1_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
       CallS DropGlue_T0_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple2_sls (T0_st) (T1_st)) } "0")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb4") (Goto "_bb3")
     ]>%E $
     <[
     "_bb1" :=
       Unwind
     ]>%E $
     <[
     "_bb2" :=
       return (zst_val)
     ]>%E $
     <[
     "_bb3" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple2_sls (T0_st) (T1_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb1") UnwindTerminate
     ]>%E $
     <[
     "_bb4" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple2_sls (T0_st) (T1_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb2") (Goto "_bb1")
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

Program Definition drop_glue_tuple3_def (DropGlue_T0_drop_glue_loc: loc) (DropGlue_T1_drop_glue_loc: loc) (DropGlue_T2_drop_glue_loc: loc) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
       CallS DropGlue_T0_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple3_sls (T0_st) (T1_st) (T2_st)) } "0")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb4") (Goto "_bb7")
     ]>%E $
     <[
     "_bb1" :=
       Unwind
     ]>%E $
     <[
     "_bb2" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb4" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple3_sls (T0_st) (T1_st) (T2_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb5") (Goto "_bb6")
     ]>%E $
     <[
     "_bb5" :=
       CallS DropGlue_T2_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple3_sls (T0_st) (T1_st) (T2_st)) } "2")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb2") (Goto "_bb1")
     ]>%E $
     <[
     "_bb6" :=
       CallS DropGlue_T2_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple3_sls (T0_st) (T1_st) (T2_st)) } "2")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb1") UnwindTerminate
     ]>%E $
     <[
     "_bb7" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple3_sls (T0_st) (T1_st) (T2_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb6") UnwindTerminate
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

Program Definition drop_glue_tuple4_def (DropGlue_T0_drop_glue_loc: loc) (DropGlue_T1_drop_glue_loc: loc) (DropGlue_T2_drop_glue_loc: loc) (DropGlue_T3_drop_glue_loc: loc) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
       CallS DropGlue_T0_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "0")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb4") (Goto "_bb9")
     ]>%E $
     <[
     "_bb1" :=
       Unwind
     ]>%E $
     <[
     "_bb2" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb4" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb5") (Goto "_bb8")
     ]>%E $
     <[
     "_bb5" :=
       CallS DropGlue_T2_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "2")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb6") (Goto "_bb7")
     ]>%E $
     <[
     "_bb6" :=
       CallS DropGlue_T3_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "3")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb2") (Goto "_bb1")
     ]>%E $
     <[
     "_bb7" :=
       CallS DropGlue_T3_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "3")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb1") UnwindTerminate
     ]>%E $
     <[
     "_bb8" :=
       CallS DropGlue_T2_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "2")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb7") UnwindTerminate
     ]>%E $
     <[
     "_bb9" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple4_sls (T0_st) (T1_st) (T2_st) (T3_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb8") UnwindTerminate
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

Program Definition drop_glue_tuple5_def (DropGlue_T0_drop_glue_loc: loc) (DropGlue_T1_drop_glue_loc: loc) (DropGlue_T2_drop_glue_loc: loc) (DropGlue_T3_drop_glue_loc: loc) (DropGlue_T4_drop_glue_loc: loc) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) (T4_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
       CallS DropGlue_T0_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "0")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb4") (Goto "_bb11")
     ]>%E $
     <[
     "_bb1" :=
       Unwind
     ]>%E $
     <[
     "_bb2" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb4" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb5") (Goto "_bb10")
     ]>%E $
     <[
     "_bb5" :=
       CallS DropGlue_T2_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "2")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb6") (Goto "_bb9")
     ]>%E $
     <[
     "_bb6" :=
       CallS DropGlue_T3_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "3")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb7") (Goto "_bb8")
     ]>%E $
     <[
     "_bb7" :=
       CallS DropGlue_T4_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "4")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb2") (Goto "_bb1")
     ]>%E $
     <[
     "_bb8" :=
       CallS DropGlue_T4_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "4")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb1") UnwindTerminate
     ]>%E $
     <[
     "_bb9" :=
       CallS DropGlue_T3_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "3")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb8") UnwindTerminate
     ]>%E $
     <[
     "_bb10" :=
       CallS DropGlue_T2_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "2")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb9") UnwindTerminate
     ]>%E $
     <[
     "_bb11" :=
       CallS DropGlue_T1_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ PtrOp } ( "ptr" )) at{ (tuple5_sls (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) } "1")]
         (Some (Na1Ord, UntypedOp unit_sl, "ret")) (Goto "_bb10") UnwindTerminate
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Next Obligation.
  solve_fn_vars_nodup.
Qed.

End TupleDropGlue_code.

Section TupleDropGlue_trait_req_incls.
  Context `{RRGS : !(refinedrustGS Σ)}.

  Definition trait_incl_of_drop_glue_tuple1 (T0_rt: RT) (T0_st: syn_type) (DropGlue_T0_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T0_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[T0_ty]) : ([T0_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T0_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T0_rt) T0_st -[] -[T0_ty])))).

  Definition trait_incl_of_drop_glue_tuple2 (T0_rt: RT) (T1_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (DropGlue_T0_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T0_rt)))) (DropGlue_T1_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T1_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : ([T0_rt; T1_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T0_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T0_rt) T0_st -[] -[T0_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T1_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T1_rt) T1_st -[] -[T1_ty])))).

  Definition trait_incl_of_drop_glue_tuple3 (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (DropGlue_T0_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T0_rt)))) (DropGlue_T1_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T1_rt)))) (DropGlue_T2_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T2_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : ([T0_rt; T1_rt; T2_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T0_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T0_rt) T0_st -[] -[T0_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T1_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T1_rt) T1_st -[] -[T1_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T2_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T2_rt) T2_st -[] -[T2_ty])))).

  Definition trait_incl_of_drop_glue_tuple4 (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T3_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) (DropGlue_T0_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T0_rt)))) (DropGlue_T1_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T1_rt)))) (DropGlue_T2_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T2_rt)))) (DropGlue_T3_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T3_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T0_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T0_rt) T0_st -[] -[T0_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T1_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T1_rt) T1_st -[] -[T1_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T2_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T2_rt) T2_st -[] -[T2_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T3_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T3_rt) T3_st -[] -[T3_ty])))).

  Definition trait_incl_of_drop_glue_tuple5 (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T3_rt: RT) (T4_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) (T4_st: syn_type) (DropGlue_T0_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T0_rt)))) (DropGlue_T1_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T1_rt)))) (DropGlue_T2_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T2_rt)))) (DropGlue_T3_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T3_rt)))) (DropGlue_T4_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T4_rt)))) : (spec_with _ _ Prop) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T0_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T0_rt) T0_st -[] -[T0_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T1_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T1_rt) T1_st -[] -[T1_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T2_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T2_rt) T2_st -[] -[T2_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T3_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T3_rt) T3_st -[] -[T3_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T4_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T4_rt) T4_st -[] -[T4_ty])))).
End TupleDropGlue_trait_req_incls.

Section TupleDropGlue_specs.
  Context `{RRGS : !(refinedrustGS Σ)}.

  Definition type_of_drop_glue_tuple1 (T0_rt: RT) (T0_st: syn_type) :=
    spec! ( *[]) : 0 | ( *[T0_ty]) : ([T0_rt] : list RT), (λ a b, scope_add_typarams _ -[T0_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec ((tuple1_rt ((T0_rt)))) ((tuple1_st (T0_st)))) -[] -[(tuple1_ty ((T0_rt)) -[] -[T0_ty])]).(DropGlue_drop_glue_spec) a b))) <MERGE!>.

  Definition type_of_drop_glue_tuple2 (T0_rt: RT) (T1_rt: RT) (T0_st: syn_type) (T1_st: syn_type) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : ([T0_rt; T1_rt] : list RT), (λ a b, scope_add_typarams _ -[T0_ty; T1_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec ((tuple2_rt ((T0_rt)) ((T1_rt)))) ((tuple2_st (T0_st) (T1_st)))) -[] -[(tuple2_ty ((T0_rt)) ((T1_rt)) -[] -[T0_ty; T1_ty])]).(DropGlue_drop_glue_spec) a b))) <MERGE!>.

  Definition type_of_drop_glue_tuple3 (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : ([T0_rt; T1_rt; T2_rt] : list RT), (λ a b, scope_add_typarams _ -[T0_ty; T1_ty; T2_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec ((tuple3_rt ((T0_rt)) ((T1_rt)) ((T2_rt)))) ((tuple3_st (T0_st) (T1_st) (T2_st)))) -[] -[(tuple3_ty ((T0_rt)) ((T1_rt)) ((T2_rt)) -[] -[T0_ty; T1_ty; T2_ty])]).(DropGlue_drop_glue_spec) a b))) <MERGE!>.

  Definition type_of_drop_glue_tuple4 (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T3_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt] : list RT), (λ a b, scope_add_typarams _ -[T0_ty; T1_ty; T2_ty; T3_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec ((tuple4_rt ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)))) ((tuple4_st (T0_st) (T1_st) (T2_st) (T3_st)))) -[] -[(tuple4_ty ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) -[] -[T0_ty; T1_ty; T2_ty; T3_ty])]).(DropGlue_drop_glue_spec) a b))) <MERGE!>.

  Definition type_of_drop_glue_tuple5 (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T3_rt: RT) (T4_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) (T4_st: syn_type) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] : list RT), (λ a b, scope_add_typarams _ -[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty] (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec ((tuple5_rt ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) ((T4_rt)))) ((tuple5_st (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)))) -[] -[(tuple5_ty ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) ((T4_rt)) -[] -[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty])]).(DropGlue_drop_glue_spec) a b))) <MERGE!>.

  Definition drop_glue_tuple1_spec (T0_rt: RT) (T0_st: syn_type) : (spec_with _ _ (DropGlue_spec (((tuple1_rt ((T0_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T0_ty]) : ([T0_rt] : list RT), {|
        DropGlue_drop_glue_spec :=
          (type_of_drop_glue_tuple1 ((T0_rt)) (T0_st)) <TY> T0_ty : (spec_with 0 [] fn_spec);
      |}.

  Definition drop_glue_tuple2_spec (T0_rt: RT) (T1_rt: RT) (T0_st: syn_type) (T1_st: syn_type) : (spec_with _ _ (DropGlue_spec (((tuple2_rt ((T0_rt)) ((T1_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : ([T0_rt; T1_rt] : list RT), {|
        DropGlue_drop_glue_spec :=
          (type_of_drop_glue_tuple2 ((T0_rt)) ((T1_rt)) (T0_st) (T1_st)) <TY> T0_ty <TY> T1_ty : (spec_with 0 [] fn_spec);
      |}.

  Definition drop_glue_tuple3_spec (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) : (spec_with _ _ (DropGlue_spec (((tuple3_rt ((T0_rt)) ((T1_rt)) ((T2_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : ([T0_rt; T1_rt; T2_rt] : list RT), {|
        DropGlue_drop_glue_spec :=
          (type_of_drop_glue_tuple3 ((T0_rt)) ((T1_rt)) ((T2_rt)) (T0_st) (T1_st) (T2_st)) <TY> T0_ty <TY> T1_ty <TY> T2_ty : (spec_with 0 [] fn_spec);
      |}.

  Definition drop_glue_tuple4_spec (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T3_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) : (spec_with _ _ (DropGlue_spec (((tuple4_rt ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt] : list RT), {|
        DropGlue_drop_glue_spec :=
          (type_of_drop_glue_tuple4 ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) (T0_st) (T1_st) (T2_st) (T3_st)) <TY> T0_ty <TY> T1_ty <TY> T2_ty <TY> T3_ty : (spec_with 0 [] fn_spec);
      |}.

  Definition drop_glue_tuple5_spec (T0_rt: RT) (T1_rt: RT) (T2_rt: RT) (T3_rt: RT) (T4_rt: RT) (T0_st: syn_type) (T1_st: syn_type) (T2_st: syn_type) (T3_st: syn_type) (T4_st: syn_type) : (spec_with _ _ (DropGlue_spec (((tuple5_rt ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) ((T4_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] : list RT), {|
        DropGlue_drop_glue_spec :=
          (type_of_drop_glue_tuple5 ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) ((T4_rt)) (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) <TY> T0_ty <TY> T1_ty <TY> T2_ty <TY> T3_ty <TY> T4_ty : (spec_with 0 [] fn_spec);
      |}.

  Definition drop_glue_tuple1_spec_subsumption :=
    ∀ `(T0_rt : !RT) `(T0_st : !syn_type), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T0_ty]) : ([T0_rt] : list RT), (drop_glue_tuple1_spec (T0_rt) (T0_st)) -[] -[T0_ty]) (spec! ( *[]) : 0 | ( *[T0_ty]) : ([T0_rt] : list RT), scope_add_typarams _ -[T0_ty] ((DropGlue_base_spec ((tuple1_rt ((T0_rt)))) (tuple1_st (T0_st)) -[] -[(tuple1_ty ((T0_rt)) -[] -[T0_ty])])))).

  Definition drop_glue_tuple2_spec_subsumption :=
    ∀ `(T0_rt : !RT) `(T1_rt : !RT) `(T0_st : !syn_type) `(T1_st : !syn_type), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : ([T0_rt; T1_rt] : list RT), (drop_glue_tuple2_spec (T0_rt) (T1_rt) (T0_st) (T1_st)) -[] -[T0_ty; T1_ty]) (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty]) : ([T0_rt; T1_rt] : list RT), scope_add_typarams _ -[T0_ty; T1_ty] ((DropGlue_base_spec ((tuple2_rt ((T0_rt)) ((T1_rt)))) (tuple2_st (T0_st) (T1_st)) -[] -[(tuple2_ty ((T0_rt)) ((T1_rt)) -[] -[T0_ty; T1_ty])])))).

  Definition drop_glue_tuple3_spec_subsumption :=
    ∀ `(T0_rt : !RT) `(T1_rt : !RT) `(T2_rt : !RT) `(T0_st : !syn_type) `(T1_st : !syn_type) `(T2_st : !syn_type), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : ([T0_rt; T1_rt; T2_rt] : list RT), (drop_glue_tuple3_spec (T0_rt) (T1_rt) (T2_rt) (T0_st) (T1_st) (T2_st)) -[] -[T0_ty; T1_ty; T2_ty]) (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty]) : ([T0_rt; T1_rt; T2_rt] : list RT), scope_add_typarams _ -[T0_ty; T1_ty; T2_ty] ((DropGlue_base_spec ((tuple3_rt ((T0_rt)) ((T1_rt)) ((T2_rt)))) (tuple3_st (T0_st) (T1_st) (T2_st)) -[] -[(tuple3_ty ((T0_rt)) ((T1_rt)) ((T2_rt)) -[] -[T0_ty; T1_ty; T2_ty])])))).

  Definition drop_glue_tuple4_spec_subsumption :=
    ∀ `(T0_rt : !RT) `(T1_rt : !RT) `(T2_rt : !RT) `(T3_rt : !RT) `(T0_st : !syn_type) `(T1_st : !syn_type) `(T2_st : !syn_type) `(T3_st : !syn_type), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt] : list RT), (drop_glue_tuple4_spec (T0_rt) (T1_rt) (T2_rt) (T3_rt) (T0_st) (T1_st) (T2_st) (T3_st)) -[] -[T0_ty; T1_ty; T2_ty; T3_ty]) (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt] : list RT), scope_add_typarams _ -[T0_ty; T1_ty; T2_ty; T3_ty] ((DropGlue_base_spec ((tuple4_rt ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)))) (tuple4_st (T0_st) (T1_st) (T2_st) (T3_st)) -[] -[(tuple4_ty ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) -[] -[T0_ty; T1_ty; T2_ty; T3_ty])])))).

  Definition drop_glue_tuple5_spec_subsumption :=
    ∀ `(T0_rt : !RT) `(T1_rt : !RT) `(T2_rt : !RT) `(T3_rt : !RT) `(T4_rt : !RT) `(T0_st : !syn_type) `(T1_st : !syn_type) `(T2_st : !syn_type) `(T3_st : !syn_type) `(T4_st : !syn_type), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] : list RT), (drop_glue_tuple5_spec (T0_rt) (T1_rt) (T2_rt) (T3_rt) (T4_rt) (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) -[] -[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) (spec! ( *[]) : 0 | ( *[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty]) : ([T0_rt; T1_rt; T2_rt; T3_rt; T4_rt] : list RT), scope_add_typarams _ -[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty] ((DropGlue_base_spec ((tuple5_rt ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) ((T4_rt)))) (tuple5_st (T0_st) (T1_st) (T2_st) (T3_st) (T4_st)) -[] -[(tuple5_ty ((T0_rt)) ((T1_rt)) ((T2_rt)) ((T3_rt)) ((T4_rt)) -[] -[T0_ty; T1_ty; T2_ty; T3_ty; T4_ty])])))).
End TupleDropGlue_specs.

Section proof.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition drop_glue_tuple1_lemma (π : thread_id) : Prop :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_T_drop_glue_loc : loc),
    syn_type_is_layoutable (((tuple1_sls (T_st)) : syn_type)) →
    DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    typed_function π (drop_glue_tuple1_def DropGlue_T_drop_glue_loc T_st) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_tuple1 T_rt T_st -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
    ∗ (⌜((trait_incl_of_drop_glue_tuple1 (T_rt) (T_st) (DropGlue_T_spec))-[] -[T_ty])%Z⌝))).

  Ltac drop_glue_tuple1_prelude :=
    unfold drop_glue_tuple1_lemma;
    set (FN_NAME := FUNCTION_NAME "drop_glue_tuple1");
    intros T_rt T_st DropGlue_T_spec;
    intros;
    iStartProof;
    let ϝ := fresh "ϝ" in
    let T_ty := fresh "T_ty" in
    start_function "drop_glue_tuple1" ϝ ( [] ) ( [T_ty [] ] ) ( ? );
    intros arg_ptr;
    let π := get_π in
    let Σ := get_Σ in
    specialize (pose_bb_inv (PolyNil)) as loop_map;
    init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
    init_tyvars ( <[
        "T" :=
    existT _ (T_ty)
        ]>%E $ ∅ );
    unfold_generic_inst; simpl.

  Lemma drop_glue_tuple1_proof (π : thread_id) :
    drop_glue_tuple1_lemma π.
  Proof.
    drop_glue_tuple1_prelude.

    rep <-! liRStep; liShow.

    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
  Qed.

  Definition drop_glue_tuple2_lemma (π : thread_id) : Prop :=
    ∀ `(T_rt : !RT) `(U_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_U_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) (DropGlue_T_drop_glue_loc : loc) (DropGlue_U_drop_glue_loc : loc) ,
    syn_type_is_layoutable (((tuple2_sls (T_st) (U_st)) : syn_type)) →
    DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_U_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_U_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_U_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    typed_function π (drop_glue_tuple2_def DropGlue_T_drop_glue_loc  DropGlue_U_drop_glue_loc  T_st  U_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_tuple2 T_rt U_rt T_st U_st -[] -[T_ty; U_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
    ∗ (typaram_wf U_rt U_st U_ty))
    ∗ (⌜((trait_incl_of_drop_glue_tuple2 (T_rt) (U_rt) (T_st) (U_st) (DropGlue_T_spec) (DropGlue_U_spec))-[] -[T_ty; U_ty])%Z⌝))).

  Ltac drop_glue_tuple2_prelude :=
    unfold drop_glue_tuple2_lemma;
    set (FN_NAME := FUNCTION_NAME "drop_glue_tuple2");
    intros T_rt U_rt T_st U_st DropGlue_T_spec DropGlue_U_spec;
    intros;
    iStartProof;
    let ϝ := fresh "ϝ" in
    let T_ty := fresh "T_ty" in
    let U_ty := fresh "U_ty" in
    start_function "drop_glue_tuple2" ϝ ( [] ) ( [T_ty [U_ty [] ] ] ) ( ? );
    intros arg_ptr;
    let π := get_π in
    let Σ := get_Σ in
    specialize (pose_bb_inv (PolyNil)) as loop_map;
    init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
    init_tyvars ( <[
        "T" :=
    existT _ (T_ty)
        ]>%E $ <[
        "U" :=
    existT _ (U_ty)
        ]>%E $ ∅ );
    unfold_generic_inst; simpl.

    Lemma drop_glue_tuple2_proof (π : thread_id) :
      drop_glue_tuple2_lemma π.
    Proof.
      drop_glue_tuple2_prelude.

      rep <-! liRStep; liShow.

      all: print_remaining_goal.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
      Unshelve. all: print_remaining_sidecond.
    Qed.

  Definition drop_glue_tuple3_lemma (π : thread_id) : Prop :=
    ∀ `(T_rt : !RT) `(U_rt : !RT) `(V_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(V_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_U_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) `(DropGlue_V_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (V_rt)))) (DropGlue_T_drop_glue_loc : loc) (DropGlue_U_drop_glue_loc : loc) (DropGlue_V_drop_glue_loc : loc),
    syn_type_is_layoutable (((tuple3_sls (T_st) (U_st) (V_st)) : syn_type)) →
    DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_U_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_U_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_U_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_V_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_V_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_V_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    typed_function π (drop_glue_tuple3_def DropGlue_T_drop_glue_loc DropGlue_U_drop_glue_loc DropGlue_V_drop_glue_loc T_st U_st V_st) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty; V_ty]) : ([T_rt; U_rt; V_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_tuple3 T_rt U_rt V_rt T_st U_st V_st -[] -[T_ty; U_ty; V_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
    ∗ (typaram_wf U_rt U_st U_ty)
    ∗ (typaram_wf V_rt V_st V_ty))
    ∗ (⌜((trait_incl_of_drop_glue_tuple3 (T_rt) (U_rt) (V_rt) (T_st) (U_st) (V_st) (DropGlue_T_spec) (DropGlue_U_spec) (DropGlue_V_spec))-[] -[T_ty; U_ty; V_ty])%Z⌝))).

  Ltac drop_glue_tuple3_prelude :=
    unfold drop_glue_tuple3_lemma;
    set (FN_NAME := FUNCTION_NAME "drop_glue_tuple3");
    intros T_rt U_rt V_rt T_st U_st V_st DropGlue_T_spec DropGlue_U_spec DropGlue_V_spec;
    intros;
    iStartProof;
    let ϝ := fresh "ϝ" in
    let T_ty := fresh "T_ty" in
    let U_ty := fresh "U_ty" in
    let V_ty := fresh "V_ty" in
    start_function "drop_glue_tuple3" ϝ ( [] ) ( [T_ty [U_ty [V_ty [] ] ] ] ) ( ? );
    intros arg_ptr;
    let π := get_π in
    let Σ := get_Σ in
    specialize (pose_bb_inv (PolyNil)) as loop_map;
    init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
    init_tyvars ( <[
        "T" :=
    existT _ (T_ty)
        ]>%E $ <[
        "U" :=
    existT _ (U_ty)
        ]>%E $ <[
        "V" :=
    existT _ (V_ty)
        ]>%E $ ∅ );
    unfold_generic_inst; simpl.

  Lemma drop_glue_tuple3_proof (π : thread_id) :
    drop_glue_tuple3_lemma π.
  Proof.
    drop_glue_tuple3_prelude.

    rep <-! liRStep; liShow.

    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
  Qed.

  Definition drop_glue_tuple4_lemma (π : thread_id) : Prop :=
    ∀ `(T_rt : !RT) `(U_rt : !RT) `(V_rt : !RT) `(W_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(V_st : !syn_type) `(W_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_U_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) `(DropGlue_V_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (V_rt)))) `(DropGlue_W_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (W_rt)))) (DropGlue_T_drop_glue_loc : loc) (DropGlue_U_drop_glue_loc : loc) (DropGlue_V_drop_glue_loc : loc) (DropGlue_W_drop_glue_loc : loc),
    syn_type_is_layoutable (((tuple4_sls (T_st) (U_st) (V_st) (W_st)) : syn_type)) →
    DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_U_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_U_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_U_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_V_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_V_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_V_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_W_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_W_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_W_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    typed_function π (drop_glue_tuple4_def DropGlue_T_drop_glue_loc DropGlue_U_drop_glue_loc DropGlue_V_drop_glue_loc DropGlue_W_drop_glue_loc T_st U_st V_st W_st) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty; V_ty; W_ty]) : ([T_rt; U_rt; V_rt; W_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_tuple4 T_rt U_rt V_rt W_rt T_st U_st V_st W_st -[] -[T_ty; U_ty; V_ty; W_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
    ∗ (typaram_wf U_rt U_st U_ty)
    ∗ (typaram_wf V_rt V_st V_ty)
    ∗ (typaram_wf W_rt W_st W_ty))
    ∗ (⌜((trait_incl_of_drop_glue_tuple4 (T_rt) (U_rt) (V_rt) (W_rt) (T_st) (U_st) (V_st) (W_st) (DropGlue_T_spec) (DropGlue_U_spec) (DropGlue_V_spec) (DropGlue_W_spec))-[] -[T_ty; U_ty; V_ty; W_ty])%Z⌝))).

  Ltac drop_glue_tuple4_prelude :=
    unfold drop_glue_tuple4_lemma;
    set (FN_NAME := FUNCTION_NAME "drop_glue_tuple4");
    intros T_rt U_rt V_rt W_rt T_st U_st V_st W_st DropGlue_T_spec DropGlue_U_spec DropGlue_V_spec DropGlue_W_spec;
    intros;
    iStartProof;
    let ϝ := fresh "ϝ" in
    let T_ty := fresh "T_ty" in
    let U_ty := fresh "U_ty" in
    let V_ty := fresh "V_ty" in
    let W_ty := fresh "W_ty" in
    start_function "drop_glue_tuple4" ϝ ( [] ) ( [T_ty [U_ty [V_ty [W_ty [] ] ] ] ] ) ( ? );
    intros arg_ptr;
    let π := get_π in
    let Σ := get_Σ in
    specialize (pose_bb_inv (PolyNil)) as loop_map;
    init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
    init_tyvars ( <[
        "T" :=
    existT _ (T_ty)
        ]>%E $ <[
        "U" :=
    existT _ (U_ty)
        ]>%E $ <[
        "V" :=
    existT _ (V_ty)
        ]>%E $ <[
        "W" :=
    existT _ (W_ty)
        ]>%E $ ∅ );
    unfold_generic_inst; simpl.

  Lemma drop_glue_tuple4_proof (π : thread_id) :
    drop_glue_tuple4_lemma π.
  Proof.
    drop_glue_tuple4_prelude.

    rep <-! liRStep; liShow.

    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
  Qed.

  Definition drop_glue_tuple5_lemma (π : thread_id) : Prop :=
    ∀ `(T_rt : !RT) `(U_rt : !RT) `(V_rt : !RT) `(W_rt : !RT) `(X_rt : !RT) `(T_st : !syn_type) `(U_st : !syn_type) `(V_st : !syn_type) `(W_st : !syn_type) `(X_st : !syn_type) `(DropGlue_T_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) `(DropGlue_U_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) `(DropGlue_V_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (V_rt)))) `(DropGlue_W_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (W_rt)))) `(DropGlue_X_spec : !(spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (X_rt)))) (DropGlue_T_drop_glue_loc : loc) (DropGlue_U_drop_glue_loc : loc) (DropGlue_V_drop_glue_loc : loc) (DropGlue_W_drop_glue_loc : loc) (DropGlue_X_drop_glue_loc : loc),
    syn_type_is_layoutable (((tuple5_sls (T_st) (U_st) (V_st) (W_st) (X_st)) : syn_type)) →
    DropGlue_T_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_T_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_T_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_U_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_U_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_U_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_V_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_V_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_V_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_W_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_W_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_W_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    DropGlue_X_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_X_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_X_spec-[] -[]))  -[] -[]) (λ π, (True))%I) -∗
    typed_function π (drop_glue_tuple5_def DropGlue_T_drop_glue_loc DropGlue_U_drop_glue_loc DropGlue_V_drop_glue_loc DropGlue_W_drop_glue_loc DropGlue_X_drop_glue_loc T_st U_st V_st W_st X_st) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; U_ty; V_ty; W_ty; X_ty]) : ([T_rt; U_rt; V_rt; W_rt; X_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_tuple5 T_rt U_rt V_rt W_rt X_rt T_st U_st V_st W_st X_st -[] -[T_ty; U_ty; V_ty; W_ty; X_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
    ∗ (typaram_wf U_rt U_st U_ty)
    ∗ (typaram_wf V_rt V_st V_ty)
    ∗ (typaram_wf W_rt W_st W_ty)
    ∗ (typaram_wf X_rt X_st X_ty))
    ∗ (⌜((trait_incl_of_drop_glue_tuple5 (T_rt) (U_rt) (V_rt) (W_rt) (X_rt) (T_st) (U_st) (V_st) (W_st) (X_st) (DropGlue_T_spec) (DropGlue_U_spec) (DropGlue_V_spec) (DropGlue_W_spec) (DropGlue_X_spec))-[] -[T_ty; U_ty; V_ty; W_ty; X_ty])%Z⌝))).

  Ltac drop_glue_tuple5_prelude :=
    unfold drop_glue_tuple5_lemma;
    set (FN_NAME := FUNCTION_NAME "drop_glue_tuple5");
    intros T_rt U_rt V_rt W_rt X_rt T_st U_st V_st W_st X_st DropGlue_T_spec DropGlue_U_spec DropGlue_V_spec DropGlue_W_spec DropGlue_X_spec;
    intros;
    iStartProof;
    let ϝ := fresh "ϝ" in
    let T_ty := fresh "T_ty" in
    let U_ty := fresh "U_ty" in
    let V_ty := fresh "V_ty" in
    let W_ty := fresh "W_ty" in
    let X_ty := fresh "X_ty" in
    start_function "drop_glue_tuple5" ϝ ( [] ) ( [T_ty [U_ty [V_ty [W_ty [X_ty [] ] ] ] ] ] ) ( ? );
    intros arg_ptr;
    let π := get_π in
    let Σ := get_Σ in
    specialize (pose_bb_inv (PolyNil)) as loop_map;
    init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
    init_tyvars ( <[
        "T" :=
    existT _ (T_ty)
        ]>%E $ <[
        "U" :=
    existT _ (U_ty)
        ]>%E $ <[
        "V" :=
    existT _ (V_ty)
        ]>%E $ <[
        "W" :=
    existT _ (W_ty)
        ]>%E $ <[
        "X" :=
    existT _ (X_ty)
        ]>%E $ ∅ );
    unfold_generic_inst; simpl.

  Lemma drop_glue_tuple5_proof (π : thread_id) :
    drop_glue_tuple5_lemma π.
  Proof.
    drop_glue_tuple5_prelude.

    rep <-! liRStep; liShow.

    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.
    Unshelve. all: print_remaining_sidecond.
  Qed.
End proof.
