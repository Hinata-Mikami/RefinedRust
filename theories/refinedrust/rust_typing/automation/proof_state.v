From refinedrust.base Require Import type programs value.
From refinedrust.primitive Require Import functions.
From lithium Require Import hooks all.
From iris.proofmode Require Import environments.

(* Initialize the [named_lfts] assertion with external lifetimes.
   Usually called after [start_function].
 *)
Tactic Notation "init_lfts" constr(π) constr(fid) uconstr(map) :=
  lazymatch goal with
  | |- _ =>
      unshelve iPoseProof (named_lfts_init (π, fid) (map : list (string * lft))) as "-#?";
      [apply _ .. | ]
  end.
  (*specialize (tt : LFT_MAP map) as lfts.*)

Tactic Notation "init_tyvars" uconstr(M) :=
  specialize (tt : TYVAR_MAP M) as tyvars.

Definition BLOCK_PRECOND `{!typeGS Σ} (bid : label) (P : iProp Σ) : Set := unit.
Arguments BLOCK_PRECOND : simpl never.

Definition CASE_DISTINCTION_INFO {B} (info : B) (* (i : list location_info) *) : Set := unit.
Arguments CASE_DISTINCTION_INFO : simpl never.

Inductive RUST_PROGRAM_POINT : Set :=
| RustProgramPointStmt (s : stmt)
| RustProgramPointExpr (s : stmt) (e : expr)
| RustProgramPointCall (v : val) (vl : list val)
    (destination : option (lang.order * op_type * expr)) (normal unwind : stmt).

Definition LAST_RUST_PROGRAM_POINT (point : RUST_PROGRAM_POINT) : Set := unit.
Arguments LAST_RUST_PROGRAM_POINT : simpl never.

Definition ELCTX (E : elctx) : elctx := E.
Arguments ELCTX : simpl never.
Ltac unfold_elctx :=
  try match goal with
  | H := ELCTX _ |- _ => subst H; unfold ELCTX
  end.

Definition CODE_MARKER (rf : function) : function := rf.
Notation "'HIDDEN'" := (CODE_MARKER _) (only printing).
Arguments CODE_MARKER : simpl never.
Ltac unfold_code_marker_and_compute_map_lookup :=
  unfold CODE_MARKER in *;
  match goal with
    | |- f_code ?FN !! _ = Some _ => unfold FN;
          match goal with
          | |- f_code ?t !! _ = Some _ =>
              let rec unfold_fn t :=
                match t with
                | ?a _ => unfold_fn a
                | ?a => unfold a
                end
              in unfold_fn t
          end; unfold f_code
  end;
  compute_map_lookup.

Definition RETURN_MARKER `{!typeGS Σ} (R : @typed_stmt_R_t Σ) : @typed_stmt_R_t Σ := R.
Notation "'HIDDEN'" := (RETURN_MARKER _) (only printing).
(* simplify RETURN_MARKER as soon as it is applied enough in the goal *)
Arguments RETURN_MARKER _ _ /.

Definition UNWIND_MARKER `{!typeGS Σ} (U : @typed_stmt_U_t Σ) : @typed_stmt_U_t Σ := U.
Notation "'HIDDEN_UNWIND'" := (UNWIND_MARKER _) (only printing).
Arguments UNWIND_MARKER _ /.

(* Function name marker *)
Definition FUNCTION_NAME (s : string) := s.
Arguments FUNCTION_NAME : simpl never.
Notation "'HIDDEN'" := (FUNCTION_NAME _) (only printing) : rr_hidden.

(* Function ptr type assignments *)
Notation "'HIDDEN_FUNCTION_PTR_T' v" := (ty_own_val (function_ptr _ _) _ _ _ v) (only printing, at level 100) : rr_hidden.

Definition function_ty_wrapper {T : Type} (t : T) := t.
Notation "'HIDDEN_FUNCTION_TY'" := (function_ty_wrapper _) (only printing, at level 0) : rr_hidden.

Ltac set_function_types :=
  repeat match goal with
  | |- context [function_ptr _ (_, ?ty)] =>
      match ty with
      | λ _, _ =>
        let H := fresh in
        set (H := ty);
        change ty with (function_ty_wrapper ty) in H;
        unfold spec_instantiate_lft_fst, spec_instantiate_typaram_fst, spec_instantiated in H
      end
  end.

(* Trait incl assumptions *)
Notation "'HIDDEN_TRAIT_INCL'" := (trait_incl_marker _) (only printing, at level 0) : rr_hidden.

(** Sidecondition caching *)

(** Single cache *)
Definition CACHED {A : Type} (a : A) := a.
Global Typeclasses Opaque CACHED.
Arguments CACHED : simpl never.
Notation "'CACHED'" := (CACHED _) (only printing).

Lemma enter_cache {A} : A → CACHED A.
Proof. apply CACHED. Defined.

(** Hook to process an assumption [H] before entering it into the cache. *)
Ltac enter_cache_hook H cont :=
  cont H.

(** Unsafe version that bypasses the hooks *)
Ltac enter_cache_unsafe H :=
  apply enter_cache in H.
Ltac enter_cache H :=
  enter_cache_hook H ltac:(fun Hn =>
    enter_cache_unsafe Hn).


(** Joint cache *)
Definition JCACHED {A : Type} (a : A) := a.
Global Typeclasses Opaque JCACHED.
Arguments JCACHED : simpl never.
Notation "'JCACHED'" := (JCACHED _) (only printing).

Lemma init_jcache : JCACHED True.
Proof. by apply JCACHED. Defined.

Lemma enter_jcache {A B} :
  B →
  JCACHED A →
  JCACHED (B ∧ A).
Proof.
  unfold JCACHED. done.
Qed.

Ltac open_jcache :=
  match goal with
  | H : JCACHED ?A |- _ =>
      unfold JCACHED in H;
      repeat match type of H with
      | _ ∧ _ =>
          destruct H as [? H]
      end
  end
.

Ltac open_scache :=
  unfold CACHED in *
.
Ltac open_cache :=
  open_scache;
  try open_jcache
.

Ltac init_jcache :=
  let Hcache := fresh "Hcache" in
  specialize init_jcache as Hcache.
Ltac ensure_jcache :=
  lazymatch goal with
  | H : JCACHED _ |- _ => idtac
  | |- _ => init_jcache
  end.

(** Unsafe version that bypasses the hooks *)
Ltac enter_jcache_unsafe H :=
  match goal with
  | Hcache : JCACHED _ |- _ =>
      apply (enter_jcache H) in Hcache;
      clear H
  end
.
Ltac enter_jcache H :=
  enter_cache_hook H ltac:(fun Hn =>
    enter_jcache_unsafe Hn)
.

Ltac specialize_cache T :=
  let Hn := fresh in
  specialize T as Hn;
  enter_jcache Hn.
Ltac assert_is_not_cached H :=
  lazymatch type of H with
  | CACHED _ => fail
  | JCACHED _ => fail
  | _ => idtac
  end.




(** Case distinctions *)
Ltac add_case_distinction_info info :=
  let Hcase := fresh "HCASE" in
  have Hcase := (() : (CASE_DISTINCTION_INFO info))
  (*get_loc_info ltac:(fun icur =>*)
  (*let Hcase := fresh "HCASE" in*)
  (*have Hcase := (() : (CASE_DISTINCTION_INFO hint info icur)))*)
.

Ltac set_last_rust_program_point point :=
  repeat match goal with
  | H : LAST_RUST_PROGRAM_POINT _ |- _ => clear H
  end;
  let Hpoint := fresh "HLAST" in
  have Hpoint := (() : LAST_RUST_PROGRAM_POINT point).

Ltac set_last_rust_expression_program_point e :=
  lazymatch reverse goal with
  | H : LAST_RUST_PROGRAM_POINT (RustProgramPointStmt ?s) |- _ =>
      set_last_rust_program_point (RustProgramPointExpr s e)
  | H : LAST_RUST_PROGRAM_POINT (RustProgramPointExpr ?s _) |- _ =>
      set_last_rust_program_point (RustProgramPointExpr s e)
  | H : LAST_RUST_PROGRAM_POINT
      (RustProgramPointCall ?v ?vl ?destination ?normal ?unwind) |- _ =>
      let s := constr:(Call (Val v) (Val <$> vl) destination normal unwind) in
      set_last_rust_program_point (RustProgramPointExpr s e)
  end.

(** * Tactics cleaning the proof state *)
Ltac clear_unused_vars :=
  repeat match goal with
         | H1 := FUNCTION_NAME _, H : ?T |- _ =>
           lazymatch T with
           (* Keep cache *)
           | CACHED _ => fail
           (* Keep current location and case distinction info. *)
           (*| CURRENT_LOCATION _ _ => fail*)
           (*| CASE_DISTINCTION_INFO _ _ _ => fail*)
           | _ => idtac
           end;
           let ty := (type of T) in
           match ty with | Type => clear H | Set => clear H end
         end.

Ltac li_clear_all :=
  repeat multimatch goal with
  | H : ?P |- _ =>
      match P with
      | JCACHED _ => idtac
      | _ => try clear H
      end
  end.
Ltac clear_layout :=
repeat match goal with
| H : use_struct_layout_alg _ = _ |- _ => clear H
| H : use_enum_layout_alg _ = _ |- _ => clear H
| H : use_union_layout_alg _ = _ |- _ => clear H
end.

(** * Tactics for showing failures to the user *)

(*Ltac print_current_location :=*)
  (*try lazymatch reverse goal with*)
      (*| H : CURRENT_LOCATION ?l ?up_to_date |- _ =>*)
        (*let rec print_loc_info l :=*)
            (*match l with*)
            (*| ?i :: ?l =>*)
              (*lazymatch eval unfold i in i with*)
              (*| LocationInfo ?f ?ls ?cs ?le ?ce =>*)
                (*let f := eval unfold f in f in*)
                (*idtac "Location:" f "[" ls ":" cs "-" le ":" ce "]";*)
                (*print_loc_info l*)
              (*end*)
            (*| [] => idtac "up to date:" up_to_date*)
            (*end in*)
        (*print_loc_info l;*)
        (*clear H*)
      (*end.*)

Ltac print_case_distinction_info :=
  tryif lazymatch goal with
        | H : CASE_DISTINCTION_INFO _ |- _ => idtac
        end
  then (
    idtac "Case distinctions:";
    try match reverse goal with
    | H : CASE_DISTINCTION_INFO ?i (* ?l *) |- _ =>
      lazymatch i with
      | (?a, ?b) => idtac " " a "->" b
      | ?a => idtac " " a
      end;
      fail
    end)
  else idtac "Case distinctions: none".

Ltac print_last_rust_program_point :=
  lazymatch reverse goal with
  | H : LAST_RUST_PROGRAM_POINT (RustProgramPointStmt ?s) |- _ =>
      idtac "Last backtracking point (statement):" s
  | H : LAST_RUST_PROGRAM_POINT (RustProgramPointExpr ?s ?e) |- _ =>
      idtac "Last backtracking point (expression):" e;
      idtac "In statement:" s
  | H : LAST_RUST_PROGRAM_POINT
      (RustProgramPointCall ?v ?vl ?destination ?normal ?unwind) |- _ =>
      let s := constr:(Call (Val v) (Val <$> vl) destination normal unwind) in
      idtac "Last backtracking point (call):" s
  | _ => idtac "Last backtracking point: none"
  end.

Ltac print_open_lithium_evars :=
  tryif multimatch goal with
        | H := EVAR_ID ?x |- _ => is_evar x; idtac
        end
  then (
    idtac "Open Lithium evars:";
    try match reverse goal with
    | H := EVAR_ID ?x |- _ =>
      is_evar x;
      let A := type of H in
      idtac " " H ":" A;
      fail
    end)
  else idtac "Open Lithium evars: none".

Ltac print_guarded_location_hint l :=
  let rec go Hs :=
    lazymatch Hs with
    | Esnoc ?Hs' ?id ?Q =>
        first [
          lazymatch Q with
          | guarded ?prepaid (ltype_own ?lt ?k ?π ?r ?l') =>
              constr_eq l l';
              idtac "Hint: ownership of" l "is guarded; unguard it first, for example with 'apply_update updateable_strip_guards'."
          end
        | go Hs' ]
    end in
  lazymatch goal with
  | |- envs_entails (Envs ?Hi ?Hs _) _ => first [go Hs | go Hi]
  | H := Envs ?Hi ?Hs _ |- _ => first [go Hs | go Hi]
  end.

Ltac print_array_access_hint l :=
  lazymatch l with
  | @OffsetLocSt ?alg ?base ?st ?off =>
      let rec go Hs :=
        lazymatch Hs with
        | Esnoc ?Hs' ?id ?Q =>
            first [
              lazymatch Q with
              | ltype_own ?lt ?k ?π ?r ?base' =>
                  constr_eq base base';
                  idtac "Hint: the requested location is an array-style offset of the owned base location" base ".";
                  idtac "      Before stepping into this lookup, try 'apply_update (updateable_typed_array_access" base off st ")'."
              end
            | go Hs' ]
        end in
      lazymatch goal with
      | |- envs_entails (Envs ?Hi ?Hs _) _ => first [go Hs | go Hi]
      | H := Envs ?Hi ?Hs _ |- _ => first [go Hs | go Hi]
      end
  end.

Ltac print_extract_value_hint P Q :=
  lazymatch P with
  | ltype_own (◁ ?ty)%I Owned ?π (PlaceIn ?r) ?l =>
      first [
        lazymatch Q with
        | ltype_own (◁ value_t true ?st)%I Owned ?π' (PlaceIn ?v) ?l' =>
            constr_eq l l';
            constr_eq π π';
            idtac "Hint: this subsumption targets typed value ownership at location" l ".";
            idtac "      Before stepping into this subsumption, try 'apply_update (updateable_extract_typed_value" l ")'."
        | ltype_own (◁ value_t false ?st)%I Owned ?π' (PlaceIn ?v) ?l' =>
            constr_eq l l';
            constr_eq π π';
            idtac "Hint: this subsumption targets untyped value ownership at location" l ".";
            idtac "      Before stepping into this subsumption, try 'apply_update (updateable_extract_untyped_value" l ")'."
        | ty_own_val ?ty' ?π' ?r' MetaNone ?v =>
            constr_eq ty ty';
            constr_eq π π';
            constr_eq r r';
            idtac "Hint: extracting the value stored at location" l "can expose this value assertion.";
            idtac "      Consider 'apply_update (updateable_extract_typed_value" l ")' when the type is sized and allows reads,";
            idtac "      or 'apply_update (updateable_extract_untyped_value" l ")' otherwise."
        end
      ]
  end.

Ltac print_stratify_hint :=
  let print_hint l :=
    idtac "Hint: location" l "has a non-OfTy ltype; try 'iApply (prove_with_subtype_stratify" l ")'." in
  let rec go Hs :=
    lazymatch Hs with
    | Esnoc ?Hs' ?id ?Q =>
        first [
          lazymatch Q with
          | ltype_own ?lt ?k ?π ?r ?l =>
              lazymatch lt with
              | AliasLtype _ _ _ => print_hint l
              | BlockedLtype _ _ => print_hint l
              | ShrBlockedLtype _ _ => print_hint l
              | MutLtype _ _ => print_hint l
              | ShrLtype _ _ => print_hint l
              | StructLtype _ _ => print_hint l
              | ArrayLtype _ _ _ => print_hint l
              | EnumLtype _ _ => print_hint l
              | OpenedLtype _ _ _ _ _ => print_hint l
              | CoreableLtype _ _ => print_hint l
              | ShadowedLtype _ _ _ => print_hint l
              | OpenedNaLtype _ _ _ _ => print_hint l
              | _ => go Hs'
              end
          end
        | go Hs' ]
    end in
  lazymatch goal with
  | |- envs_entails (Envs ?Hi ?Hs _) _ => first [go Hs | go Hi]
  | H := Envs ?Hi ?Hs _ |- _ => first [go Hs | go Hi]
  end.

Ltac print_acquire_credits_hint P :=
  first [
    lazymatch P with
    | guarded true _ => idtac
    | have_creds => idtac
    end
  ];
  let rec go Hs :=
    lazymatch Hs with
    | Esnoc ?Hs' ?id ?Q =>
        first [
          lazymatch Q with
          | credit_store ?n ?m =>
              idtac "Hint: the context contains a credit store with" n "credits and" m "time receipts.";
              idtac "      If it has at least 5 credits and 1 time receipt, try 'iAcquireCredits as' with a fresh Iris hypothesis name."
          end
        | go Hs' ]
    end in
  lazymatch goal with
  | |- envs_entails (Envs ?Hi ?Hs _) _ => first [go Hs | go Hi]
  | H := Envs ?Hi ?Hs _ |- _ => first [go Hs | go Hi]
  end.

Ltac print_lithium_sidecondition_explanation P :=
  first [
    lazymatch P with
    | context [protected _] =>
        idtac "Lithium is trying to instantiate a protected evar using this side condition:"
    end
  | has_evar P;
    idtac "Lithium is trying to instantiate an evar using this side condition:"
  | idtac "Lithium cannot solve this side condition:"
  ];
  idtac " " P.

Ltac print_lithium_goal_explanation :=
  lazymatch goal with
  | |- ?P ∧ _ =>
      print_lithium_sidecondition_explanation P
  | |- envs_entails _ (find_in_context (FindLoc ?l) _) =>
      idtac "Lithium is trying to find ownership for location" l "in the context.";
      first [print_guarded_location_hint l | print_array_access_hint l | idtac]
  | |- envs_entails _ (find_in_context ?fic _) =>
      idtac "Lithium is trying to find an assertion described by" fic "in the context."
  | |- envs_entails _ (subsume_full _ ?P ?Q _ _ _) =>
      idtac "Lithium could not select a SubsumeFull rule from:";
      idtac " " P;
      idtac "to:";
      idtac " " Q;
      try print_extract_value_hint P Q
  | |- envs_entails _ (prove_with_subtype _ _ ?step _ ?P _ _) =>
      idtac "Lithium could not select a ProveWithSubtype rule for this assertion:";
      idtac " " P;
      first [
        print_acquire_credits_hint P
      | lazymatch step with
        | true => print_stratify_hint
        end
      |
        lazymatch P with
        | bi_forall _ =>
            idtac "Hint: there is intentionally no general ProveWithSubtype rule for universal assertions."
        | ltype_own _ _ _ _ ?l =>
            first [print_guarded_location_hint l
                  | idtac "Hint: if the assertion should be proved manually, try 'iApply prove_with_subtype_default'."]
        end
      | idtac "Hint: if the assertion should be proved manually, try 'iApply prove_with_subtype_default'."
      ]
  | |- ?P =>
    idtac "Leftover goal: ";
    idtac " " P
  end.

Ltac liExplainGoal :=
  print_lithium_goal_explanation.

Ltac liExplain :=
  unfold_instantiated_evars;
  try liUnfoldSyntax;
  liSimpl; li_unfold_lets_in_context;
  print_case_distinction_info;
  print_last_rust_program_point;
  print_open_lithium_evars; 
  liExplainGoal;
  liShow.

Ltac print_rocq_hyps :=
  try match reverse goal with
  | H : ?X |- _ =>
    lazymatch X with
    | BLOCK_PRECOND _ _ => fail
    | CASE_DISTINCTION_INFO _ => fail
    | LAST_RUST_PROGRAM_POINT _ => fail
    | gFunctors => fail
    | typeGS _ => fail
    | ghost_varG _ _ => fail
    (*| globalGS _ => fail*)
    | _ => idtac H ":" X; fail
    end
  end.

Ltac print_goal :=
  (*print_current_location;*)
  print_case_distinction_info;
  idtac "Goal:";
  print_rocq_hyps;
  idtac "---------------------------------------";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "";
  idtac "".

Ltac print_typesystem_goal fn :=
  idtac "Type system got stuck in function" fn  "!";
  liExplain
  (*print_goal*)
.

Ltac print_sidecondition_goal fn :=
  idtac "Cannot solve side condition in function" fn "!";
  print_goal; admit.

Ltac print_remaining_shelved_goal fn :=
  idtac "Shelved goal remaining in " fn "!";
  print_goal; admit.
