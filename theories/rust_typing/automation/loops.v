Require Import Stdlib.Strings.String.
From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export type.
From lithium Require Export all.
From lithium Require Import hooks.
From refinedrust.automation Require Import ident_to_string lookup_definition.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** * Loopy stuff *)
(* using our own list type here in order to be able to put iProp's in it (universe troubles) *)
#[universes(polymorphic)]
Inductive poly_list (T : Type) : Type :=
  | PolyNil
  | PolyCons (x : T) (l : poly_list T).
Arguments PolyNil {_}.
Arguments PolyCons {_}.

#[universes(polymorphic)]
Inductive poly_option (T : Type) : Type :=
  | PolyNone
  | PolySome (x : T).
Arguments PolyNone {_}.
Arguments PolySome {_}.

(* Wrapper to store predicates of arbitrary arity. *)
Definition wrap_inv {T} (x : T) := existT (P := id) _ x.
(* Type of loop invariants:
   - list of variables the invariant is over
   - list of variables whose type is preserved
   - list of uninit variables
   - a predicate on the refinements,
   - a predicate on the lifetime contexts
   - optionally, the iterator variable, for which we pass the refinement into the invariant
*)
Definition bb_inv_t := (list loc * list loc * list loc * sigT (@id Type) * sigT (@id Type) * option loc)%type.
(* Type of the loop invariant map we keep in the context *)
Definition bb_inv_map_t := poly_list (var_name * bb_inv_t)%type.

(* In [Prop] and sealed so it does not get discarded as a trivial assertion by Lithium when introducing *)
Definition bb_inv_map_marker_def (M : bb_inv_map_t) := True.
Definition bb_inv_map_marker_aux M : seal (bb_inv_map_marker_def M). Proof. by eexists. Qed.
Definition bb_inv_map_marker M := (bb_inv_map_marker_aux M).(unseal).
Definition bb_inv_map_marker_unfold M : bb_inv_map_marker M = bb_inv_map_marker_def M := (bb_inv_map_marker_aux M).(seal_eq).

Lemma pose_bb_inv (M : bb_inv_map_t) :
  bb_inv_map_marker M.
Proof.
  rewrite bb_inv_map_marker_unfold. done.
Qed.

(** Given a [runtime_function] [rfn], get the list of stack locations as a [constr]. *)
Ltac gather_locals rfn :=
  match rfn with
  | Build_runtime_function ?fn ?l =>
    eval simpl in (map fst l)
  end.

(** Find the invariant for basic block [loop_bb] in the invariant map [loop_inv_map].
  Returns a uconstr option with the result. *)
Ltac find_bb_inv loop_inv_map loop_bb :=
  match loop_inv_map with
  | PolyCons (loop_bb, ?inv) _ =>
    constr:(PolySome inv)
  | PolyCons (_, _) ?loop_inv_map2 =>
    find_bb_inv loop_inv_map2 loop_bb
  | PolyNil =>
    constr:(@PolyNone bb_inv_t)
  end.

(** Find the type assignment for the location [loc] in the [env : env], and return it as a [constr]. *)
Ltac find_type_assign_in_env loc env :=
  lazymatch env with
  | Enil => fail 10 "find_type_assign_in_env: no " loc " in env"
  | Esnoc ?env2 _ (loc ◁ₗ[?π, ?b] ?r @ ?lt)%I =>
      constr:((loc ◁ₗ[π, b] r @ lt)%I)
  | Esnoc ?env2 _ _ => find_type_assign_in_env loc env2
  end.

(** Making strings from numbers *)
Definition digit_to_ascii (n : nat) : ascii :=
  match n with
  | 0 => Ascii false false false false true true false false
  | 1 => Ascii true false false false true true false false
  | 2 => Ascii false true false false true true false false
  | 3 => Ascii true true false false true true false false
  | 4 => Ascii false false true false true true false false
  | 5 => Ascii true false true false true true false false
  | 6 => Ascii false true true false true true false false
  | 7 => Ascii true true true false true true false false
  | 8 => Ascii false false false true true true false false
  | 9 => Ascii true false false true true true false false
  | _ => Ascii false false false false true true false false
  end.
Definition nat_to_string (n : nat) : string.
Proof.
  refine (String.rev _).
  refine (lt_wf_rec n (λ _, string) _).
  intros m rec.
  refine (match m as m' return m = m' → _ with
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9  => λ _, String (digit_to_ascii m) EmptyString
          | _ => λ Heq, _
          end eq_refl).
  refine (String (digit_to_ascii (m `mod` 10)) (rec (m `div` 10) _)).
  abstract(apply Nat.div_lt; lia).
Defined.

(** Generates [count] successive fresh identifiers as Coq strings with prefix [prefix].
  Poses the result as a hypothesis [out]. *)
(* TODO: potentially take a list of suffix strings, so that we can we also get the variable names for the refinements, e.g. x, y? *)
Ltac get_idents_rec' prefix count acc out :=
  match count with
  | 0%nat =>
      set (out := acc)
  | (S ?n)%nat =>
      (* need to prefix with some symbol because just a number is not a valid ident *)
      let count_str := eval cbv in (append "_" (nat_to_string n)) in
      string_to_ident_cps count_str ltac:(fun count_ident =>
      (* make a fresh identifier *)
      let Hident := fresh prefix count_ident in
      (* convert to string so we can store it *)
      let Hident_str := constr:(ident_to_string! Hident) in
      let acc := constr:(Hident_str :: acc) in
      get_idents_rec' prefix constr:(n) constr:(acc) out)
  end.
Ltac get_idents_rec prefix count res :=
  get_idents_rec' ident:(prefix) constr:(count) constr:(@nil string) ident:(res)
.

(** Finds the type assignments for the locations [local_locs] in the spatial context [spatial_env],
  and abstracts their refinements to existentials [x_1, ..., x_n] whose names get picked from the list [ex_names : list string].
  It needs to hold that [length ex_names ≥ length local_locs = n].
  [base_app] is the name of a context item which will be specialized with the existentially abstracted refinements, to result in a fully applied term [base_app_specialized = base_app x_1 ... x_n] of type [iProp].
  [base] is a term of type [iProp].

  The tactic instantiates the current goal with the proposition claiming ownership of the locals, [base_app_specialized], and [base], with the existentials quantified in the term.

  The implementation of this is currently quite hacky, mainly to work around Ltac's bad support for working with open terms. *)
Ltac build_local_sepconj local_locs spatial_env ex_names base base_app :=
  lazymatch local_locs with
  | nil =>
      exact ((base ∗ base_app)%I)
  | cons ?local ?local_locs2 =>
      let own_prop := find_type_assign_in_env local spatial_env in

      (* get the name for this *)
      lazymatch ex_names with
      | nil => fail 10 "not enough names provided"
      | ?name :: ?ex_names2 =>
        string_to_ident_cps name ltac:(fun ident =>

        (* create the type with existentially abstracted refinement *)
        let abstracted_prop :=
          lazymatch own_prop with
          | (?loc ◁ₗ[?π, ?b] ?r @ ?lt)%I =>
              (* crucial: we specialize a hypothesis _below_ the binder here in order to work around Ltac's restrictions for working with open terms *)
              constr:((∃ ident, loc ◁ₗ[π, b] ident @ lt ∗
                ltac:(specialize (base_app ident); build_local_sepconj local_locs2 spatial_env ex_names2 base base_app))%I)
          end
        in
        exact (abstracted_prop))
    end
  end.

Ltac get_Σ :=
  let tgs := constr:(_ : typeGS _) in
  match type of tgs with
  | typeGS ?Σ => Σ
  end.
Ltac get_π :=
  match goal with
  | π : thread_id |- _ => π
  end.

(** Composes the loop invariant from the invariant [Inv : bb_inv_t] (a constr),
  the runtime function [FN : runtime_function], the current Iris environment [env : env],
  and the current contexts [current_E : elctx], [current_L : llctx],
  and calls [cont Inv opt_var], where [Inv] is the invariant and [opt_var] is the optional iterator variable. *)
Ltac compute_loop_invariant FN Inv envs current_E current_L cont :=
  (* find Σ *)
  let Σ := get_Σ in
  (* get spatial env *)
  let envs := eval hnf in envs in
  let spatial_env :=
    match envs with
    | Envs _ ?spatial _ => spatial
    | _ => fail 10 "infer_loop_invariant: could not determine spatial env"
    end
  in

  (* extract the invariants *)
  let inv_locals :=
    match Inv with
    | (?inv_locals, _, _, _, _, _) => constr:(inv_locals)
    end in
  let preserved_locals :=
    match Inv with
    | (_, ?pres_locals, _, _, _, _) => constr:(pres_locals)
    end in
  let functional_inv := match Inv with
                       | (_, _, _, wrap_inv ?inv, _, _) => uconstr:(inv)
                       end
  in
  let llctx_inv := match Inv with
                   | (_, _, _, _, wrap_inv ?inv, _) => uconstr:(inv)
                   end
  in
  let iterator_var := match Inv with
                   | (_, _, _, _, _, ?var) => uconstr:(var)
                   end
  in

  (* generate names for the existentially abstracted refinements *)
  let num_locs := eval cbv in (length inv_locals) in
  let names_ident := fresh "tmp" in
  get_idents_rec ident:(r) constr:(num_locs) ident:(names_ident);
  let names := eval cbv in names_ident in
  clear names_ident;

  let Hinv := fresh "Hinv" in

  (* optionally apply to the refinement of the iterator variable *)
  let iterator_var := constr:(iterator_var) in
  match iterator_var with
  | Some ?var =>
      (*let own_prop := find_type_assign_in_env var spatial_env in*)
      (*lazymatch own_prop with*)
      (*| (?loc ◁ₗ[?π, ?b] ?r @ ?lt)%I =>*)
          (*specialize (Ha r)*)
      (*end*)
    pose (Hinv :=
      λ (iter_init_state : _) (E : elctx) (L : llctx),
      ltac:(
        (* specialize the lifetime ctx invariant *)
        let HEL := fresh "Hel" in
        pose (HEL := (E = current_E ∧ L = current_L));

        (* pose the loop invariant as a local hypothesis so we can specialize it while building the term *)
        let Ha := fresh "Hinv" in
        pose (Ha := functional_inv);

        specialize (Ha iter_init_state);

        build_local_sepconj inv_locals spatial_env names constr:(((True ∗ ⌜HEL⌝)%I: iProp Σ)) Ha
    ));
    (* get rid of all the lets we introduced *)
    simpl in Hinv;
    let Inv := eval unfold Hinv in Hinv in
    clear Hinv;
    cont Inv iterator_var

  | None => 
    pose (Hinv :=
      λ (E : elctx) (L : llctx),
      ltac:(
        (* specialize the lifetime ctx invariant *)
        let HEL := fresh "Hel" in
        pose (HEL := (E = current_E ∧ L = current_L));

        (* pose the loop invariant as a local hypothesis so we can specialize it while building the term *)
        let Ha := fresh "Hinv" in
        pose (Ha := functional_inv);

        build_local_sepconj inv_locals spatial_env names constr:(((True ∗ ⌜HEL⌝)%I: iProp Σ)) Ha
    ));
    (* get rid of all the lets we introduced *)
    simpl in Hinv;
    let Inv := eval unfold Hinv in Hinv in
    clear Hinv;
    cont Inv (@None nat)
  end

.
