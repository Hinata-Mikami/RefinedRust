From radium Require Export tactics.
From refinedrust Require Export static type program_rules int int_rules unit never struct.struct mut_ref.mut_ref shr_ref.shr_ref functions uninit programs enum maybe_uninit alias_ptr fixpoint mutual_fixpoint primitive.existentials existentials_na array.array base.value generics xmap.
From refinedrust Require Export automation.loc_eq manual automation.
From iris.proofmode Require Import rocq_tactics reduction string_ident.
From refinedrust Require Export automation.simpl.
From refinedrust Require Export options.

(* In my experience, this has led to more problems with [normalize_autorewrite] rewriting below definitions too eagerly. *)
#[export] Unset Keyed Unification.

(* Hide continuations etc. *)
Global Open Scope rr_hidden.

(* For some reason, we need to declare this instance here for stuff to work, despite exporting [simpl] as the last thing above! So weird! *)
#[universes(polymorphic)]
Global Instance simpl_exist_plist_cons' {X : Type} (F : X → Type) (x : X) xs  :
SimplExist (plist F (x :: xs)) (λ (Q : plist F (x :: xs) → Prop), ∃ p : F x, ∃ ps : plist F xs, Q (p -:: ps)).
Proof.
  (*apply simpl_exist_plist_cons.*)
  intros ? (p & ps & Hx). exists (p -:: ps). done.
Qed.
Global Instance simpl_forall_plist_cons {X} (F : X → Type) x xs :
  SimplForall (plist F (x :: xs)) 1 (λ T, ∀ (a : F x) (s : plist F xs), T (a -:: s)).
Proof. intros ? Q [? ?]. apply Q. Qed.
Global Instance simpl_forall_plist_nil {X} (F : X → Type) :
  SimplForall (plist F []) 0 (λ T, T -[]).
Proof. intros ? Q []. apply Q. Qed.
Global Instance simpl_forall_hlist_cons {X} (F : X → Type) x xs :
  SimplForall (hlist F (x :: xs)) 1 (λ T, ∀ (a : F x) (s : hlist F xs), T (a +:: s)).
Proof. intros ? Q a. inv_hlist a. intros. apply Q. Qed.
Global Instance simpl_forall_hlist_nil {X} (F : X → Type) :
  SimplForall (hlist F []) 0 (λ T, T +[]).
Proof. intros ? Q a. inv_hlist a. apply Q. Qed.

Global Open Scope Z_scope.

Abbreviation Obs := gvar_pobs.

Hint Extern 10 (Inhabited (RT_xt _)) => simpl; apply ty_xt_inhabited; done : typeclass_instances.

(** extend [solve_type_proper] *)
Ltac solve_type_proper_hook ::=
  match goal with
    | |- ltype_own (OfTy _) ?bk _ _ _ ≡{_}≡ ltype_own (OfTy _) ?bk _ _ _ =>
      match bk with
      | Shared _ => apply ofty_own_ne_shared; try apply _
      | Uniq _ _ => apply ofty_own_contr_uniq; try apply _
      | Owned => apply ofty_own_ne_owned; try apply _
      end
    | |- guarded _ _ ≡{_}≡ guarded _ _ =>
      apply guarded_dist; intros
  end.

Ltac solve_type_proper_prepare ::=
  intros;
  simpl in *;
  prepare_initial_coq_context;
  simpl.

(** Bundle for all ghost state we need *)
Class refinedrustGS Σ := {
  refinedrust_typeGS :: typeGS Σ;
  refinedrust_staticGS :: staticGS Σ;
}.

Ltac instantiate_benign_universals term ::=
  lazymatch type of term with
  | ∀ (_ : gFunctors) (_ : refinedrustGS _), _ =>
      instantiate_benign_universals uconstr:(term _ _)
  | ∀ _ : typeGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | ∀ _ : staticGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | ∀ _ : refinedrustGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | _ =>
      constr:(term)
  end.


Notation "x '.ghost'" := (x.2) (at level 1, only parsing).
Notation "x '.cur'" := (x.1) (at level 1, only parsing).

Abbreviation i8 := I8.
Abbreviation i16 := I16.
Abbreviation i32 := I32.
Abbreviation i64 := I64.
Abbreviation i128 := I128.
Abbreviation isize := ISize.

Abbreviation u8 := U8.
Abbreviation u16 := U16.
Abbreviation u32 := U32.
Abbreviation u64 := U64.
Abbreviation u128 := U128.
Abbreviation usize := USize.

(*Global Typeclasses Opaque enum_t.*)
(*Global Typeclasses Opaque active_union_t.*)
(*Global Typeclasses Opaque array_t.*)
(*Global Typeclasses Opaque offset_ptr_t.*)


(*Global Typeclasses Opaque shr_ref.*)
(*Global Typeclasses Opaque mut_ref.*)
(*Global Typeclasses Opaque unit_t.*)
(*Global Typeclasses Opaque struct_t.*)
(*Global Typeclasses Opaque int.*)
(*Global Typeclasses Opaque char_t.*)
(*Global Typeclasses Opaque bool_t.*)
(*Global Typeclasses Opaque ex_plain_t.*)
(*Global Typeclasses Opaque bytewise.*)
(*Global Typeclasses Opaque value_t.*)


(*Global Typeclasses Opaque mk_ex_inv_def.*)
(*Global Typeclasses Opaque mk_pers_ex_inv_def.*)
