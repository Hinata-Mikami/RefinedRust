From refinedrust Require Export static type program_rules int int_rules products mut_ref shr_ref functions uninit box programs enum maybe_uninit alias_ptr fixpoint existentials arrays value generics xmap.
From refinedrust Require Export automation.loc_eq manual automation.
From refinedrust Require Export simpl.

(* In my experience, this has led to more problems with [normalize_autorewrite] rewriting below definitions too eagerly. *)
Export Unset Keyed Unification.

(* For some reason, we need to declare this instance here for stuff to work, despite exporting [simpl] as the last thing above! So weird! *)
Global Instance simpl_exist_plist_cons' {X : Type} (F : X → Type) (x : X) xs (Q : plist F (x :: xs) → Prop) :
SimplExist (plist F (x :: xs)) Q (∃ p : F x, ∃ ps : plist F xs, Q (p -:: ps)).
Proof.
  (*apply simpl_exist_plist_cons.*)
  intros (p & ps & Hx). exists (p -:: ps). done.
Qed.
Global Instance simpl_forall_plist_cons {X} (F : X → Type) x xs T :
  SimplForall (plist F (x :: xs)) 1 T (∀ (a : F x) (s : plist F xs), T (a -:: s)).
Proof. intros Q [? ?]. apply Q. Qed.
Global Instance simpl_forall_plist_nil {X} (F : X → Type) T :
  SimplForall (plist F []) 0 T (T -[]).
Proof. intros Q []. apply Q. Qed.
Global Instance simpl_forall_hlist_cons {X} (F : X → Type) x xs T :
  SimplForall (hlist F (x :: xs)) 1 T (∀ (a : F x) (s : hlist F xs), T (a +:: s)).
Proof. intros Q a. inv_hlist a. intros. apply Q. Qed.
Global Instance simpl_forall_hlist_nil {X} (F : X → Type) T :
  SimplForall (hlist F []) 0 T (T +[]).
Proof. intros Q a. inv_hlist a. apply Q. Qed.

Global Open Scope Z_scope.

Notation Obs := gvar_pobs.

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

(*Global Typeclasses Opaque enum_t.*)
(*Global Typeclasses Opaque active_union_t.*)
(*Global Typeclasses Opaque array_t.*)
(*Global Typeclasses Opaque offset_ptr_t.*)
(*Global Typeclasses Opaque box.*)


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
