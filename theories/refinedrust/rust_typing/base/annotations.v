From refinedrust Require Import base.


(** * Config options for the type checker *)

Inductive rr_config_dont_fold_places : Prop :=
| RR_CONFIG_DONT_FOLD_PLACES.

Inductive rr_config_dont_interpret_typing_hints : Prop :=
| RR_CONFIG_DONT_INTERPRET_TYPING_HINTS.

Inductive rr_config_dont_interpret_shrref_typing_hints : Prop :=
| RR_CONFIG_DONT_INTERPRET_SHR_REF_TYPING_HINTS.

(* If resolution is not possible as there is no observation, the type system by default will universally quantify it.
  Set this flag to instead make it a hard failure (useful to debug incomplete specs). *)
Inductive rr_config_strict_resolution : Prop :=
| RR_CONFIG_DO_STRICT_RESOLUTION.

Class CheckConfig (C : Prop) : Prop := mk_check_config { check_config_witness : C }.
Global Hint Extern 10 (CheckConfig ?C) =>
  match goal with
  | H: C |- _ =>
      refine (mk_check_config C H)
  end : typeclass_instances.

(** * Annotations *)

Inductive stop_annot : Prop :=
  StopAnnot.

(** Annotation for closing an unwind branch when the function's unwind condition is [False]. *)
Inductive panic_free_unwind_annot : Set :=
  UnwindFreeAnnot.

(** Annotation for starting a local lifetime [n ⊑ ⨅ sup].
  [n] will contain a fresh atomic lifetime, which is the handle to end [n]. *)
Inductive startlft_annot : Set :=
  StartLftAnnot (n : string) (sup : list string).

(** Similar to startlft, but do not include a new atomic lifetime in n, thus making [n = ⨅ sup]. *)
Inductive aliaslft_annot : Set :=
  AliasLftAnnot (n : string) (sup : list string).

(** Annotation for ending a local lifetime n. *)
Inductive endlft_annot : Set :=
  EndLftAnnot (n : string).

(** Annotation for extending a local lifetime n ⊑ ⨅ κs to be equal to ⨅ κs. *)
Inductive extend_annot : Set :=
  ExtendLftAnnot (n : string).

(** Annotation for stratifying the context at this point. *)
Inductive stratify_context_annot : Set :=
  StratifyContextAnnot.

(** Annotation for creating a dynamic inclusion of a lifetime κ1 ⊑ κ2 *)
Inductive includelft_annot : Set :=
  DynIncludeLftAnnot (n1 n2 : string).

(** Annotation for copying the entry n2 ↦ κ in the name map for n1, so that n1 ↦ κ. *)
Inductive copylftname_annot : Set :=
  CopyLftNameAnnot (n1 n2 : string).

(** This asserts that an expression has a particular syntactic Rust type by triggering subtyping to the intended type. *)
Inductive assert_type_annot : Set :=
  | AssertTypeAnnot (ty : rust_type).

(** Annotation for manual unconstrained lft annotations *)
Inductive unconstrained_lft_annot : Set :=
  UnconstrainedLftAnnot (n1 : string).

Definition UnconstrainedLftHint_def (n1 : string) (sup : list string) :=
  True.
Definition UnconstrainedLftHint_aux : seal UnconstrainedLftHint_def. Proof. by eexists. Qed.
Definition UnconstrainedLftHint := UnconstrainedLftHint_aux.(unseal).
Definition UnconstrainedLftHint_unfold :
  UnconstrainedLftHint = UnconstrainedLftHint_def :=
  UnconstrainedLftHint_aux.(seal_eq).
Lemma pose_unconstrained_lft_hint (n1 : string) (sup : list string) (T : Prop) :
  (UnconstrainedLftHint n1 sup → T) → T.
Proof.
  rewrite UnconstrainedLftHint_unfold.
  intros Ha. apply Ha. done.
Qed.
Ltac pose_unconstrained_lft_hint n sup :=
  apply (pose_unconstrained_lft_hint n sup); intros ?.
Ltac check_unconstrained_lft n :=
  match goal with
  | H : UnconstrainedLftHint n _ |- _ =>
      idtac
  | |- _ =>
    idtac "Lifetime " n " is unconstrained, pose a hint using 'pose_unconstrained_lft_hint' "
  end.

