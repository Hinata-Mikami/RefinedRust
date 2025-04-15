From refinedrust Require Import base.

Inductive stop_annot : Prop :=
  StopAnnot.

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

(** TODO: just a place holder until we handle drops properly. *)
Inductive drop_annot : Set :=
  | DropAnnot.
