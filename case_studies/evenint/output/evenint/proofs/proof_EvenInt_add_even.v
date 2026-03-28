From Sniper Require Import Sniper.
From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

(** SMTCoq lemmas *)

(* The lemma Zeven relies on the internal representation of Z *)
(* As this is too complicated, let's instead use a witness *)
Lemma Zeven_div2_equiv (z: Z) : Zeven z ↔ z = 2 * (Z.div2 z).
Proof.
  by induction z; [| split; destruct p.. ].
Qed.

Lemma Zeven_div2_linearity: ∀ (x y: Z),
  Zeven x ∨ Zeven y →
  Z.div2 (x + y) = Z.div2 x + Z.div2 y.
Proof.
  destruct 1; destruct x, y; try lia; destruct p, p0; try done; lia.
Qed.


(** Filters + Triggers *)

Ltac2 Set filter_defined_terms as frtd :=
  fun () =>
    'Z.le :: 'Z.opp :: 'Z.div2
    :: 'has_layout_loc :: 'void_ptr :: 'usize
    :: 'MinInt :: 'MaxInt
    :: 'bb_inv_map_marker :: 'bb_inv_t
    :: 'bool_decide :: '@elem_of :: 'int_elem_of_it
    :: frtd ().

Ltac2 Set filter_inductive_types as frtd :=
  fun () =>
    'loc :: 'poly_list
    :: 'int_type :: 'struct_layout
    :: frtd ().

Ltac revert_hypothesis Hs :=
  lazymatch Hs with
  | (?Hs1, ?Hs2) =>
      revert_hypothesis Hs1;
      revert_hypothesis Hs2
  | ?H =>
      revert H
  end.

Ltac my_Zeven_rewrite_hyps H :=
  setoid_rewrite Zeven_div2_equiv in H.

Ltac my_Zeven_rewrite_goal :=
  let H := fresh "H_Zeven_div2_linearity" in
  generalize Zeven_div2_linearity;
  setoid_rewrite Zeven_div2_equiv;
  intros H.

Ltac my_bool_decide_rewrite body :=
  let Hbody := fresh "H_body_bool_decide" in
  let Hhyp := fresh "H_assert_bool_decide" in
  set (Hbody := bool_decide body);
  assert (Hhyp: Hbody = true ↔ body) by apply bool_decide_eq_true;
  clearbody Hbody.

Ltac my_unfolder_hyps H to_unfold :=
  unfold to_unfold in H.

Ltac2 my_Zeven_hyp_trigger () :=
  TContains (TSomeHyp, Arg id) (TConstant (Init.Some "Zeven") NotArg).

Ltac2 my_Zeven_goal_trigger () :=
  TContains (TGoal, NotArg) (TConstant (Init.Some "Zeven") NotArg).

Ltac2 my_bool_decide_trigger () :=
  let trigger loc := TContains (loc, NotArg) (TApp (TConstant (Init.Some "bool_decide") NotArg) (TAny (Arg id)) NotArg) in
  TDisj (trigger TGoal) (trigger TSomeHyp).

Ltac2 my_unfolder_trigger constant :=
  TContains (TSomeHyp, Arg id) (TConstant (Init.Some constant) (Arg id)).

Ltac2 Set sniper_transformations as st := fun () =>
  ((my_Zeven_hyp_trigger (), Init.false, Init.None), "my_Zeven_rewrite_hyps", trivial_filter) ::
  ((my_Zeven_goal_trigger (), Init.false, Init.None), "my_Zeven_rewrite_goal", trivial_filter) ::
  ((my_bool_decide_trigger (), Init.false, Init.None), "my_bool_decide_rewrite", trivial_filter) ::
  ((my_unfolder_trigger "elem_of", Init.false, Init.None), "my_unfolder_hyps", trivial_filter) ::
  ((my_unfolder_trigger "int_elem_of_it", Init.false, Init.None), "my_unfolder_hyps", trivial_filter) ::
  (st ()).


(** Defining CompDec for int_type *)

(*** EqbType *)

Global Instance SMTCoq_EqbType_from_EqDecision `{EqDecision T} : SMT_classes.EqbType T.
Proof. split with (fun x y => bool_decide (x = y)). intros; apply bool_decide_eq_true. Defined.

(*** Inhabitant *)

Global Instance SMTCoq_Inhabited_from_stdpp_Inhabited `{Inhabited T} : SMT_classes.Inhabited T.
Proof. split. apply inhabitant. Defined.

Global Instance int_type_inhabited : Inhabited int_type := populate (I8).

(*** The order *)

Definition int_type_rank (t : int_type) : Z :=
  match t with
  | I8 => 0 | I16 => 1 | I32 => 2 | I64 => 3 | I128 => 4
  | U8 => 5 | U16 => 6 | U32 => 7 | U64 => 8 | U128 => 9
  | ISize => 10 | USize => 11 | CharIt => 12
  end.

Definition int_type_lt (x y : int_type) : Prop :=
  int_type_rank x < int_type_rank y.

(*** OrdType *)

Instance int_type_lt_strict_order :
  StrictOrder int_type_lt.
Proof.
  split; intros ??; unfold int_type_lt in *; lia.
Qed.

Instance int_type_ord : OrdType int_type.
Proof.
  split with int_type_lt.
  - apply StrictOrder_Transitive.
  - intros ??? ->.
    by apply StrictOrder_Irreflexive with y.
Qed.

(*** Compare *)

Definition int_type_compare (x y : int_type) : OrderedType.Compare SMT_classes.lt eq x y.
Proof.
  destruct (Z.compare (int_type_rank x) (int_type_rank y)) as [Hlt | Heq | Hgt] eqn:H.
  - apply OrderedType.EQ. by destruct x, y.
  - apply OrderedType.LT.
    admit.
  - apply OrderedType.GT.
    admit.
Admitted.

(*** Final *)

Instance IntType_CompDec : CompDec int_type.
Proof.
  split with int_type_ord.
  - apply _.
  - split. apply int_type_compare.
  - apply _.
Qed.


(** The proof *)

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.

  Unshelve. all: try solve [ sidecond_solver ].
  Unshelve.
    all: unshelve_sidecond.
    all: clear_unused_vars.
    all: clear FN_NAME.
    all: repeat match goal with
    | H : JCACHED _ |- _ => clear H
    | H : CACHED _ |- _ => clear H
    | H : bb_inv_map_marker _ |- _ => clear H
    end.
    all: snipe.

  Unshelve. all: print_remaining_sidecond.
Qed.

End proof.
