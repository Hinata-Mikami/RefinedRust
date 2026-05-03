From Sniper Require Import Sniper.
From refinedrust Require Import base util.
From refinedrust.automation Require Import proof_state loops.
From refinedrust Require Import options.

(** General infrastructure compatibility *)
(*** EqbType *)
Global Instance SMTCoq_EqbType_from_EqDecision `{EqDecision T} : SMT_classes.EqbType T :=
  {|
    SMT_classes.eqb := λ x y : T, bool_decide (x = y);
    SMT_classes.eqb_spec := λ x y : T, bool_decide_eq_true (x = y)
  |}.

(*** Inhabitant *)
Global Instance SMTCoq_Inhabited_from_stdpp_Inhabited `{Inhabited T} : SMT_classes.Inhabited T :=
  {| default_value := inhabitant |}.


(** Filters *)
(** Filtered definitions are uninterpreted *)
Ltac2 Set filter_defined_terms as frtd :=
  fun () =>
    'Z.le
    :: 'Z.opp
    :: 'Z.div2
    :: 'has_layout_loc :: 'void_ptr :: 'USize
    :: 'MinInt :: 'MaxInt
    :: 'bb_inv_map_marker :: 'bb_inv_t
    :: 'bool_decide :: '@elem_of :: 'int_elem_of_it
    :: frtd ().

(* Filtered inductives are uninterpreted *)
Ltac2 Set filter_inductive_types as frtd :=
  fun () =>
    'loc :: 'poly_list
    :: 'int_type :: 'struct_layout
    :: frtd ().

(* NOTE: Make sure that triggers ALWAYS make progress!!! *)
(* Rewriter for bool_decide *)
Ltac my_bool_decide_rewrite body :=
  let Hbody := fresh "H_body_bool_decide" in
  let Hhyp := fresh "H_assert_bool_decide" in
  set (Hbody := bool_decide body) in *;
  assert (Hhyp: Hbody = true ↔ body) by apply bool_decide_eq_true;
  clearbody Hbody.
(* triggers in goal and hyp *)
Ltac2 my_bool_decide_trigger () :=
  let trigger loc := TContains (loc, NotArg) (TApp (TConstant (Init.Some "bool_decide") NotArg) (TAny (Arg id)) NotArg) in
  TDisj (trigger TGoal) (trigger TSomeHyp).


(* Trigger for unfolding a term *)
Ltac my_unfolder_hyps H to_unfold :=
  unfold to_unfold in H.
Ltac2 my_unfolder_trigger constant :=
  TContains (TSomeHyp, Arg id) (TConstant (Init.Some constant) (Arg id)).

Ltac2 Set sniper_transformations as st := fun () =>
  (* simplify bool_decide *)
  ((my_bool_decide_trigger (), Init.false, Init.None), "my_bool_decide_rewrite", trivial_filter) ::
  (* unfold elem_of *)
  ((my_unfolder_trigger "elem_of", Init.false, Init.None), "my_unfolder_hyps", trivial_filter) ::
  (* unfold int_elem_of_it *)
  ((my_unfolder_trigger "int_elem_of_it", Init.false, Init.None), "my_unfolder_hyps", trivial_filter) ::
  (st ()).


(** Infrastructure for int_type translation *)
Definition int_type_rank (t : int_type) : Z :=
  match t with
  | I8 => 0 | I16 => 1 | I32 => 2 | I64 => 3 | I128 => 4
  | U8 => 5 | U16 => 6 | U32 => 7 | U64 => 8 | U128 => 9
  | ISize => 10 | USize => 11 | CharIt => 12
  end.

Definition int_type_lt (x y : int_type) : Prop :=
  (int_type_rank x < int_type_rank y)%Z.

Global Instance int_type_lt_strict_order :
  StrictOrder int_type_lt.
Proof.
  split; intros ??; unfold int_type_lt in *; lia.
Qed.

Definition int_type_compare (x y : int_type) : OrderedType.Compare int_type_lt eq x y.
Proof.
  destruct (Z.compare (int_type_rank x) (int_type_rank y)) eqn:H.
  - apply OrderedType.EQ. by destruct x, y.
  - apply OrderedType.LT. by destruct x, y.
  - apply OrderedType.GT. by destruct x, y.
Defined.

Global Instance Comparable_int_type : Comparable int_type.
Proof. split. apply int_type_compare. Defined.

Global Instance CompDec_int_type : CompDec int_type.
Proof.
  split with (StrictOrder_to_OrdType int_type_lt_strict_order).
  - apply _.
  - split. apply int_type_compare.
  - apply _.
Qed.
