From Sniper Require Import Sniper.
From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.evenint.generated Require Import generated_code_evenint generated_specs_evenint generated_template_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

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

Ltac2 Set filter_reflexivity_terms_def as frtd :=
  fun () =>
    'Z.le :: 'Z.opp :: 'Z.div2
    :: 'has_layout_loc :: 'void_ptr :: 'usize
    :: 'MinInt :: 'MaxInt
    :: 'bb_inv_map_marker :: 'bb_inv_t
    :: 'bool_decide :: '@elem_of
    :: frtd ().

Ltac2 Set filter_algebraic_types_def as frtd :=
  fun () =>
    'loc :: 'poly_list
    :: 'int_type :: 'struct_layout
    :: frtd ().

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.

  Unshelve. 1-17,19-24: sidecond_solver.
  Unshelve.
    all: unshelve_sidecond.
    all: clear_unused_vars.
    all: clear FN_NAME.
    all: repeat match goal with
    | H : JCACHED _ |- _ => clear H
    | H : CACHED _ |- _ => clear H
    | H : bb_inv_map_marker _ |- _ => clear H
    end.
  {
    (* Command idea: Snipe Register Zeven [Zeven_div2_linearity; ...] *)
    revert H5 H6.
    generalize Zeven_div2_linearity.

    (* Command idea: Snipe Rewrite Zeven Zeven_div2_equiv. *)
    setoid_rewrite Zeven_div2_equiv.

    (* Command idea: Snipe Rewrite bool_decide ltac:(...). *)
    set (X := bool_decide (self + other ∈ i32)).
    assert (X = true ↔ self + other ∈ i32) by apply bool_decide_eq_true.
    clearbody X.

    (* TODO: Improve Snipe *)
    unfold elem_of in H.
    unfold int_elem_of_it in H.

    snipe.
    admit.
  }
  {
    (* Command idea: Snipe Register Zeven [Zeven_div2_linearity; ...] *)
    revert H5 H6.
    generalize Zeven_div2_linearity.

    (* Command idea: Snipe Rewrite Zeven Zeven_div2_equiv. *)
    setoid_rewrite Zeven_div2_equiv.

    (* Finally ! *)
    unshelve snipe.
    all: admit.
  }

  Unshelve. all: print_remaining_sidecond.
Admitted.
End proof.
