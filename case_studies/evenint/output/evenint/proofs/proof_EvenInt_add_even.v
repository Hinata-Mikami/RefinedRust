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
  fun () => 'Z.le :: 'Z.opp :: 'Z.div2 :: 'has_layout_loc :: 'void_ptr :: 'usize :: 'MinInt :: 'MaxInt :: 'bb_inv_map_marker :: 'elem_of :: 'bool_decide :: frtd ().

Ltac2 Set filter_algebraic_types_def as frtd :=
  fun () => 'loc :: 'int_type :: 'poly_list :: frtd ().

(* Ltac2 Set filter_generation_principle_def as frtd := *)
(*   fun () => '(frtd (), 'loc, 'int_type). *)

Lemma EvenInt_add_even_proof (π : thread_id) :
  EvenInt_add_even_lemma π.
Proof.
  EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { (* TODO: FN_NAME holds a string, and must not be sent to SMT solvers *)
    clear FN_NAME.

    (* The environment needs to be cleared because one filter cannot register new instances. *)
    (* This will be soon fixed. *)
    clear H3 H4 arg_self arg_other.
    clear EvenInt_sl tuple2_sl H H0.
    clear loop_map.
    clear H11.

    (* Command idea: Snipe Register Zeven [Zeven_div2_linearity; ...] *)
    revert H5 H6.
    generalize Zeven_div2_linearity.

    (* Command idea: Snipe Rewrite Zeven Zeven_div2_equiv. *)
    setoid_rewrite Zeven_div2_equiv.

    (* There is currently a bug in SMTCoq that makes Rocq hanging *)
    revert H1 H2 H7 H8 H9 H10 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36.

    (* Finally ! *)
    (* NOTE: veriT takes a lot of time, but newer version answers directly. *)
    verit.
  }

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
