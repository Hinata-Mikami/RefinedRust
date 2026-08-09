From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_knights_tour.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma knights_tour_proof (π : thread_id) :
  knights_tour_lemma π.
Proof.
  knights_tour_prelude.

  rep liRStep.
  split.
  { liInst Hevar_x1 r'. liInst Hevar_x2 r'0.
    rewrite Z2Nat.inj_succ in Hkpath; last lia.
    rewrite Z2Nat.inj_mul in Hkpath; try lia.
    solve_goal.
  }
  repeat liRStep.

  all: print_remaining_goal.

  Unshelve.
  all: sidecond_solver.
  (* !start proof(knights_tour.knights_tour) *)
  all: try (revert select (_ ∈ []); solve_goal).
  all: try rename select (∀ a b : Z, _ -> a ≤ 2 ∧ _) into Hbound.
  all: cbn in *.
  all: unfold name_hint in *.
  all: try rename select (in_bounds (Z.to_nat size) _) into Hinbounds.
  all: try solve_goal.
  - rename select (∀ i j : nat, _) into Hlookup.
    specialize Hlookup with (Z.to_nat a) (Z.to_nat b).
    case_decide.
    { split; first done.
      rewrite! Z2Nat.id in Hlookup; try lia. done. }
    rename select (_ ≠ (a,b)) into Hneq.
    revert Hneq; solve_goal.
  - apply extend_kpath_trivial.
  - opose proof (Hbound _ _ _); [ apply elem_of_app; right; apply elem_of_cons; eauto | ].
    solve_goal.
  - opose proof (Hbound _ _ _); [ apply elem_of_app; right; apply elem_of_cons; eauto | ].
    solve_goal.
  - have Hmem : *[x'4; s] ∈ _iter_hist_37 ++ -[x'4; s] :: x'2; first solve
    [ rewrite elem_of_app; right; rewrite elem_of_cons; left; done].
    rename select (∀ a b : Z, _ -> (Z.abs (0 - a) = 2 ∧ _) ∨ _) into Hkmove.
    specialize Hkmove with x'4 s.
    apply Hkmove in Hmem. done.
  - etrans; first eapply size_of_array_in_bytes_mono; last done. lia.
  - apply extend_kpath_app; first done.
    apply extend_kpath_singleton; try solve_goal.
  - eapply (kpath_extension_in_bounds (Z.to_nat size, x6) _ _ candidates x'3); done.
  - eapply (kpath_extend (a,b) _ (_,_) (Z.to_nat size, x6) (Z.to_nat size, x'2)); try done.
    + unfold board_at. intros i j. cbn.
      rename select (∀ i j : nat, _) into Hlookup.
      specialize Hlookup with (Z.to_nat i) (Z.to_nat j).
      replace (Z.to_nat (Z.to_nat i)) with (Z.to_nat i) in Hlookup by lia.
      replace (Z.to_nat (Z.to_nat j)) with (Z.to_nat j) in Hlookup by lia.
      replace (S (S (Z.to_nat x'1 - Z.to_nat 2))) with (Z.to_nat x'1) by lia.
      rewrite Z2Nat.id; try lia.
      rewrite! Z2Nat.id in Hlookup; try lia. done.
    + rename select (_ ∈ candidates) into Hincand.
      eapply kpath_extension_is0; [exact Hincand | done].
    + rename select (_ ∈ candidates) into Hincand.
      eapply kpath_extension_kmove; [exact Hincand | done].
  Unshelve. all: apply inhabitant.
  (* !end proof *)
Qed.
End proof.
