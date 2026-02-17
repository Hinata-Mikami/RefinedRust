From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.boxed.boxed.generated Require Import generated_code_boxed generated_specs_boxed generated_template_box_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma box_new_proof (π : thread_id) :
  box_new_lemma π.
Proof.
  box_new_prelude.

  rep <-! liRStep; liShow.
  { apply_update (updateable_subsume_uninit_to x' (st_of T_ty MetaNone)).
    rep liRStep; liShow. }
  { rep <-! liRStep; liShow.
    apply_update (updateable_subsume_uninit_to x' (st_of T_ty MetaNone)).
    rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rename select (x' `has_layout_loc` _) into Hlyl.
    move: Hlyl. rewrite /has_layout_loc. simpl.
    rewrite ly_align_of_rust_layout_align; first solve_goal.
    + unfold ly_align. eexists. solve_goal.
    + split; first solve_goal.
      rewrite MaxInt_eq. eapply use_layout_alg_align.
      done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
