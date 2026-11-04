From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_read.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma read_proof (π : thread_id) :
  read_lemma π.
Proof.
  read_prelude.

  destruct k.
  { rep liRStep; simp_ltypes.
    rep liRStep; liShow.
    all: rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
    rep liRStep; liShow.
  }
  { rep liRStep; simp_ltypes.
    rep liRStep; liShow.
    all: rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
    rep liRStep; liShow. }
  { rep liRStep; simp_ltypes.
    rep liRStep.
    all: rename select (st_of _ _ = st_of _ _) into Hst_eq; try rewrite -Hst_eq.
    rep liRStep; liShow.
    rewrite -Hst_eq.
    rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
