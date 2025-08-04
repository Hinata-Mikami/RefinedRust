From caesium Require Import lang notation.
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
    liRStepUntil (typed_read_end).
    (* locally override the instance used for moves *)
    (*iApply type_read_ofty_move_owned_value.*)
    (*liFromSyntax.*)
    repeat liRStep; liShow.
  }
  { rep liRStep; simp_ltypes. 
    rep liRStep; liShow. }
  { rep liRStep; simp_ltypes. 
    repeat liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rename select (st_of _ = st_of _) into Hst_eq; try rewrite -Hst_eq.
  all: sidecond_hook.
  all: f_equiv; eapply syn_type_has_layout_inj; first done; by rewrite Hst_eq.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
