From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_read_volatile.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_read_volatile_proof (π : thread_id) :
  const_ptr_read_volatile_lemma π.
Proof.
  const_ptr_read_volatile_prelude.

  rep liRStep; liShow.
  simp_ltypes.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rename select (st_of _ = st_of _) into Hst_eq; try rewrite -Hst_eq.
  all: sidecond_hook.
  { f_equiv. eapply syn_type_has_layout_inj; first done.
    by rewrite Hst_eq. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
