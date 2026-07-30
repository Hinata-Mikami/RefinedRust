From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_dangling_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma dangling_mut_proof (π : thread_id) :
  dangling_mut_lemma π.
Proof.
  dangling_mut_prelude.

  repeat liRStep; liShow.
  specialize (ly_align_ge_1 T_st_ly) as ?. 
  rewrite decide_True; last lia.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
