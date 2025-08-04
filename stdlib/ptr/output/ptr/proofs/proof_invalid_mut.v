From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_invalid_mut.
From rrstd.ptr.ptr.proofs Require Import proof_invalid.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma invalid_mut_proof (π : thread_id) :
  invalid_mut_lemma π.
Proof.
  apply invalid_proof.
Qed.
End proof.
