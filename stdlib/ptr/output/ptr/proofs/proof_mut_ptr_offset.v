From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_mut_ptr_offset.
From rrstd.ptr.ptr.proofs Require Import proof_const_ptr_offset.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma mut_ptr_offset_proof (π : thread_id) :
  mut_ptr_offset_lemma π.
Proof.
  (* implementation and spec are the same *)
  apply const_ptr_offset_proof.
Qed.
End proof.
