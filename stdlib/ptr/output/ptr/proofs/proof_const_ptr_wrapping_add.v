From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_wrapping_add.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_wrapping_add_proof (π : thread_id) :
  const_ptr_wrapping_add_lemma π.
Proof.
  const_ptr_wrapping_add_prelude.

  repeat liRStep; liShow.
  liFromSyntax.
  rewrite /typed_bin_op/typed_val_expr.
  iIntros "Hv1 Hv2" (Φ) "#CTX #HE HL Hf Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv1" as "(_ & %Hv1)".
  rewrite {1}/ty_own_val /=. iDestruct "Hv2" as "(_ & -> & %)".
  iRename select (credit_store _ _) into "Hstore".
  iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hatcl)".
  iDestruct "CTX" as "(LFT & LLCTX)".
  iApply wp_ptr_wrapping_offset.
  { apply val_to_of_loc. }
  { done. }
  iApply (physical_step_intro_tr with "Hat"). iIntros "!> [Hat Hat'] Hcred !>".
  iPoseProof ("Hatcl" with "[Hat']") as "Hstore".
  { iApply tr_weaken; last done. lia. }
  iPoseProof (credit_store_donate with "Hstore Hcred") as "Hstore".
  iPoseProof (credit_store_donate_tr with "Hstore Hat") as "Hstore".
  assert ((l wrapping_offset{T_st_ly}ₗ count).2 ∈ USize).
  { rewrite /wrapping_offset_loc /wrapping_shift_loc/=.
    by apply wrap_unsigned_in_range. }
  iApply ("Hcont" $! _ _ _ (alias_ptr_t) with "HL Hf").
  { rewrite /ty_own_val /=. iPureIntro. simplify_layout_goal. done. }

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite /WrappingOffsetLocSt.
    simplify_layout_goal. done. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
