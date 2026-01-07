From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_with_addr.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_with_addr_proof (π : thread_id) :
  const_ptr_with_addr_lemma π.
Proof.
  const_ptr_with_addr_prelude.

  repeat liRStep; liShow.
  typed_val_expr_bind.
  repeat liRStep; liShow.
  typed_val_expr_bind.
  repeat liRStep; liShow.
  rewrite /typed_val_expr.
  iIntros (?) "#CTX HE HL Hf HCont".
  iRename select (_ ◁ᵥ{π, _} addr @ int USize)%I into "Hv".
  iEval (rewrite /ty_own_val/=) in "Hv".
  iDestruct "Hv" as "(_ & %)".
  iApply wp_copy_alloc_id; [done | apply val_to_of_loc | ].
  iApply physical_step_intro; iNext.
  set (l2 := (x.1, addr) : loc).
  iAssert (l2 ◁ᵥ{π, MetaNone} (x.1, addr) @ alias_ptr_t)%I as "?".
  { rewrite /ty_own_val/=. do 2 iR.
    simpl. iPureIntro. by eapply val_to_Z_in_range. }
  iApply ("HCont" $! _ _ _ (alias_ptr_t) l2 with "HL Hf []").
  { done. }
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
