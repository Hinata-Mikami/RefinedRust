From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_sub.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_sub_proof (π : thread_id) :
  const_ptr_sub_lemma π.
Proof.
  const_ptr_sub_prelude.

  repeat liRStep; liShow.
  liFromSyntax.
  iRename select (loc_in_bounds l _ _) into "Hbounds".
  iDestruct "Hbounds" as "#Hbounds".
  repeat liRStep; liShow.
  rewrite /typed_bin_op/typed_val_expr.
  iIntros "Hv1 Hv2" (Φ) "#CTX #HE HL Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv1" as %Hv1.
  rewrite {1}/ty_own_val /=. iDestruct "Hv2" as "[-> %]".
  iDestruct (loc_in_bounds_ptr_in_range with "Hbounds") as %[Hran1 Hran2].
  rewrite /size_of_st. simplify_layout_goal.
  iRename select (credit_store _ _) into "Hstore".
  iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hatcl)".
  iDestruct "CTX" as "(LFT & TIME & LLCTX)".
  iMod (persistent_time_receipt_0) as "Hp".
  iApply (wp_ptr_neg_offset_credits with "TIME Hat Hp").
  { done. }
  { apply val_to_of_loc. }
  { done. }
  { (* count is positive, so this should work *)
    rename select (MinInt _ ≤ count * _) into Hmin.
    rename select (count * _ ≤ MaxInt _) into Hmax.
    revert Hmin Hmax.
    split; rewrite -?MinInt_eq -?MaxInt_eq. 
    { move: Hmax. unsafe_unfold_common_caesium_defs; simpl. lia. }
    { lia. }
  }
  { rewrite /offset_loc.
    iApply (loc_in_bounds_offset with "Hbounds").
    { done. }
    { destruct l; simpl. clear Hran2. lia. }
    { destruct l; simpl. clear Hran1. lia. }
  }
  { iApply (loc_in_bounds_offset with "Hbounds"); [ done | | ].
    { clear Hran2. lia. }
    { clear Hran1. lia. }
  }
  iNext. simpl. iEval (rewrite additive_time_receipt_succ). iIntros "Hcred [Hat Hat']".
  iPoseProof ("Hatcl" with "Hat'") as "Hstore".
  iPoseProof (credit_store_donate with "Hstore Hcred") as "Hstore".
  iPoseProof (credit_store_donate_atime with "Hstore Hat") as "Hstore".
  iAssert (loc_in_bounds (l offsetst{st_of T_ty}ₗ -count) 0 0) as "#Hlb'". 
  { iApply loc_in_bounds_offset; last done. all: sidecond_hammer. }
  iPoseProof (loc_in_bounds_ptr_in_range with "Hlb'") as "%".
  iApply ("Hcont" $! _ π _ _ (alias_ptr_t) with "HL").
  { rewrite /ty_own_val /=. 
    iPureIntro. split; first done. sidecond_hammer. }

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
