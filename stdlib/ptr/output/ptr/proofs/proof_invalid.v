From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_invalid.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma invalid_proof (π : thread_id) :
  invalid_lemma π.
Proof.
  invalid_prelude.

  repeat liRStep. liShow.
  (* EraseProv *)
  rewrite /typed_un_op/typed_val_expr.
  iIntros "Hv" (Φ) "#CTX #HE HL Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv" as %Hv.
  iApply wp_erase_prov.
  { rewrite /has_layout_val. erewrite (val_to_Z_ot_length _ (IntOp USize)); done. }
  iApply  ("Hcont" $! _ π _ _ (int USize) _ with "HL []").
  { rewrite /ty_own_val/=. iPureIntro. by apply val_to_Z_erase_prov. }

  iIntros "Hv" (Φ') "_ _ HL Hcont".
  rewrite {1}/ty_own_val /=. iDestruct "Hv" as %Hv'.
  iApply wp_cast_int_ptr_prov_none; [done | done | | | done | ].
  { by rewrite -MaxInt_eq. }
  { apply val_to_byte_prov_erase_prov. }
  iIntros "!> Hl Hcred".
  iApply ("Hcont" $! _ π _ _ (alias_ptr_t) _ with "HL").
  { rewrite /ty_own_val /=. iPureIntro.
    split; first done.
    by eapply val_to_Z_in_range. }
  iAssert (val_of_loc (ProvAlloc None, addr : caesium.loc.addr) ◁ᵥ{π} (ProvAlloc None, addr : caesium.loc.addr) @ alias_ptr_t)%I as "?".
  { rewrite /ty_own_val /= //. iPureIntro.
    split; first done. by eapply val_to_Z_in_range. }
  set (l2 := (ProvAlloc None, addr : loc.addr) : loc).
  iAssert (l2 ◁ₗ[π, Owned false] .@ ◁ unit_t)%I with "[Hl]" as "?".
  { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl.
    iSplitR. { iPureIntro. by apply syn_type_has_layout_unit. }
    iSplitR. { iPureIntro. rewrite /has_layout_loc/aligned_to.
      eapply Z.divide_1_l. }
    iSplitR; first done.
    iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
    iSplitR; first done. iSplitR; first done.
    iExists (). iSplitR; first done.
    iModIntro. iExists []. iFrame. rewrite /ty_own_val /= //. }

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
