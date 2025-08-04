From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_alloc_alloc_internal.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma alloc_alloc_internal_proof (π : thread_id) :
  alloc_alloc_internal_lemma π.
Proof.
  alloc_alloc_internal_prelude.

  repeat liRStep; liShow.

  (* do the alloc *)
  typed_val_expr_bind. repeat liRStep; liShow.
  typed_val_expr_bind. repeat liRStep; liShow.
  iSelect (_ ◁ᵥ{_} size @ _)%I (fun H => iRename H into "Hsize").
  iSelect (_ ◁ᵥ{_} align_log2 @ _)%I (fun H => iRename H into "Halign_log2").
  rewrite {1 2}/ty_own_val /=. iDestruct "Hsize" as "%Hsize".
  iDestruct "Halign_log2" as "%Halign_log2".
  rewrite /typed_val_expr.
  iIntros (Φ) "#CTX HE HL Hcont".
  iApply (wp_alloc _ _ _ _ (Z.to_nat size) (Z.to_nat align_log2)).
  { rewrite Hsize. f_equiv.
    apply val_to_Z_unsigned_nonneg in Hsize; last done. lia. }
  { rewrite Halign_log2. f_equiv.
    apply val_to_Z_unsigned_nonneg in Halign_log2; last done. lia. }
  { lia. }
  iIntros "!>" (l) "Hl Hf %Hly Hcred".
  iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
  iApply ("Hcont" $! _ π _  _ (alias_ptr_t) l with "HL []").
  { rewrite /ty_own_val /=.
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%Husize".
    iPureIntro. done. }
  set (ly := (Layout (Z.to_nat size) (Z.to_nat align_log2))).
  iAssert (l ◁ₗ[π, Owned false] .@ ◁ (uninit (UntypedSynType ly)))%I with "[Hl]" as "Hl'".
  { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    assert (syn_type_has_layout (UntypedSynType ly) ly) as Hly'.
    { solve_layout_alg. }
    iExists ly. simpl. iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iSplitR. { rewrite length_replicate /ly /ly_size /=. done. }
    iSplitR; first done.
    iExists tt. iSplitR; first done.
    iModIntro. iExists _. iFrame. rewrite uninit_own_spec. iExists ly.
    iSplitR; first done. iPureIntro. rewrite /has_layout_val length_replicate /ly /ly_size //. }

  iRevert "Hf".

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
