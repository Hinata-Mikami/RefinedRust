From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_alloc_dealloc_internal.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma alloc_dealloc_internal_proof (π : thread_id) :
  alloc_dealloc_internal_lemma π.
Proof.
  alloc_dealloc_internal_prelude.

  repeat liRStep; liShow.
  (* do the free *)
  typed_stmt_bind. repeat liRStep; liShow.
  typed_stmt_bind. repeat liRStep; liShow.
  typed_stmt_bind. repeat liRStep; liShow.
  iSelect (_ ◁ᵥ{_} size @ _)%I (fun H => iRename H into "Hsize").
  iSelect (_ ◁ᵥ{_} align_log2 @ _)%I (fun H => iRename H into "Halign_log2").
  iSelect (ptr ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Hptr").
  iSelect (freeable_nz _ _ _ _) (fun H => iRename H into "Hfree").
  rewrite {1 2}/ty_own_val /=. iDestruct "Hsize" as "%Hsize".
  iDestruct "Halign_log2" as "%Halign_log2".

  rewrite /typed_stmt.
  iIntros (?) "#CTX #HE HL Hcont".
  rewrite ltype_own_ofty_unfold /lty_of_ty_own. simpl.
  set (ly := Layout (Z.to_nat size) (Z.to_nat align_log2)).
  iDestruct "Hptr" as "(%ly' & %Hst & %Hly & _ & #Hlb & _ & %r' & <- & Hb)".
  specialize (syn_type_has_layout_untyped_inv _ _ Hst) as (-> & ? & ?).
  iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
  iDestruct "Hb" as "(%v' & Hptr & Hv')".
  iPoseProof (ty_own_val_has_layout with "Hv'") as "%Hlyv'"; first done.

  iApply (wps_free _ _ _ ptr _ _ (Z.to_nat size) (Z.to_nat align_log2) with "[Hptr] [Hfree]").
  { rewrite Hsize. f_equiv.
    apply val_to_Z_unsigned_nonneg in Hsize; last done. lia. }
  { rewrite Halign_log2. f_equiv.
    apply val_to_Z_unsigned_nonneg in Halign_log2; last done. lia. }
  { lia. }
  { iExists _. iFrame. fold ly. done. }
  { rewrite /freeable_nz.
    destruct ((Z.to_nat size)) eqn:Heq; first lia. done. }
  iIntros "!> Hcred".

  to_typed_stmt "CTX HE HL Hcont".
  (* TODO *)
  instantiate (1 := ϝ).
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
