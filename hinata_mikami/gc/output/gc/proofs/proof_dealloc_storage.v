From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_dealloc_storage.

Set Default Proof Using "Type".

Local Typeclasses Opaque alloc_dead.

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma dealloc_storage_proof (π : thread_id) :
  dealloc_storage_lemma π.
Proof.
  dealloc_storage_prelude.

  rep liRStep.
  typed_stmt_bind. rep liRStep; liShow.

  iRename select (ptr ◁ₗ[_, Owned] _ @ _)%I into "Hstorage".
  iRename select (freeable_nz ptr _ 1 HeapAlloc) into "Hfree".
  iRename select (_ ◁ᵥ{_, _} ptr @ alias_ptr_t)%I into "Hptr".
  iEval (rewrite /ty_own_val /=) in "Hptr".
  iDestruct "Hptr" as "(_ & Hptr)".
  iPoseProof (alias_ptr_own_val_to_decodes with "Hptr") as "%Hdecode".

  rewrite /typed_stmt.
  iIntros (??) "#CTX #HE HL Hf Hcont".
  iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own /=) in "Hstorage".
  iDestruct "Hstorage" as (storage_ly Hlayout Haligned) "(_ & _ & %r & _ & Hstorage)".
  iMod (fupd_mask_mono with "Hstorage") as "Hstorage"; first done.
  iDestruct "Hstorage" as (bytes) "[Hbytes Htyped]".
  iPoseProof (ty_own_val_has_layout with "Htyped") as "%Hbytes_layout"; first done.
  unfold CACHED in T_st_alg.
  have Hly : storage_ly = ly by (eapply syn_type_has_layout_inj; eassumption).
  subst storage_ly.
  try rewrite (use_layout_alg_eq' _ _ Hlayout).
  iEval (try rewrite (use_layout_alg_eq' _ _ Hlayout)) in "Hfree".

  iApply (wps_free_with_dead _ _ _ _ _ ptr _ _ _ (ly_size ly) (ly_align_log ly)
    with "[Hbytes] [Hfree]").
  - apply val_to_Z_i2v.
    pose proof (use_layout_alg_size _ _ Hlayout).
    split; unsafe_unfold_common_radium_defs; simpl in *; lia.
  - apply val_to_Z_i2v, ly_align_log_in_usize.
    by eapply use_layout_alg_align.
  - exact Hdecode.
  - lia.
  - destruct ly. iExists bytes. by iFrame.
  - iApply (freeable_nz_to_freeable with "Hfree"). lia.
  - iApply physical_step_intro. iNext. iIntros "Hdead".
    to_typed_stmt "CTX HE HL Hf Hcont".
    instantiate (1 := ϝ).
    rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
