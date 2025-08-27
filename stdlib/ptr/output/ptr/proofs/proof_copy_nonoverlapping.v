From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_copy_nonoverlapping.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma copy_nonoverlapping_proof (π : thread_id) :
  copy_nonoverlapping_lemma π.
Proof.
  copy_nonoverlapping_prelude.

  repeat liRStep; liShow.
  open_cache.

  (* manual proof from here to formulate the loop invariant *)
  iApply typed_stmt_annot_skip.
  iSelect (_ ◁ₗ[_, _] # size @ _)%I (fun H => iRename H into "Hlen").
  iSelect (_ ◁ₗ[_, _] #0%Z @ _)%I (fun H => iRename H into "Hcount").
  iSelect (_ ◁ₗ[_, _] #src @ (◁ alias_ptr_t))%I (fun H => iRename H into "Hsrc").
  iSelect (_ ◁ₗ[_, _] #dst @ (◁ alias_ptr_t))%I (fun H => iRename H into "Hdst").
  iSelect (src ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Hs").
  iSelect (dst ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Ht").
  iApply fupd_typed_stmt.
  iMod (ofty_uninit_to_value with "Ht") as "(%v_t & Ht)"; first done.
  iMod (ofty_value_has_length with "Hs") as "(%Hlen_s & Hs)"; first done.
  { sidecond_hook. }
  iMod (ofty_value_has_length with "Ht") as "(%Hlen_t & Ht)"; first done.
  { sidecond_hook. }
  simplify_layout_goal.

  (* turn it into arrays *)
  iPoseProof (ofty_value_untyped_to_array with "Hs") as "Hs".
  { simplify_layout_goal. by eapply syn_type_has_layout_make_untyped. }
  iPoseProof (ofty_value_untyped_to_array with "Ht") as "Ht".
  { simplify_layout_goal. by eapply syn_type_has_layout_make_untyped. }
  iModIntro.

  set (loop_inv := (λ (E : elctx) (L : llctx),
    ∃ (i : nat),
    ⌜L = [ϝ ⊑ₗ{0} []]⌝ ∗
    ⌜E = ty_outlives_E T_ty ϝ ++ ty_wf_E T_ty⌝ ∗
    (credit_store 0 0 ∗
    arg_size ◁ₗ[π, Owned false] #size @ (◁ int USize) ∗
    local_count ◁ₗ[π, Owned false] #(Z.of_nat i) @ (◁ int USize) ∗
    arg_src ◁ₗ[π, Owned false] #src @ (◁ alias_ptr_t) ∗
    arg_dst ◁ₗ[π, Owned false] #dst @ (◁ alias_ptr_t) ∗
    src ◁ₗ[ π, Owned false] # (fmap (M:=list) PlaceIn (reshape (replicate (Z.to_nat size) (ly_size T_st_ly)) vs : list val)) @ (◁ array_t (Z.to_nat size) (value_t (UntypedSynType T_st_ly))) ∗
    dst ◁ₗ[π, Owned false] #(fmap (M:=list) PlaceIn (take i (reshape (replicate (Z.to_nat size) (ly_size T_st_ly)) vs : list val) ++ drop i (reshape (replicate (Z.to_nat size) (ly_size T_st_ly)) v_t))) @ (◁ array_t (Z.to_nat size) (value_t (UntypedSynType T_st_ly)))))%I).
  iApply (typed_goto_acc _ _ _ _ loop_inv).
  { unfold_code_marker_and_compute_map_lookup. }
  liRStep; liShow. iExists 0%nat.
  liRStepUntil (introduce_with_hooks).
  liRStep; liShow.
  iApply introduce_with_hooks_base.
  iIntros  "(%i & -> & -> & Hcredit & Hlen & Hcount & Hsrc & Hdst & Hs & Ht)".
  repeat liRStep; liShow.
   (*return: go back to values *)
  assert (take i (reshape (replicate (Z.to_nat size) (ly_size T_st_ly)) vs : list val) ++ drop i (reshape (replicate (Z.to_nat size) (ly_size T_st_ly)) v_t) = (reshape (replicate (Z.to_nat size) (ly_size T_st_ly)) (take (i * ly_size T_st_ly) vs ++ drop (i * ly_size T_st_ly) v_t) : list val)) as ->.
  { shelve. }
  iPoseProof (ofty_value_untyped_from_array with "Hs") as "Hs".
  { rewrite Hlen_s ly_size_mk_array_layout. lia. }
  iPoseProof (ofty_value_untyped_from_array with "Ht") as "Ht".
  { rewrite length_app length_take length_drop. rewrite Hlen_t Hlen_s !ly_size_mk_array_layout. lia. }

  iApply typed_stmt_annot_skip.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  + cbn. rewrite -list_fmap_insert.
    rewrite insert_app_r_alt; first last.
    { rewrite length_take. lia. }
    rewrite length_take length_reshape.
    rewrite Nat.min_l; first last. { rewrite length_replicate. lia. }
    rewrite Nat.sub_diag.
    f_equiv.
    rename select ((reshape _ vs : list val) !! i = Some _) into Hlook.
    rename select (i < (Z.to_nat size))%nat into Hi.
    clear -Hlook Hi.
    rewrite Nat.add_1_r.
    erewrite take_S_r; last done.
    rewrite -app_assoc.
    f_equiv.
    rewrite insert_take_drop; first last. { rewrite length_drop length_reshape length_replicate. lia. }
    rewrite take_0 drop_drop. rewrite Nat.add_1_r. done.
  + rewrite take_ge; last solve_goal with nia.
    rewrite drop_ge; last solve_goal with nia.
    by rewrite app_nil_r.
  + rewrite  drop_ge; first last. { rewrite length_reshape length_replicate. lia. }
    rewrite app_nil_r.
    rewrite drop_ge; first last. { solve_goal with nia. }
    rewrite app_nil_r.
    assert (Z.to_nat size ≤ i) as Hle by lia. clear -Hle Hlen_s.
    rewrite take_ge. 2: { rewrite length_reshape length_replicate. lia. }
    rewrite take_ge; first done.
    rewrite Hlen_s /mk_array_layout{1}/ly_size/=. nia.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
