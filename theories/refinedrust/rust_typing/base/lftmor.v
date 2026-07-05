From refinedrust Require Export type.
From refinedrust Require Import options.

(** Dependency-aware lifetime morphisms for SCC inputs. *)
Section dep_lft_mor.
  Context `{!typeGS Σ}.

  Import EqNotations.

  Fixpoint full_deps_from (i : nat) (rts : list RT) : gset nat :=
    match rts with
    | [] => ∅
    | _ :: rts => {[i]} ∪ full_deps_from (S i) rts
    end.

  Definition full_deps (rts : list RT) : gset nat := full_deps_from 0 rts.

  Class DepsFull (rts : list RT) (deps : gset nat) : Prop := deps_full_proof : deps = full_deps rts.

  Fixpoint dep_lfts_aux {rts : list RT} (deps : gset nat) (i : nat)
      (tys : mut_types rts) : list lft :=
    match tys with
    | +[] => []
    | ty +:: tys =>
        if decide (i ∈ deps) then ty_lfts ty ++ dep_lfts_aux deps (S i) tys
        else dep_lfts_aux deps (S i) tys
    end.

  Definition dep_lfts {rts : list RT} (deps : gset nat) (tys : mut_types rts) : list lft :=
    dep_lfts_aux deps 0 tys.

  Fixpoint dep_wf_E_aux {rts : list RT} (deps : gset nat) (i : nat)
      (tys : mut_types rts) : elctx :=
    match tys with
    | +[] => []
    | ty +:: tys =>
        if decide (i ∈ deps) then ty_wf_E ty ++ dep_wf_E_aux deps (S i) tys
        else dep_wf_E_aux deps (S i) tys
    end.

  Definition dep_wf_E {rts : list RT} (deps : gset nat) (tys : mut_types rts) : elctx :=
    dep_wf_E_aux deps 0 tys.

  Lemma dep_lfts_aux_singleton_before {rts : list RT} k offset
      (tys : mut_types rts) :
    (k < offset)%nat → dep_lfts_aux ({[k]} : gset nat) offset tys = [].
  Proof.
    revert offset. induction tys as [|rt rts ty tys IH]; intros offset Hlt; simpl; first done.
    destruct (decide (offset ∈ ({[k]} : gset nat))) as [Hin | _].
    { apply elem_of_singleton in Hin. lia. }
    apply IH. lia.
  Qed.

  Lemma dep_wf_E_aux_singleton_before {rts : list RT} k offset
      (tys : mut_types rts) :
    (k < offset)%nat → dep_wf_E_aux ({[k]} : gset nat) offset tys = [].
  Proof.
    revert offset. induction tys as [|rt rts ty tys IH]; intros offset Hlt; simpl; first done.
    destruct (decide (offset ∈ ({[k]} : gset nat))) as [Hin | _].
    { apply elem_of_singleton in Hin. lia. }
    apply IH. lia.
  Qed.

  Lemma dep_lfts_aux_singleton_project_def {rts rt} (Hinh : Inhabited (RT_xt rt))
      (offset i : nat) (Hlook : rts !! i = Some rt) (tys : mut_types rts) :
    dep_lfts_aux ({[(offset + i)%nat]} : gset nat) offset tys =
      ty_lfts (rew [type] (lookup_lnth rts rt i rt Hlook) in
        @mut_component _ _ rts rt type_inhabitant tys i).
  Proof.
    revert offset i rt Hinh Hlook.
    induction tys as [|rt0 rts ty tys IH]; intros offset i rt Hinh Hlook; simpl in Hlook.
    { exfalso. rewrite lookup_nil in Hlook. done. }
    destruct i as [|i].
    - injection Hlook as <-. simpl.
      destruct (decide (offset ∈ ({[(offset + 0)%nat]} : gset nat))) as [_ | Hnot].
      2: { exfalso. apply Hnot. set_solver. }
      rewrite dep_lfts_aux_singleton_before; last lia.
      rewrite app_nil_r.
      set (Hrew := lookup_lnth (rt0 :: rts) rt0 0 rt0 Hlook).
      change (ty_lfts ty = ty_lfts (rew [type] Hrew in ty)).
      replace Hrew with (@eq_refl RT rt0) by apply proof_irrelevance. done.
    - simpl.
      destruct (decide (offset ∈ ({[(offset + S i)%nat]} : gset nat))) as [Hin | _].
      { apply elem_of_singleton in Hin. lia. }
      replace (offset + S i)%nat with (S offset + i)%nat by lia.
      apply IH.
  Qed.

  Lemma dep_wf_E_aux_singleton_project_def {rts rt} (Hinh : Inhabited (RT_xt rt))
      offset i (Hlook : rts !! i = Some rt) (tys : mut_types rts) :
    dep_wf_E_aux ({[(offset + i)%nat]} : gset nat) offset tys =
      ty_wf_E (rew [type] (lookup_lnth rts rt i rt Hlook) in
        @mut_component _ _ rts rt type_inhabitant tys i).
  Proof.
    revert offset i rt Hinh Hlook.
    induction tys as [|rt0 rts ty tys IH]; intros offset i rt Hinh Hlook; simpl in Hlook.
    { exfalso. rewrite lookup_nil in Hlook. done. }
    destruct i as [|i].
    - injection Hlook as <-. simpl.
      destruct (decide (offset ∈ ({[(offset + 0)%nat]} : gset nat))) as [_ | Hnot].
      2: { exfalso. apply Hnot. set_solver. }
      rewrite dep_wf_E_aux_singleton_before; last lia.
      rewrite app_nil_r.
      set (Hrew := lookup_lnth (rt0 :: rts) rt0 0 rt0 Hlook).
      change (ty_wf_E ty = ty_wf_E (rew [type] Hrew in ty)).
      replace Hrew with (@eq_refl RT rt0) by apply proof_irrelevance. done.
    - simpl.
      destruct (decide (offset ∈ ({[(offset + S i)%nat]} : gset nat))) as [Hin | _].
      { apply elem_of_singleton in Hin. lia. }
      replace (offset + S i)%nat with (S offset + i)%nat by lia.
      apply IH.
  Qed.

  Lemma dep_lfts_singleton_project {rts rt} `{!Inhabited (RT_xt rt)}
      i (Hlook : rts !! i = Some rt) (tys : mut_types rts) :
    dep_lfts ({[i]} : gset nat) tys = ty_lfts (mut_type_project tys i Hlook).
  Proof.
    rewrite mut_type_project_unfold /mut_type_project_def /dep_lfts.
    replace i with (0 + i)%nat at 1 by lia.
    apply dep_lfts_aux_singleton_project_def.
  Qed.

  Lemma dep_wf_E_singleton_project {rts rt} `{!Inhabited (RT_xt rt)}
      i (Hlook : rts !! i = Some rt) (tys : mut_types rts) :
    dep_wf_E ({[i]} : gset nat) tys = ty_wf_E (mut_type_project tys i Hlook).
  Proof.
    rewrite mut_type_project_unfold /mut_type_project_def /dep_wf_E.
    replace i with (0 + i)%nat at 1 by lia.
    apply dep_wf_E_aux_singleton_project_def.
  Qed.

  Lemma full_deps_from_elem i rts j :
    (i ≤ j < i + length rts)%nat → j ∈ full_deps_from i rts.
  Proof.
    revert i j. induction rts as [|rt rts IH]; intros i j Hrange; simpl in *.
    { lia. }
    destruct (decide (j = i)) as [-> | Hne].
    { set_solver. }
    assert (S i ≤ j < S i + length rts)%nat as Htail by lia.
    specialize (IH (S i) j Htail). set_solver.
  Qed.

  Lemma dep_lfts_aux_full {rts : list RT} deps i (tys : mut_types rts) :
    (∀ j, (i ≤ j < i + length rts)%nat → j ∈ deps) →
    dep_lfts_aux deps i tys = mut_lfts tys.
  Proof.
    revert i. induction tys as [|rt rts ty tys IH]; intros i Hdeps; simpl.
    { done. }
    destruct (decide (i ∈ deps)) as [_ | Hnot].
    - rewrite IH; first done. intros j Hrange. apply Hdeps. simpl. lia.
    - exfalso. apply Hnot. apply Hdeps. simpl. lia.
  Qed.

  Lemma dep_wf_E_aux_full {rts : list RT} deps i (tys : mut_types rts) :
    (∀ j, (i ≤ j < i + length rts)%nat → j ∈ deps) →
    dep_wf_E_aux deps i tys = mut_wf_E tys.
  Proof.
    revert i. induction tys as [|rt rts ty tys IH]; intros i Hdeps; simpl.
    { done. }
    destruct (decide (i ∈ deps)) as [_ | Hnot].
    - rewrite IH; first done. intros j Hrange. apply Hdeps. simpl. lia.
    - exfalso. apply Hnot. apply Hdeps. simpl. lia.
  Qed.

  Lemma dep_lfts_full {rts : list RT} deps (tys : mut_types rts) :
    DepsFull rts deps → dep_lfts deps tys = mut_lfts tys.
  Proof.
    intros ->. apply dep_lfts_aux_full.
    intros j Hrange. apply full_deps_from_elem. done.
  Qed.

  Lemma dep_wf_E_full {rts : list RT} deps (tys : mut_types rts) :
    DepsFull rts deps → dep_wf_E deps tys = mut_wf_E tys.
  Proof.
    intros ->. apply dep_wf_E_aux_full.
    intros j Hrange. apply full_deps_from_elem. done.
  Qed.

  Lemma dep_lfts_aux_union {rts : list RT} deps1 deps2 i (tys : mut_types rts) :
    ⊢ lft_equiv (lft_intersect_list (dep_lfts_aux (deps1 ∪ deps2) i tys))
        (lft_intersect_list (dep_lfts_aux deps1 i tys) ⊓
          lft_intersect_list (dep_lfts_aux deps2 i tys)).
  Proof.
    revert i. induction tys as [|rt rts ty tys IH]; intros i; simpl.
    { iApply lft_intersect_idempotent. }
    destruct (decide (i ∈ deps1)) as [Hin1 | Hnot1];
      destruct (decide (i ∈ deps2)) as [Hin2 | Hnot2];
      destruct (decide (i ∈ deps1 ∪ deps2)) as [Hin | Hnot]; try set_solver.
    - rewrite !lft_intersect_list_app. iApply lft_equiv_trans.
      { iApply lft_equiv_intersect; first iApply lft_equiv_refl. iApply IH. }
      iSplit.
      + iApply lft_incl_glb.
        * iApply lft_incl_glb.
          { iApply lft_intersect_incl_l. }
          iApply lft_incl_trans; first iApply lft_intersect_incl_r.
          iApply lft_intersect_incl_l.
        * iApply lft_incl_glb.
          { iApply lft_intersect_incl_l. }
          iApply lft_incl_trans; first iApply lft_intersect_incl_r.
          iApply lft_intersect_incl_r.
      + iApply lft_incl_glb.
        * iApply lft_incl_trans; first iApply lft_intersect_incl_l.
          iApply lft_intersect_incl_l.
        * iApply lft_incl_glb.
          { iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply lft_intersect_incl_r. }
          iApply lft_incl_trans; first iApply lft_intersect_incl_r.
          iApply lft_incl_trans; first iApply lft_intersect_incl_r.
          iApply lft_incl_refl.
    - rewrite !lft_intersect_list_app. iApply lft_equiv_trans.
      { iApply lft_equiv_intersect; first iApply lft_equiv_refl. iApply IH. }
      rewrite assoc.
      iApply lft_equiv_refl.
    - rewrite !lft_intersect_list_app. iApply lft_equiv_trans.
      { iApply lft_equiv_intersect; first iApply lft_equiv_refl. iApply IH. }
      rewrite assoc.
      rewrite [lft_intersect_list _ ⊓ lft_intersect_list _]comm.
      rewrite -assoc.
      iApply lft_equiv_refl.
  Qed.

  Lemma dep_lfts_union {rts : list RT} deps1 deps2 (tys : mut_types rts) :
    ⊢ lft_equiv (lft_intersect_list (dep_lfts (deps1 ∪ deps2) tys))
        (lft_intersect_list (dep_lfts deps1 tys) ⊓
          lft_intersect_list (dep_lfts deps2 tys)).
  Proof. iApply dep_lfts_aux_union. Qed.

  Lemma dep_wf_E_aux_union {rts : list RT} deps1 deps2 i (tys : mut_types rts) :
    elctx_interp (dep_wf_E_aux (deps1 ∪ deps2) i tys) ≡
      (elctx_interp (dep_wf_E_aux deps1 i tys) ∗
        elctx_interp (dep_wf_E_aux deps2 i tys))%I.
  Proof.
    revert i. induction tys as [|rt rts ty tys IH]; intros i; simpl.
    { rewrite elctx_interp_nil. iSplit; iIntros "_"; done. }
    destruct (decide (i ∈ deps1)) as [Hin1 | Hnot1];
      destruct (decide (i ∈ deps2)) as [Hin2 | Hnot2];
      destruct (decide (i ∈ deps1 ∪ deps2)) as [Hin | Hnot]; try set_solver.
    - rewrite !elctx_interp_app IH. iSplit.
      + iIntros "(#Hty & H1 & H2)". iFrame. iFrame "#".
      + iIntros "((#Hty & H1) & _ & H2)". iFrame. iFrame "#".
    - rewrite !elctx_interp_app IH. rewrite assoc. done.
    - rewrite !elctx_interp_app IH. iSplit.
      + iIntros "(Hty & H1 & H2)". iFrame.
      + iIntros "(H1 & Hty & H2)". iFrame.
  Qed.

  Lemma dep_wf_E_union {rts : list RT} deps1 deps2 (tys : mut_types rts) :
    elctx_interp (dep_wf_E (deps1 ∪ deps2) tys) ≡
      (elctx_interp (dep_wf_E deps1 tys) ∗
        elctx_interp (dep_wf_E deps2 tys))%I.
  Proof. apply dep_wf_E_aux_union. Qed.

  Definition dep_beta_interp {rts : list RT}
      (βdeps : list (lft * gset nat)) (tys : mut_types rts) : iProp Σ :=
    ([∗ list] βdep ∈ βdeps,
      βdep.1 ⊑ lft_intersect_list (dep_lfts βdep.2 tys))%I.

  Definition DepBetaFull {rts : list RT}
      (βdeps : list (lft * gset nat)) : Type :=
    { βs : list lft &
      ∀ tys : mut_types rts,
        dep_beta_interp βdeps tys ≡
          ([∗ list] β ∈ βs, β ⊑ lft_intersect_list (mut_lfts tys))%I }.

  Lemma dep_lfts_aux_empty {rts : list RT} i (tys : mut_types rts) :
    dep_lfts_aux ∅ i tys = [].
  Proof.
    revert i. induction tys as [|rt rts ty tys IH]; intros i; simpl; first done.
    destruct (decide (i ∈ ∅)) as [Hin | _]; first set_solver.
    apply IH.
  Qed.

  Lemma dep_lfts_empty {rts : list RT} (tys : mut_types rts) :
    dep_lfts ∅ tys = [].
  Proof. apply dep_lfts_aux_empty. Qed.

  Lemma dep_wf_E_aux_empty {rts : list RT} i (tys : mut_types rts) :
    dep_wf_E_aux ∅ i tys = [].
  Proof.
    revert i. induction tys as [|rt rts ty tys IH]; intros i; simpl; first done.
    destruct (decide (i ∈ ∅)) as [Hin | _]; first set_solver.
    apply IH.
  Qed.

  Lemma dep_wf_E_empty {rts : list RT} (tys : mut_types rts) :
    dep_wf_E ∅ tys = [].
  Proof. apply dep_wf_E_aux_empty. Qed.

  Lemma DepBetaFull_nil {rts : list RT} : DepBetaFull (rts:=rts) [].
  Proof.
    exists []. intros tys. rewrite /dep_beta_interp /=. done.
  Qed.

  Record DepLftMorphism {rts B} `{!Lifecycle B}
      (deps : gset nat) (F : mut_types rts → B) : Type := mk_dep_lft_morph {
    dep_lft_morph_α : lft;
    dep_lft_morph_E : elctx;
    dep_lft_morph_βdeps : list (lft * gset nat);
    dep_lft_morph_lfts :
      ⊢ ∀ tys, lft_equiv (lft_intersect_list (lifecycle_lfts (F tys)))
          (dep_lft_morph_α ⊓ lft_intersect_list (dep_lfts deps tys));
    dep_lft_morph_wf_E :
      ∀ tys, elctx_interp (lifecycle_wf_E (F tys)) ≡
          (elctx_interp dep_lft_morph_E ∗ elctx_interp (dep_wf_E deps tys) ∗
            dep_beta_interp dep_lft_morph_βdeps tys)%I;
  }.

  Existing Class DepLftMorphism.

  Class DepLftMorphismBetaFull {rts B} `{!Lifecycle B} {deps : gset nat}
      {F : mut_types rts → B} (Hm : DepLftMorphism deps F) : Type :=
    dep_lft_morphism_beta_full : DepBetaFull (rts:=rts) (@dep_lft_morph_βdeps rts B _ deps F Hm).

  Global Arguments mk_dep_lft_morph {_ _ _ _ _}.
  Global Arguments dep_lft_morph_α {_ _ _ _ _} _.
  Global Arguments dep_lft_morph_E {_ _ _ _ _} _.
  Global Arguments dep_lft_morph_βdeps {_ _ _ _ _} _.
  Global Arguments dep_lft_morph_lfts {_ _ _ _ _} _.
  Global Arguments dep_lft_morph_wf_E {_ _ _ _ _} _.

  Program Definition mk_dep_lft_morph_const {rts B} `{!Lifecycle B}
      (F : mut_types rts → B) (α : lft) (E : elctx)
      (Hlfts : ⊢ ∀ tys, lft_equiv (lft_intersect_list (lifecycle_lfts (F tys))) α)
      (Hwf_E : ∀ tys, elctx_interp (lifecycle_wf_E (F tys)) ≡ elctx_interp E) :
      DepLftMorphism ∅ F :=
    mk_dep_lft_morph α E [] _ _.
  Next Obligation.
    iIntros (rts B ? F α E Hlfts Hwf_E tys).
    iApply lft_equiv_trans; first iApply (Hlfts $! tys).
    rewrite dep_lfts_empty /= lft_intersect_right_id.
    iApply lft_equiv_refl.
  Qed.
  Next Obligation.
    intros rts B ? F α E Hlfts Hwf_E tys.
    rewrite (Hwf_E tys) dep_wf_E_empty /dep_beta_interp /= elctx_interp_nil.
    iSplit.
    - iIntros "HE". iFrame. done.
    - iIntros "(HE & _ & _)". iFrame.
  Qed.

  Definition dep_lft_morph_const {rts B} `{!Lifecycle B} {deps : gset nat}
      {F : mut_types rts → B} (Hdeps : deps = ∅)
      (Hm : DepLftMorphism ∅ F) : DepLftMorphism deps F.
  Proof. subst deps. exact Hm. Defined.

  Global Program Instance dep_lft_morph_ignore {rts B} `{!Lifecycle B} (x : B) :
    DepLftMorphism ∅ (λ _ : mut_types rts, x) :=
      dep_lft_morph_const _ (mk_dep_lft_morph_const _ (lft_intersect_list $ lifecycle_lfts x) (lifecycle_wf_E x) _ _).
  Next Obligation.
    done.
  Defined.
  Next Obligation.
    iIntros (?????). iApply lft_equiv_refl.
  Qed.
  Next Obligation.
    done.
  Qed.

  Lemma dep_lft_morph_outlives_E {rts rt} deps (F : mut_types rts → type rt) κ α tys :
    (⊢ ∀ tys, lft_equiv (lft_intersect_list (lifecycle_lfts (F tys)))
        (α ⊓ lft_intersect_list (dep_lfts deps tys))) →
    elctx_interp (ty_outlives_E (F tys) κ) ≡
      (κ ⊑ α ∗ κ ⊑ lft_intersect_list (dep_lfts deps tys))%I.
  Proof.
    intros Hlfts.
    rewrite /ty_outlives_E. change (ty_lfts (F tys)) with (lifecycle_lfts (F tys)).
    rewrite lfts_outlives_E_interp.
    iPoseProof (Hlfts $! tys) as "Hlfts".
    iSplit.
    - iIntros "#Ha". iSplit.
      + iApply (lft_incl_trans with "Ha").
        iApply lft_incl_trans; last iApply lft_intersect_incl_l.
        iApply lft_equiv_incl_l. iApply "Hlfts".
      + iApply (lft_incl_trans with "Ha").
        iApply lft_incl_trans; last iApply lft_intersect_incl_r.
        iApply lft_equiv_incl_l. iApply "Hlfts".
    - iIntros "#[Hα Hdeps]".
      iApply (lft_incl_trans _ (α ⊓ lft_intersect_list (dep_lfts deps tys))).
      { iApply lft_incl_glb; done. }
      iApply lft_equiv_incl_r. iApply "Hlfts".
  Qed.

  Program Definition dep_lft_morph_make_id {rts A B} `{!Lifecycle A} `{!Lifecycle B} deps
      (F : mut_types rts → A) (G : mut_types rts → B)
      (Hm : DepLftMorphism deps F)
      (Hlfts : ∀ tys, lifecycle_lfts (G tys) = lifecycle_lfts (F tys))
      (HwfE : ∀ tys, lifecycle_wf_E (G tys) = lifecycle_wf_E (F tys)) :
      DepLftMorphism deps G :=
    mk_dep_lft_morph
      (dep_lft_morph_α Hm)
      (dep_lft_morph_E Hm)
      (dep_lft_morph_βdeps Hm)
      _ _.
  Next Obligation.
    iIntros (rts A B ?? deps F G Hm Hlfts HwfE tys).
    rewrite Hlfts. iApply (dep_lft_morph_lfts Hm).
  Qed.
  Next Obligation.
    intros rts A B ?? deps F G Hm Hlfts HwfE tys.
    rewrite HwfE. apply (dep_lft_morph_wf_E Hm).
  Qed.

  Program Definition dep_lft_morph_make_ref {rts rt1 rt2} deps
      (F : mut_types rts → type rt1) (G : mut_types rts → type rt2) κ
      (Hm : DepLftMorphism deps F)
      (Hlfts : ∀ tys, ty_lfts (G tys) = κ :: ty_lfts (F tys))
      (HwfE : ∀ tys, ty_wf_E (G tys) = ty_wf_E (F tys) ++ ty_outlives_E (F tys) κ) :
      DepLftMorphism deps G :=
    mk_dep_lft_morph
      (κ ⊓ dep_lft_morph_α Hm)
      (dep_lft_morph_E Hm ++ [(κ, dep_lft_morph_α Hm)])
      (dep_lft_morph_βdeps Hm ++ [(κ, deps)])
      _ _.
  Next Obligation.
    iIntros (rts rt1 rt2 deps F G κ Hm Hlfts HwfE tys).
    change (lifecycle_lfts (G tys)) with (ty_lfts (G tys)).
    rewrite Hlfts /=. iApply lft_equiv_trans.
    { iApply lft_equiv_intersect; first iApply lft_equiv_refl.
      iApply (dep_lft_morph_lfts Hm). }
    rewrite assoc. iApply lft_equiv_refl.
  Qed.
  Next Obligation.
    intros rts rt1 rt2 deps F G κ Hm Hlfts HwfE tys.
    change (lifecycle_wf_E (G tys)) with (ty_wf_E (G tys)).
    rewrite HwfE elctx_interp_app (dep_lft_morph_wf_E Hm tys).
    rewrite /dep_beta_interp big_sepL_app /=.
    rewrite elctx_interp_app.
    rewrite (dep_lft_morph_outlives_E deps F κ (dep_lft_morph_α Hm) tys (dep_lft_morph_lfts Hm)).
    iSplit.
    - iIntros "((HE & Hdep & Hβ) & Hκa & Hκdep)". iFrame. done.
    - iIntros "((HE & Hκa) & Hdep & Hβ & Hκdep)".
      iEval (rewrite /elctx_interp/elctx_elt_interp /=) in "Hκa".
      iDestruct "Hκa" as "[Hκa _]". iDestruct "Hκdep" as "[Hκdep _]". iFrame.
  Qed.

  Lemma DepLftMorphism_to_LftMorphism {rts B} `{!Lifecycle B}
      (deps : gset nat) (F : mut_types rts → B) :
    ∀ Hm : DepLftMorphism deps F,
    DepsFull rts deps →
    DepLftMorphismBetaFull Hm →
    LftMorphism F.
  Proof.
    intros HA Hfull Hβfull.
    apply lft_morph_add.
    destruct Hβfull as [βs Hβs].
    refine (mk_lft_morph_add (dep_lft_morph_α HA) (dep_lft_morph_E HA)
      βs _ _).
    - iIntros (tys). iApply lft_equiv_trans.
      { iApply (dep_lft_morph_lfts HA). }
      iApply lft_equiv_intersect; first iApply lft_equiv_refl.
      rewrite (dep_lfts_full deps tys Hfull). iApply lft_equiv_refl.
    - intros tys. rewrite (dep_lft_morph_wf_E HA tys).
      rewrite (dep_wf_E_full deps tys Hfull) (Hβs tys). done.
  Qed.

  Global Program Instance DepLftMorphism_hcons {rts rt rts'} depsG depsGs
      (G : mut_types rts → type rt) (Gs : mut_types rts → mut_types rts') :
    DepLftMorphism depsG G →
    DepLftMorphism depsGs Gs →
    DepLftMorphism (depsG ∪ depsGs) (λ x, G x +:: Gs x) :=
    λ HG HGs,
      mk_dep_lft_morph
        (dep_lft_morph_α HG ⊓ dep_lft_morph_α HGs)
        (dep_lft_morph_E HG ++ dep_lft_morph_E HGs)
        (dep_lft_morph_βdeps HG ++ dep_lft_morph_βdeps HGs) _ _.
  Next Obligation.
    iIntros (rts rt rts' depsG depsGs G Gs HG HGs x).
    rewrite /mut_lfts /= lft_intersect_list_app.
    iApply lft_equiv_trans.
    { iApply lft_equiv_intersect; [iApply (dep_lft_morph_lfts HG) | iApply (dep_lft_morph_lfts HGs)]. }
    iSplit.
    - iApply lft_incl_glb.
      { iApply lft_incl_glb.
        + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply lft_intersect_incl_l.
        + iApply lft_incl_trans; first iApply lft_intersect_incl_r. iApply lft_intersect_incl_l. }
      iApply lft_incl_trans.
      { iApply lft_incl_glb.
        + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply lft_intersect_incl_r.
        + iApply lft_incl_trans; first iApply lft_intersect_incl_r. iApply lft_intersect_incl_r. }
      iApply lft_equiv_incl_r. iApply dep_lfts_union.
    - iApply lft_incl_glb.
      { iApply lft_incl_glb.
        + iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply lft_intersect_incl_l.
        + iApply lft_incl_trans; first iApply lft_intersect_incl_r.
          iApply lft_incl_trans.
          { iApply lft_equiv_incl_l. iApply dep_lfts_union. }
          iApply lft_intersect_incl_l. }
      iApply lft_incl_glb.
      { iApply lft_incl_trans; first iApply lft_intersect_incl_l. iApply lft_intersect_incl_r. }
      iApply lft_incl_trans; first iApply lft_intersect_incl_r.
      iApply lft_incl_trans.
      { iApply lft_equiv_incl_l. iApply dep_lfts_union. }
      iApply lft_intersect_incl_r.
  Qed.
  Next Obligation.
    intros rts rt rts' depsG depsGs G Gs HG HGs x.
    change (elctx_interp (ty_wf_E (G x) ++ mut_wf_E (Gs x)) ≡
      (elctx_interp (dep_lft_morph_E HG ++ dep_lft_morph_E HGs) ∗
      elctx_interp (dep_wf_E (depsG ∪ depsGs) x) ∗
      dep_beta_interp (dep_lft_morph_βdeps HG ++ dep_lft_morph_βdeps HGs) x)%I).
    rewrite !elctx_interp_app.
    rewrite (dep_lft_morph_wf_E HG x) (dep_lft_morph_wf_E HGs x).
    rewrite /dep_beta_interp big_sepL_app dep_wf_E_union.
    rewrite -!assoc.
    iSplit.
    - iIntros "(HE & HW & Hβ & HEs & HWs & Hβs)". iFrame.
    - iIntros "(HE & HEs & HW & HWs & Hβ & Hβs)". iFrame.
  Qed.

  Program Definition DepLftMorphism_nil {rts}
      (F : mut_types rts → mut_types []) :
    DepLftMorphism ∅ F :=
    @dep_lft_morph_const _ _ _ _ _ eq_refl (mk_dep_lft_morph_const F static [] _ _).
  Next Obligation.
    iIntros (rts F x). remember (F x) as Fx. dependent destruction Fx.
    iApply lft_equiv_refl.
  Qed.
  Next Obligation.
    intros rts F x. remember (F x) as Fx. dependent destruction Fx.
    rewrite elctx_interp_nil. done.
  Qed.

  (** Lifting to [hlist] *)
  Class DepHTypeLftMorphism {rts rts'}
      (deps : gset nat) (F : mut_types rts → mut_types rts') : Type := {
    dep_htype_lft_morphism_lft : DepLftMorphism deps F;
  }.

  Global Instance DepHTypeLftMorphism_cons {rts rt rts'} depsG depsGs
      (G : mut_types rts → type rt) (Gs : mut_types rts → mut_types rts') :
    DepLftMorphism depsG G →
    DepHTypeLftMorphism depsGs Gs →
    DepHTypeLftMorphism (depsG ∪ depsGs) (λ x, G x +:: Gs x).
  Proof.
    intros HG [HGs]. constructor. eapply DepLftMorphism_hcons; assumption.
  Defined.

  Lemma DepHTypeLftMorphism_to_HTypeLftMorphism {rts rts'}
      (deps : gset nat) (F : mut_types rts → mut_types rts') :
    ∀ Hm : DepHTypeLftMorphism deps F,
    DepsFull rts deps →
    DepLftMorphismBetaFull (dep_htype_lft_morphism_lft (DepHTypeLftMorphism:=Hm)) →
    HTypeLftMorphism F.
  Proof.
    intros [Hm] Hfull Hβfull. constructor.
    eapply DepLftMorphism_to_LftMorphism; done.
  Qed.

  Global Instance DepHTypeLftMorphism_nil {rts}
    (F : mut_types rts → mut_types []) : DepHTypeLftMorphism ∅ F.
  Proof. constructor. apply DepLftMorphism_nil. Defined.
End dep_lft_mor.

Global Hint Mode DepsFull + + : typeclass_instances.
Global Hint Extern 3 (DepsFull _ _) => unfold DepsFull; simpl; set_solver : typeclass_instances.

Global Hint Mode DepLftMorphismBetaFull + + + + + + + + : typeclass_instances.
(* TODO generalize *)
Ltac solve_dep_beta_full :=
  simpl;
  apply DepBetaFull_nil.
Global Hint Extern 3 (DepLftMorphismBetaFull _) =>
  unfold DepLftMorphismBetaFull;
  simpl;
  solve_dep_beta_full : typeclass_instances.

(* needs [eapply], so declaring it an instance does not suffice *)
Global Hint Extern 3 (LftMorphism _) => simple eapply DepLftMorphism_to_LftMorphism : typeclass_instances.

Section projection.
  Context `{!typeGS Σ}.
  Import EqNotations.

  Lemma mut_type_project_cons_head_eq {rt rts} `{!Inhabited (RT_xt rt)}
      (tys : mut_types (rt :: rts)) :
    mut_type_project tys 0 eq_refl = hlist_head tys.
  Proof.
    rewrite (@mut_type_project_unfold).
    dependent destruction tys. simpl.
    set (Hrew := lookup_lnth (rt :: rts) rt 0 rt eq_refl).
    change (rew [type] Hrew in t = t).
    replace Hrew with (@eq_refl RT rt) by apply proof_irrelevance. done.
  Qed.

  Lemma mut_type_project_cons_tail_eq {rt0 rt rts} `{!Inhabited (RT_xt rt)}
      (tys : mut_types (rt0 :: rts)) i
      (Hlook : rts !! i = Some rt) (Hlook' : (rt0 :: rts) !! S i = Some rt) :
    mut_type_project (hlist_tail tys) i Hlook =
      mut_type_project tys (S i) Hlook'.
  Proof.
    rewrite !(@mut_type_project_unfold).
    dependent destruction tys. simpl.
    unfold mut_type_project_def, mut_component. simpl.
    replace Hlook' with Hlook by apply proof_irrelevance.
    done.
  Qed.

  (** Projection is a lifetime morphism with a single dependency *)
  Global Instance mut_type_project_dep_lft_morphism {rts rt}
      `{!Inhabited (RT_xt rt)} i (Hlook : rts !! i = Some rt) :
    DepLftMorphism ({[i]} : gset nat) (λ tys : mut_types rts, mut_type_project tys i Hlook).
  Proof.
    refine (mk_dep_lft_morph static [] [] _ _).
    - abstract (iIntros (tys); rewrite dep_lfts_singleton_project left_id;
      iApply lft_equiv_refl).
    - abstract (intros tys; rewrite dep_wf_E_singleton_project elctx_interp_nil;
      iSplit; iIntros "H";
      [iFrame; rewrite /dep_beta_interp /=; done
      | iDestruct "H" as "(_ & H & _)"; done]).
  Defined.

  Global Instance mut_type_project_cons_head_lft_morphism {rts1 rt rt' rts}
      `{!Inhabited (RT_xt rt')}
      (G : mut_types rts1 → type rt) (Gs : mut_types rts1 → mut_types rts)
      (Hlook : (rt :: rts) !! 0%nat = Some rt') deps :
    DepLftMorphism deps G →
    DepLftMorphism deps (λ x, mut_type_project (G x +:: Gs x) 0 Hlook).
  Proof.
    intros HG.
    eapply (dep_lft_morph_make_id deps G
      (λ x, mut_type_project (G x +:: Gs x) 0 Hlook) HG).
    - abstract (intros x; injection Hlook as <-;
      replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance;
      rewrite mut_type_project_cons_head_eq; done).
    - abstract (intros x; injection Hlook as <-;
      replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance;
      rewrite mut_type_project_cons_head_eq; done).
  Defined.

  Global Instance mut_type_project_cons_tail_lft_morphism {rts1 rt rt' rts}
      `{!Inhabited (RT_xt rt')}
      (Gs : mut_types rts1 → mut_types (rt :: rts))
      i (Hlook : (rt :: rts) !! S i = Some rt') deps
      :
    DepLftMorphism deps (λ x, mut_type_project (hlist_tail $ Gs x) i Hlook) →
    DepLftMorphism deps (λ x, mut_type_project (Gs x) (S i) Hlook).
  Proof.
    intros HGs.
    eapply (dep_lft_morph_make_id deps
      (λ x, mut_type_project (hlist_tail $ Gs x) i Hlook)
      (λ x, mut_type_project (Gs x) (S i) Hlook) HGs).
    - abstract (intros x; rewrite -(mut_type_project_cons_tail_eq (Gs x) i Hlook Hlook); done).
    - abstract (intros x; rewrite -(mut_type_project_cons_tail_eq (Gs x) i Hlook Hlook); done).
  Defined.
End projection.
