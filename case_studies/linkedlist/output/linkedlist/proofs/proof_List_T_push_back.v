From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_push_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma head_app_l {A} (l1 l2 : list A) :
  length l1 > 0 →
  head (l1 ++ l2) = head l1.
Proof.
  rewrite head_app.
  destruct l1 as [ | x l1]; simpl; first lia.
  done.
Qed.
Hint Rewrite -> @head_app_l using lia : lithium_rewrite.
Hint Rewrite -> @last_lookup : lithium_rewrite.
Hint Rewrite Nat.sub_1_r : lithium_rewrite.

Lemma simplify_goal_big_sepL_app {A} (xs1 xs2 : list A) (Φ : nat → A → iProp Σ) T:
  ([∗ list] i↦x ∈ xs1, Φ i x) ∗ ([∗ list] i↦x ∈ xs2, Φ (length xs1 + i)%nat x) ∗ T
  ⊢ simplify_goal ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  rewrite /simplify_goal.
  rewrite big_sepL_app.
  iIntros "($ & $ & $)".
Qed.
Definition simplify_goal_big_sepL_app_inst := [instance @simplify_goal_big_sepL_app with 10%N].
Global Existing Instance simplify_goal_big_sepL_app_inst.

Lemma List_T_push_back_proof (π : thread_id) :
  List_T_push_back_lemma π.
Proof.
  List_T_push_back_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep. liShow.
    (* The empty case establishes the singleton list invariant. *)
    move: Hlocs.
    rep liRStep.
    liInst Hevar_rf ([$# value]).
    liInst Hevar_locs ([x']).
    liShow. rep liRStep. }
  rep <-! liRStep. liShow.
  revert Hlocs.
  rep <-! liRStep.

  (* Isolate the old tail so its next pointer can be updated. *)
  iRename select ([∗ list] i ↦ _ ∈ _, _)%I into "Hold".
  odestruct (lookup_lt_is_Some_2 self (length self - 1) _) as (last_elem & Hlook).
  { lia. }
  iPoseProof (big_sepL_delete _ _ (length self - 1) with "Hold") as "(Hlast & Hcl)".
  { rewrite list_lookup_fmap. rewrite Hlook//. }
  rename select (_ !! _ = Some tl_ptr) into Hlook_last.
  rewrite Hlen_eq in Hlook_last.
  iRevert "Hlast".

  rep <-! liRStep. liShow.
  apply_update (updateable_strip_guards).
  rep <-! liRStep; liShow.

  iAcquireCredits as "Hcred1".
  iAcquireCredits as "Hcred2".
  rep liRStep; liShow.

  liInst Hevar_rf (($# self) ++ [$# value]).
  liInst Hevar_locs (locs ++ [x']).

  rep liRStep; liShow.

  (* Rebuild the invariant with the updated tail and appended node. *)
  iApply (prove_with_subtype_stratify l0).
  rep liRStep. liShow.
  iApply prove_with_subtype_default.
  iRename select ((x' ◁ₗ[_, _] _ @ _))%I into "Hnew".
  iRename select (freeable_nz l0 _ _ _) into "Hfree_old".
  iRename select (freeable_nz x' _ _ _) into "Hfree".
  iSplitL "Hcl Hfree_old Hcred1".
  { iIntros "Hold". rep liRStep. liShow.
    iApply (big_sepL_delete  _ _ (length self - 1)).
    { rewrite list_lookup_fmap. rewrite Hlook//. }
    liShow. rep liRStep; liShow.
    iApply (big_sepL_impl with "Hcl").
    iModIntro. iIntros (k xk Hxk) "Hnode".
    destruct (decide (k = (length self - 1)%nat)); first done.
    iDestruct "Hnode" as (l1 lnext0 lprev0)
      "(%Hloc_lookup & %Hnext_lookup & %Hprev_lookup & Hguard & Hfree_node)".
    have Hindex_bound : (k < length locs)%nat.
    { by apply (lookup_lt_Some locs k l1). }
    have Hnext_bound : (S k < length locs)%nat.
    { have Hxk_bound := lookup_lt_Some _ _ _ Hxk.
      rewrite length_fmap in Hxk_bound.
      rewrite Hlen_eq. lia. }
    have Hnext_lookup_locs : locs !! S k = Some lnext0.
    { rewrite lookup_app_l in Hnext_lookup; last exact Hnext_bound.
      exact Hnext_lookup. }
    iExists l1, lnext0, lprev0.
    iSplit; first (iPureIntro; by apply lookup_app_l_Some).
    iSplit; first (iPureIntro; do 2 apply lookup_app_l_Some; exact Hnext_lookup_locs).
    iSplit.
    { iPureIntro. change (((NULL_loc :: locs) ++ [x']) !! k = Some lprev0).
      by apply lookup_app_l_Some. }
    iFrame. }
  rep liRStep.
  rewrite Hlen_eq. rewrite Nat.sub_diag/=.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - apply Forall_app; solve_goal.
  - rewrite Hlen_eq Nat.sub_diag//.
  - replace (S (length self) - length self)%nat with 1%nat by lia.
    rename select ((NULL_loc :: locs) !! Nat.pred (length self) = Some lprev)
      into Htail_prev_lookup.
    change (((NULL_loc :: locs) ++ [x']) !! Nat.pred (length self) = Some lprev).
    apply lookup_app_l_Some. exact Htail_prev_lookup.

  Unshelve.
  - replace (S (length self) - length self)%nat with 1%nat by lia. done.
  - have Hlocs_nonempty : (0 < length locs)%nat by lia.
    rewrite <- Hlen_eq.
    rewrite <- (Nat.succ_pred_pos _ Hlocs_nonempty). simpl.
    rewrite lookup_total_app_l; last lia.
    apply symmetry, list_lookup_total_correct.
    rewrite Hlen_eq. exact Hlook_last.

  all: print_remaining_sidecond.
Qed.
End proof.
