From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_mark_from.
From hinata_mikami.extra_proofs.gc Require Import heap_lemmas.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Heap_mark_from_proof (π : thread_id) :
  Heap_mark_from_lemma π.
Proof.
  Heap_mark_from_prelude.

  rep <-! liRStep; liShow.

  iRename select
    ([∗ list] k ↦ x ∈ (id <$> h),
      ∃ (l0 n : loc) (m : bool), _)%I
    into "Hnodes".

  assert (Hmap_vals : (id <$> h) = h).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  assert (Hmap_locs : (id <$> h0) = h0).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  assert (Hmap_nexts : (id <$> h1) = h1).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  assert (Hmap_marks : (id <$> h2) = h2).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  iEval (
    rewrite Hmap_vals
            Hmap_locs
            Hmap_nexts
            Hmap_marks
  ) in "Hnodes".

  assert (Hi_vals : (i < length h)%nat) by lia.

  destruct (lookup_lt_is_Some_2 h i Hi_vals)
    as [vi Hvi].

  iDestruct
    (big_sepL_lookup_acc_impl i vi Hvi with "Hnodes")
    as "(HiNode & Hclose)".

  iDestruct "HiNode" as
    (node_l nexti marki)
    "(%Hloc_i & %Hnext_i & %Hmark_i &
      Hguard & Hfree)".

  assert (node_l = l) as -> by congruence.

  apply_update updateable_strip_guards.

  rep <-! liRStep; liShow.

  {
    iRename select
      (l ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".
    
    iAcquireCredits as "Hcred".

    iRevert "Hnode Hfree Hclose".

    rep <-! liRStep; liShow.

    rep liRStep; liShow.

    liInst Hevar_x1 h.
    liInst Hevar_x0 h1.
    liInst Hevar_x3 h2.

    rep liRStep; liShow.

    iRename select
      (l ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".

    iRename select
      (freeable_nz l _ 1 HeapAlloc)%I
      into "Hfree".

    iRename select
      (∀ Ψ : nat → Z → iPropI Σ, _)%I
      into "Hclose".

    set (P := fun (k : nat) (y : Z) =>
      (∃ (l0 n : loc) (m : bool),
        ⌜h0 !! k = Some l0⌝ ∗
        ⌜h1 !! k = Some n⌝ ∗
        ⌜h2 !! k = Some m⌝ ∗
        guarded true
          (l0 ◁ₗ[π, Owned]
            # -[# y; # n; # m]
            @ (◁ (Node_ty <INST!>))) ∗
        freeable_nz l0
          (ly_size (use_layout_alg' Node_sls))
          1 HeapAlloc)%I).

    iSpecialize ("Hclose" $! P).

    iSpecialize ("Hclose" with "[]").
    {
      iModIntro.
      iIntros (k y) "%Hlookup %Hneq HP".
      unfold P.
      iExact "HP".
    }

    iRevert "Hnode Hfree Hclose".
    iIntros "Hnode Hfree Hclose".
    rep liRStep; liShow.

    iApply
    (prove_with_subtype_big_sepL_acc
      _ _ _ _ h P i vi _
      with "Hclose").
    
    unfold P.

    rep liRStep; liShow.

  }
  {
    iRename select
      (l ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".

    liShow.
    iAcquireCredits as "Hcred".
    liShow.

    rep <-! liRStep; liShow.

    - rep liRStep; liShow.
      liInst Hevar_x1 h.
      liInst Hevar_x0 h1.
      liInst Hevar_x3 (<[i := true]> h2).

      rep liRStep; liShow.

      set (Pnew := fun (k : nat) (y : Z) =>
        (∃ (l0 n : loc) (m : bool),
          ⌜h0 !! k = Some l0⌝ ∗
          ⌜h1 !! k = Some n⌝ ∗
          ⌜(<[i := true]> h2) !! k = Some m⌝ ∗
          guarded true
            (l0 ◁ₗ[π, Owned]
              # -[# y; # n; # m]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l0
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc)%I).

      iSpecialize ("Hclose" $! Pnew).
      iSpecialize ("Hclose" with "[]").
      {
        iModIntro.
        iIntros (k y) "%Hlookup %Hneq Hold".

        iDestruct "Hold" as
          (l0 n m)
          "(%Hloc_k & %Hnext_k & %Hmark_k &
            Hguard_k & Hfree_k)".

        unfold Pnew.

        iExists l0, n, m.

        iSplit.
        { iPureIntro. exact Hloc_k. }

        iSplit.
        { iPureIntro. exact Hnext_k. }

        iSplit.
        {
          iPureIntro.
          rewrite list_lookup_insert_ne.
          - exact Hmark_k.
          - congruence.
        }

        iFrame.
      }

      {
        iApply
        (prove_with_subtype_big_sepL_acc
          _ _ _ _ h Pnew i vi _
          with "Hclose").

        unfold Pnew.
        rep liRStep; liShow.
      }

      - assert (Hnext_valid_i :
          nexti = NULL_loc ∨ nexti ∈ h0).
        {
          exact
            ((proj1
               (Forall_lookup
                 (fun n : loc =>
                   n = NULL_loc ∨ n ∈ h0)
                 h1)
               Hnext_valid)
              i nexti Hnext_i).
        }

        assert (Hnext_nonnull : nexti <> NULL_loc).
        {
          intro Heq.
          subst nexti.
          apply H17.
          unfold NULL_loc.
          reflexivity.
        }

        assert (Hnext_mem : nexti ∈ h0).
        {
          destruct Hnext_valid_i as [Hnull | Hmem].
          - exfalso.
            apply Hnext_nonnull.
            exact Hnull.
          - exact Hmem.
        }

        destruct
          (list_elem_of_lookup_1 h0 nexti Hnext_mem)
          as [j Hj].
      
        rep liRStep; liShow.
        liInst Hevar_x1 h.
        liInst Hevar_x0 h1.
        liInst Hevar_x3 (<[i := true]> h2).

        rep liRStep; liShow.

        set (Pnew := fun (k : nat) (y : Z) =>
        (∃ (l0 n : loc) (m : bool),
          ⌜h0 !! k = Some l0⌝ ∗
          ⌜h1 !! k = Some n⌝ ∗
          ⌜(<[i := true]> h2) !! k = Some m⌝ ∗
          guarded true
            (l0 ◁ₗ[π, Owned]
              # -[# y; # n; # m]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l0
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc)%I).

        iSpecialize ("Hclose" $! Pnew).
        iSpecialize ("Hclose" with "[]").
        {
          iModIntro.
          iIntros (k y) "%Hlookup %Hneq Hold".

          iDestruct "Hold" as
            (l0 n m)
            "(%Hloc_k & %Hnext_k & %Hmark_k &
              Hguard_k & Hfree_k)".

          unfold Pnew.
          iExists l0, n, m.

          iSplit.
          { iPureIntro. exact Hloc_k. }

          iSplit.
          { iPureIntro. exact Hnext_k. }

          iSplit.
          {
            iPureIntro.
            rewrite list_lookup_insert_ne.
            - exact Hmark_k.
            - congruence.
          }

          iFrame.
        }
        {
          iRename select
            (l ◁ₗ[_, Owned] _ @ _)%I
            into "Hnode_new".

          liShow.

          iAssert (
            guarded true
              (l ◁ₗ[π, Owned]
                # -[# vi; # nexti; # true]
                @ (◁ (Node_ty <INST!>)))
          )%I with "[Hcred Hnode_new]" as "Hguard_new".
          {
            iApply guarded_intro.
            iFrame.
          }

          assert (Hmark_new_i :
            (<[i := true]> h2) !! i = Some true).
          {
            rewrite list_lookup_insert_eq.
            - done.
            - exact H14.
          }

          iAssert (Pnew i vi)%I
            with "[Hguard_new Hfree]" as "HiNew".
          {
            unfold Pnew.

            iExists l, nexti, true.

            iSplit.
            { iPureIntro. exact Hloc_i. }

            iSplit.
            { iPureIntro. exact Hnext_i. }

            iSplit.
            { iPureIntro. exact Hmark_new_i. }

            iFrame.
          }

          iPoseProof ("Hclose" with "HiNew") as "Hnodes_new".

          iApply prove_with_subtype_default.

          iSplitL "Hnodes_new".
          {
            iExact "Hnodes_new".
          }

          rep liRStep; liShow.

          liInst Hevar_x5 j.

          rep liRStep; liShow.
        }
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  Unshelve.
  all: eauto using
  mark_from_rel_marked,
  mark_from_rel_null,
  mark_from_rel_next.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
