From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma simplify_goal_big_sepL_app {A}
    (xs1 xs2 : list A)
    (Φ : nat → A → iProp Σ) T :
  ([∗ list] i ↦ x ∈ xs1, Φ i x) ∗
  ([∗ list] i ↦ x ∈ xs2,
      Φ (length xs1 + i)%nat x) ∗ T
  ⊢
  simplify_goal
    ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  rewrite /simplify_goal.
  rewrite big_sepL_app.
  iIntros "($ & $ & $)".
Qed.

Definition simplify_goal_big_sepL_app_inst :=
  [instance @simplify_goal_big_sepL_app with 10%N].

Global Existing Instance simplify_goal_big_sepL_app_inst.


Lemma Heap_alloc_proof (π : thread_id) :
  Heap_alloc_lemma π.
Proof.
  Heap_alloc_prelude.

  rep <-! liRStep; liShow.

  rep liRStep; liShow.

  liInst Hevar_x
    (match h with
    | [] => v
    | x :: _ => x
    end).

  liInst Hevar_x2
    (match h with
    | [] => []
    | _ :: xs => xs ++ [v]
    end).

  liInst Hevar_x0
    (h1 ++ [NULL_loc]).

  liInst Hevar_x3
    (h2 ++ [false]).

  liShow.


  destruct h as [| old_v vals_tail].
  (* Heap が 空の場合 *)
  - destruct h0 as [| old_l locs_tail];
      simpl in *; try lia.

    destruct h1 as [| old_next nexts_tail];
      simpl in *; try lia.

    destruct h2 as [| old_mark marks_tail];
      simpl in *; try lia.

    split; first done.

    rep liRStep; liShow.

  (* Heap が 非空の場合 *)
  (* big_sepL は"先頭の資源*残りの資源"のように定義されているので
     Hfirst :: Htail になるように分解し 
     - Hfirst は変更されないのでそのまま，
     - Htail は新規ノードの Node_ty と freeable_nz を証明したうえで
       Htail と新規ノードを big_sepL_app で結合し Htail_new を作る
    -> Hfirst ∗ Htail_new により invariant を再構成
       合わせて長さやすべての next が NULL か locs に含まれることを示す
  *)
  - destruct h0 as [| old_l locs_tail];
      simpl in *; try lia.

    destruct h1 as [| old_next nexts_tail];
      simpl in *; try lia.

    destruct h2 as [| old_mark marks_tail];
      simpl in *; try lia.

    injection Hlen_locs as Hlen_locs_tail.
    injection Hlen_nexts as Hlen_nexts_tail.
    injection Hlen_marks as Hlen_marks_tail.

    split.
    {
      rewrite length_app /=.
      lia.
    }

    iRename select
      ((∃ (l n : loc) (m : bool), _) ∗ _)%I
      into "Hnodes".

    iDestruct "Hnodes" as "(Hfirst & Htail)".

    assert (Hmap_vals :
      list_fmap Z Z id vals_tail = vals_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_locs :
      list_fmap loc loc id locs_tail = locs_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_nexts :
      list_fmap loc loc id nexts_tail = nexts_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_marks :
      list_fmap bool bool id marks_tail = marks_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    iEval (
      rewrite
        Hmap_vals
        Hmap_locs
        Hmap_nexts
        Hmap_marks
    ) in "Htail".

    iAssert (
      [∗ list] k ↦ v6 ∈ vals_tail,
        ∃ (l n : loc) (m : bool),
          ⌜(locs_tail ++ [x']) !! k = Some l⌝ ∗
          ⌜(nexts_tail ++ [NULL_loc]) !! k = Some n⌝ ∗
          ⌜(marks_tail ++ [false]) !! k = Some m⌝ ∗
          guarded true
            (l ◁ₗ[π, Owned]
              # -[#v6; #n; #m]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc
    )%I with "[Htail]" as "Htail_ext".
    {
      iApply (big_sepL_impl with "Htail").

      iIntros "!>" (k v6 Hlookup) "Hnode_old".

      iDestruct "Hnode_old" as
        (l n m)
        "(%Hloc & %Hnext & %Hmark &
          Hguard_old & Hfree_old)".

      iExists l, n, m.

      iSplit.
      {
        iPureIntro.

        pose proof
          (lookup_lt_Some _ _ _ Hlookup)
          as Hlt.

        rewrite lookup_app_l.
        - exact Hloc.
        - rewrite Hlen_locs_tail.
          exact Hlt.
      }

      iSplit.
      {
        iPureIntro.

        pose proof
          (lookup_lt_Some _ _ _ Hlookup)
          as Hlt.

        rewrite lookup_app_l.
        - exact Hnext.
        - rewrite Hlen_nexts_tail.
          exact Hlt.
      }

      iSplit.
      {
        iPureIntro.

        pose proof
          (lookup_lt_Some _ _ _ Hlookup)
          as Hlt.

        rewrite lookup_app_l.
        - exact Hmark.
        - rewrite Hlen_marks_tail.
          exact Hlt.
      }

      iFrame.
    }

    iAcquireCredits as "Hcred_new".

    iApply (prove_with_subtype_stratify x').
    rep liRStep; liShow.

    iApply prove_with_subtype_default.

    iRename select
      (freeable_nz x' _ _ _)
      into "Hfree_new".
      
    assert (Hlen_nexts_new :
      S (length (nexts_tail ++ [NULL_loc])) =
      S (length (vals_tail ++ [v]))).
    {
      rewrite !length_app /=.
      lia.
    }

    assert (Hlen_marks_new :
      S (length (marks_tail ++ [false])) =
      S (length (vals_tail ++ [v]))).
    {
      rewrite !length_app /=.
      lia.
    }

    assert (Hnext_valid_new :
      Forall
        (λ n : loc,
          n = NULL_loc ∨
          n ∈ ((old_l :: locs_tail) ++ [x']))
        ((old_next :: nexts_tail) ++ [NULL_loc])).
    {
      apply Forall_app.
      split.
      {
        eapply Forall_impl.
        - exact Hnext_valid.
        - intros n Hn.
          destruct Hn as [Hnull | Hin].
          + left.
            exact Hnull.
          + right.
            apply elem_of_app.
            left.
            exact Hin.
      }

      constructor.
      - left.
        done.
      - constructor.
    }

    iSplitL
      "Hfirst Htail_ext Hcred_new Hfree_new".
    {
      liRStep; liShow.

      iRename select
        (_ ◁ₗ[_, Owned] _ @ _)%I
        into "Hnew".

      iAssert (
        [∗ list] k ↦ v6 ∈ vals_tail ++ [v],
          ∃ (l n : loc) (m : bool),
            ⌜(locs_tail ++ [x']) !! k = Some l⌝ ∗
            ⌜(nexts_tail ++ [NULL_loc]) !! k = Some n⌝ ∗
            ⌜(marks_tail ++ [false]) !! k = Some m⌝ ∗
            guarded true
              (l ◁ₗ[π, Owned]
                # -[#v6; #n; #m]
                @ (◁ (Node_ty <INST!>))) ∗
            freeable_nz l
              (ly_size (use_layout_alg' Node_sls))
              1 HeapAlloc
      )%I with
        "[Htail_ext Hcred_new Hnew Hfree_new]"
        as "Htail_new".
      {
        rewrite big_sepL_app.

        iSplitL "Htail_ext".
        {
          iExact "Htail_ext".
        }

        simpl.

        iSplitL "Hcred_new Hnew Hfree_new".
        {
          iExists x', NULL_loc, false.

          iSplitR "Hcred_new Hnew Hfree_new".
          {
            iPureIntro.

            rewrite Nat.add_0_r.
            rewrite -Hlen_locs_tail.
            rewrite lookup_app_r; last lia.
            rewrite Nat.sub_diag /=.
            done.
          }

          iSplitR "Hcred_new Hnew Hfree_new".
          {
            iPureIntro.

            rewrite Nat.add_0_r.
            rewrite -Hlen_nexts_tail.
            rewrite lookup_app_r; last lia.
            rewrite Nat.sub_diag /=.
            done.
          }

          iSplitR "Hcred_new Hnew Hfree_new".
          {
            iPureIntro.

            rewrite Nat.add_0_r.
            rewrite -Hlen_marks_tail.
            rewrite lookup_app_r; last lia.
            rewrite Nat.sub_diag /=.
            done.
          }

          iSplitL "Hcred_new Hnew".
          {
            rewrite /guarded /=.
            iFrame.
          }

          iExact "Hfree_new".
        }

        done.
      }

      iDestruct "Hfirst" as
        (l n m)
        "(%Heq_l & %Heq_n & %Heq_m &
          Hguard_first & Hfree_first)".

      injection Heq_l as Heq_l.
      subst l.

      injection Heq_n as Heq_n.
      subst n.

      injection Heq_m as Heq_m.
      subst m.

      iRevert
        "Hguard_first Hfree_first Htail_new".

      rep liRStep; liShow.

    }

    rep liRStep; liShow.
    

  all: print_remaining_goal.

  Unshelve.
  all: sidecond_solver.

  Unshelve.
  all: sidecond_hammer.

  Unshelve.
  all: print_remaining_sidecond.
Qed.

End proof.
