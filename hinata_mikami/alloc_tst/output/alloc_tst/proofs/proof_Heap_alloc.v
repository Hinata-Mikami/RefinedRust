From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.alloc_tst.generated Require Import generated_code_alloc_tst generated_specs_alloc_tst generated_template_Heap_alloc.

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

  (* ptr を返す式 move "__0" を処理する *)
  rep liRStep; liShow.

  liInst Hevar_x
  (match h with
   | [] => v
   | x :: _ => x
   end).

  liInst Hevar_x0
  (match h with
   | [] => []
   | _ :: xs => xs ++ [v]
   end).

  liShow.

  destruct h as [| old_v h_tail].
  - destruct h0 as [| old_l h0_tail]; simpl in *; try lia.

    split; first done.
    (* h = [], h0 = [] の場合 *)
    iAcquireCredits as "Hcred".

    iApply (prove_with_subtype_stratify x').
    rep liRStep; liShow.
    iApply prove_with_subtype_default.

    (* こちらは既にコンテキストにあるので先に名前を付けられる *)
    iRename select
      (freeable_nz x' _ _ _)
      into "Hfree".

    (* 左: 新しい Heap invariant
       右: Heap 自体を再び畳む処理 *)
    iSplitL "Hcred Hfree".
    {
      (* 最初の inhale を実行して、Node 所有権を
         Iris コンテキストへ入れる *)
      liRStep; liShow.

      iRename select
      (_ ◁ₗ[_, Owned] _ @ _)%I
      into "Hnode".

      (* inhale True ∗ True と、その後の exhale を進める *)
      rep liRStep; liShow.
    }

    (* 現在表示されている trigger_tc を処理 *)
    rep liRStep; liShow.

  - destruct h0 as [| old_l h0_tail]; simpl in *; try lia.

      (* Hlen : S (length h0_tail) = S (length h_tail) *)
    injection Hlen as Hlen_tail.

    (* length (h_tail ++ [v]) = S (length h0_tail) *)
    split.
    {
      rewrite length_app /=.
      lia.
    }

    (* 既存の先頭ノードと tail を取り出す *)
    iRename select
      ((∃ l : loc, _) ∗ _)%I
      into "Hnodes".
    iDestruct "Hnodes" as "(Hfirst & Htail)".

    (* fmap id を通常のリストに正規化する *)
    assert (Hmap_h :
      list_fmap Z Z id h_tail = h_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    assert (Hmap_l :
      list_fmap loc loc id h0_tail = h0_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    iEval (rewrite Hmap_h Hmap_l) in "Htail".

    (* 既存 tail の lookup を、
       h0_tail から h0_tail ++ [x'] へ持ち上げる *)
    iAssert (
      [∗ list] n ↦ v6 ∈ h_tail,
        ∃ l : loc,
          ⌜(h0_tail ++ [x']) !! n = Some l⌝ ∗
          guarded true
            (l ◁ₗ[π, Owned]
              # -[#v6]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc
    )%I with "[Htail]" as "Htail_ext".
    {
      iApply (big_sepL_impl with "Htail").
      iIntros "!>" (n v6 Hlookup) "Hnode_old".

      iDestruct "Hnode_old" as (l)
        "(%Hloc & Hown & Hfree_old)".

      iExists l.
      iSplit.
      {
        iPureIntro.

        pose proof
          (lookup_lt_Some _ _ _ Hlookup)
          as Hlt.

        rewrite lookup_app_l.
        - exact Hloc.
        - rewrite Hlen_tail.
          exact Hlt.
      }

      iFrame.
    }

    (* 先頭ノードをいったん guarded でない形にする *)
    (* iRevert "Hfirst".

    rep <-! liRStep; liShow.

    apply_update (updateable_strip_guards).

    (* strip_guards の初期処理 *)
    rep liRStep; liShow.

    (* 現在残っている FindOptGuarded を明示的に処理 *)
    (* liFindInContext.
    liShow. *)

    (* guard の除去とループ終了 *)
    rep liRStep; liShow.

    (* ここまで来ると、トップレベルの先頭所有権は
       guarded true ではなく通常の ownership になっている *)

    iAcquireCredits as "Hcred_first".
    iAcquireCredits as "Hcred_new". 
    
    (* updateable_core から元の prove_with_subtype ゴールへ戻す *)
    rewrite updateable_eq.
    liShow.

    rep liRStep; liShow.

    rewrite -Hlen_tail Nat.sub_diag /=.
    rep liRStep; liShow.
    *)


    (* 新規ノードの guarded true に使う *)
    iAcquireCredits as "Hcred_new".

    iApply (prove_with_subtype_stratify x').
    rep liRStep; liShow.

    iApply prove_with_subtype_default.

    iRename select
      (freeable_nz x' _ _ _)
      into "Hfree_new".

    iSplitL "Hfirst Htail_ext Hcred_new Hfree_new".
    {
      liRStep; liShow.

      iRename select
        (_ ◁ₗ[_, Owned] _ @ _)%I
        into "Hnew".

      iAssert (
        [∗ list] n ↦ v6 ∈ h_tail ++ [v],
          ∃ l : loc,
            ⌜(h0_tail ++ [x']) !! n = Some l⌝ ∗
            guarded true
              (l ◁ₗ[π, Owned]
                # -[#v6]
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
          iExists x'.

          iSplitR "Hcred_new Hnew Hfree_new".
          {
            iPureIntro.
            rewrite Nat.add_0_r.
            rewrite -Hlen_tail.
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

      iDestruct "Hfirst" as (l)
      "(%Heq_l & Hguard_first & Hfree_first)".

      injection Heq_l as Heq_l.
      subst l.

      (* guarded は展開しない *)
      iRevert "Hguard_first Hfree_first Htail_new".

      rep liRStep; liShow.

    }
    {
      rep liRStep; liShow.
    }



  

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
