From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_alloc.


Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
(* 

(* Heap_alloc_prrof を解くための補題？ *)
(* 自動証明 rep liRStep でどこかで使われた？ *)
Lemma simplify_goal_big_sepL_app {A} (xs1 xs2 : list A)
  (Φ : nat → A → iProp Σ) T :
  ([∗ list] i ↦ x ∈ xs1, Φ i x) ∗
  ([∗ list] i ↦ x ∈ xs2, Φ (length xs1 + i)%nat x) ∗
  T
  ⊢ simplify_goal ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  rewrite /simplify_goal.
  rewrite big_sepL_app.
  iIntros "($ & $ & $)".
Qed.

Lemma simplify_goal_big_sepL_cons_snoc {A} (a b : A) (xs : list A)
  (Φ : nat → A → iProp Σ) T :
  ([∗ list] i ↦ x ∈ a :: xs, Φ i x) ∗
  Φ (length (a :: xs)) b ∗
  T
  ⊢ simplify_goal ([∗ list] i ↦ x ∈ a :: xs ++ [b], Φ i x) T.
Proof.
  rewrite /simplify_goal.
  change (a :: xs ++ [b]) with ((a :: xs) ++ [b]).
  rewrite big_sepL_app.
  simpl.
  rewrite Nat.add_0_r.
  iIntros "(Hxs & Hb & HT)".
  iFrame.
Qed.

Definition simplify_goal_big_sepL_cons_snoc_inst :=
  [instance @simplify_goal_big_sepL_cons_snoc with 0%N].
Global Existing Instance simplify_goal_big_sepL_cons_snoc_inst. *)

Lemma Heap_alloc_proof (π : thread_id) :
  Heap_alloc_lemma π.
Proof.
  Heap_alloc_prelude.

  rep <-! liRStep; liShow.

  (* 
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

  liInst Hevar_x0 (h1 ++ [NULL_loc]).
  liInst Hevar_x3 (h2 ++ [false]).
  rep liRStep; liShow.

  liInst Hevar_l
    (match h0 with
    | [] => x'
    | l :: _ => l
    end).

  liInst Hevar_n
    (match h1 with
    | [] => NULL_loc
    | n :: _ => n
    end).

  liInst Hevar_m
    (match h2 with
    | [] => false
    | m :: _ => m
    end).

  rep liRStep; liShow.

  destruct h0 as [| old_l h0_tail]; simpl in *.

  - destruct h as [| old_v h_tail]; simpl in *; try lia.
    destruct h1 as [| old_n h1_tail]; simpl in *; try lia.
    destruct h2 as [| old_m h2_tail]; simpl in *; try lia.

    rep liRStep; liShow.
  
  - destruct h as [| old_v h_tail]; simpl in *; try lia.
    destruct h1 as [| old_n h1_tail]; simpl in *; try lia.
    destruct h2 as [| old_m h2_tail]; simpl in *; try lia.

    iRename select ((∃ (l n : loc) (m : bool), _) ∗ _)%I into "Hnodes".
    iDestruct "Hnodes" as "(Hfirst & Htail)".
    iDestruct "Hfirst" as (l n m) "(%Hloc & %Hnext & %Hmark & Hown_old & Hfree_old)".
    inversion Hloc; subst l; clear Hloc.
    inversion Hnext; subst n; clear Hnext.
    inversion Hmark; subst m; clear Hmark.

    (* iRevert "Hown_old".
    rep liRStep; liShow.
    apply_update (updateable_strip_guards).
    rep liRStep; liShow.
    rep liRStep; liShow. *)

    (* iEval (rewrite /guarded /=) in "Hown_old".

    iDestruct "Hown_old" as "(Hcred_old & Hown_old)".
    iEval (rewrite /have_creds) in "Hcred_old".
    iDestruct "Hcred_old" as "(Hlc_old & Hreceipt_old)".

    iEval (rewrite /num_cred lc_succ) in "Hlc_old".
    iDestruct "Hlc_old" as "(Hlc_one & Hlc_rest)".

    iMod (lc_fupd_elim_later ⊤ with "Hlc_one Hown_old") as "Hown_old".

    rep liRStep; liShow. *)

    assert (Hmap_h : list_fmap Z Z id h_tail = h_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }
    assert (Hmap_l : list_fmap loc loc id h0_tail = h0_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }
    assert (Hmap_n : list_fmap loc loc id h1_tail = h1_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }
    assert (Hmap_m : list_fmap bool bool id h2_tail = h2_tail).
    {
      autorewrite with lithium_rewrite.
      done.
    }

    injection Hlen_locs as Hlen_locs_tail.
    injection Hlen_nexts as Hlen_nexts_tail.
    injection Hlen_marks as Hlen_marks_tail.

    iAssert (
      [∗ list] i↦x ∈ list_fmap Z Z id h_tail,
        ∃ (l n : loc) (m : bool),
          ⌜(h0_tail ++ [x']) !! i = Some l⌝ ∗
          ⌜(h1_tail ++ [NULL_loc]) !! i = Some n⌝ ∗
          ⌜(h2_tail ++ [false]) !! i = Some m⌝ ∗
          guarded true
            (l ◁ₗ[π, Owned]
              # -[#x; #n; #m]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc
    )%I with "[Htail]" as "Htail_app".
    {
      iApply (big_sepL_impl with "Htail").
      iIntros "!>" (i x Hlookup) "Hnode".

      iDestruct "Hnode" as (l n m) "(%Hloc & %Hnext & %Hmark & Hown & Hfree)".

      rewrite Hmap_h in Hlookup.
      rewrite Hmap_l in Hloc.
      rewrite Hmap_n in Hnext.
      rewrite Hmap_m in Hmark.

      pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt.

      iExists l, n, m.
      iSplit.
      {
        iPureIntro.
        rewrite lookup_app_l.
        - exact Hloc.
        - rewrite Hlen_locs_tail. exact Hlt.
      }
      iSplit.
      {
        iPureIntro.
        rewrite lookup_app_l.
        - exact Hnext.
        - rewrite Hlen_nexts_tail. exact Hlt.
      }
      iSplit.
      {
        iPureIntro.
        rewrite lookup_app_l.
        - exact Hmark.
        - rewrite Hlen_marks_tail. exact Hlt.
      }
      iFrame.
    }

    iEval (rewrite Hmap_h) in "Htail_app".

    iAssert (
      [∗ list] i↦x ∈ old_v :: h_tail,
        ∃ (l n : loc) (m : bool),
          ⌜(old_l :: h0_tail ++ [x']) !! i = Some l⌝ ∗
          ⌜(old_n :: h1_tail ++ [NULL_loc]) !! i = Some n⌝ ∗
          ⌜(old_m :: h2_tail ++ [false]) !! i = Some m⌝ ∗
          guarded true
            (l ◁ₗ[π, Owned]
              # -[#x; #n; #m]
              @ (◁ (Node_ty <INST!>))) ∗
          freeable_nz l
            (ly_size (use_layout_alg' Node_sls))
            1 HeapAlloc
    )%I with "[Hown_old Hfree_old Htail_app]" as "Hnodes_old".
    {
      simpl.
      iSplitL "Hown_old Hfree_old".
      {
        iExists old_l, old_n, old_m.
        simpl.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iFrame.
      }

      iApply (big_sepL_impl with "Htail_app").
      iIntros "!>" (i x Hlookup) "Hnode".
      iDestruct "Hnode" as (l n m) "(%Hloc & %Hnext & %Hmark & Hown & Hfree)".

      iExists l, n, m.
      simpl.
      iSplit.
      {
        iPureIntro.
        exact Hloc.
      }
      iSplit.
      {
        iPureIntro.
        exact Hnext.
      }
      iSplit.
      {
        iPureIntro.
        exact Hmark.
      }
      iFrame.
    }

    iRevert "Hnodes_old".
    rep liRStep; liShow.

    replace (length h_tail - length h0_tail)%nat with 0%nat by lia.
    simpl.

    rep liRStep; liShow. *)


    all: print_remaining_goal.
    Unshelve. all: sidecond_solver.
    Unshelve. all: sidecond_hammer.

    (* all: try solve [
    apply Forall_app;
    split;
    [
      eapply Forall_impl; [| exact Hnext_valid];
      intros n Hn;
      destruct Hn as [Hnull | Hin];
      [ left; exact Hnull
      | right; apply elem_of_app; left; exact Hin ]
    |
      constructor;
      [ left; reflexivity
      | constructor ]
    ]
    ]. *)

    Unshelve. all: print_remaining_sidecond.
   


Qed.
End proof.
