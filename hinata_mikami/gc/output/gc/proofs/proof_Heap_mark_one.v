From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_Heap_mark_one.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Heap_mark_one_proof (π : thread_id) :
  Heap_mark_one_lemma π.
Proof.
  Heap_mark_one_prelude.

  rep <-! liRStep; liShow.

  (* locs は非空 *)
  destruct h0 as [| old_l locs_tail].
  {
    simpl in H.
    lia.
  }

  (* length locs = length vals より vals も非空 *)
  destruct h as [| old_v vals_tail].
  {
    simpl in Hlen_locs.
    lia.
  }

  (* nexts も非空 *)
  destruct h1 as [| old_next nexts_tail].
  {
    simpl in Hlen_nexts.
    lia.
  }

  (* marks も非空 *)
  destruct h2 as [| old_mark marks_tail].
  {
    simpl in Hlen_marks.
    lia.
  }

  injection Hlen_locs as Hlen_locs_tail.
  injection Hlen_nexts as Hlen_nexts_tail.
  injection Hlen_marks as Hlen_marks_tail.

  iRename select
    ([∗ list] i ↦ v4 ∈ (id <$> (old_v :: vals_tail)),
      ∃ (l n : loc) (m : bool), _)%I
    into "Hnodes".

  iDestruct "Hnodes" as "(Hfirst & Htail)".

  (* 先頭ノードの情報を取り出す *)
  iDestruct "Hfirst" as
    (l n m)
    "(%Hloc & %Hnext & %Hmark &
      Hguard & Hfree)".

  assert (Hmap_vals :
    list_fmap Z Z id (old_v :: vals_tail)
      = old_v :: vals_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  assert (Hmap_locs :
    list_fmap loc loc id (old_l :: locs_tail)
      = old_l :: locs_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  assert (Hmap_nexts :
    list_fmap loc loc id (old_next :: nexts_tail)
      = old_next :: nexts_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  assert (Hmap_marks :
    list_fmap bool bool id (old_mark :: marks_tail)
      = old_mark :: marks_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  simpl in Hloc, Hnext, Hmark.

  injection Hloc as Hloc.
  subst l.

  injection Hnext as Hnext.
  subst n.

  injection Hmark as Hmark.
  subst m.

  apply_update updateable_strip_guards.

  rep <-! liRStep; liShow.

  iRename select
    (old_l ◁ₗ[_, Owned] _ @ _)%I
    into "Hnode_new".

  iAcquireCredits as "Hcred".

  (* ここではまだ guarded に戻さない。
     old_l の直接 ownership を Lithium に返す。 *)
  iRevert "Hnode_new Hfree Htail".

  rep <-! liRStep; liShow.

  rep liRStep; liShow.

  liInst Hevar_x old_v.
  liInst Hevar_x2 vals_tail.
  liInst Hevar_x0 (old_next :: nexts_tail).
  liInst Hevar_x3 (true :: marks_tail).

  liShow.

  rep liRStep; liShow.

  
  assert (Hmap_vals_tail :
    list_fmap Z Z id vals_tail = vals_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }
  assert (Hmap_locs_tail :
    list_fmap loc loc id locs_tail = locs_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }
  assert (Hmap_nexts_tail :
    list_fmap loc loc id nexts_tail = nexts_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }
  assert (Hmap_marks_tail :
    list_fmap bool bool id marks_tail = marks_tail).
  {
    autorewrite with lithium_rewrite.
    done.
  }

  iRename select
    ([∗ list] k ↦ y ∈ _,
      ∃ (l n : loc) (m : bool), _)%I
    into "Htail".

  unfold list_fmap in Hmap_vals_tail.

  iEval (
    rewrite Hmap_vals_tail
            Hmap_locs_tail
            Hmap_nexts_tail
            Hmap_marks_tail
  ) in "Htail".

  iRevert "Htail".

  rep liRStep; liShow.


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
