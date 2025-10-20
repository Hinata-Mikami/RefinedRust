From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_push.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma Vec_T_push_proof (π : thread_id) :
  Vec_T_push_lemma π.
Proof.
  Vec_T_push_prelude.

  rep <-! liRStep; liShow.
  { apply_update (updateable_typed_array_access x'0 (length self ) (st_of T_ty)).
    repeat liRStep; liShow. }
  { rep <-! liRStep; liShow.
    apply_update (updateable_typed_array_access x1 (length self ) (st_of T_ty)).
    repeat liRStep; liShow. }


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.

  (*all: match type of Hlen_cap with (Z.of_nat (length (project_vec_els ?len2 ?xs2)) < _)%Z => rename len2 into len; rename xs2 into xs end.*)
  all: match type of Hxs with _ = project_vec_els ?len2 ?xs2 => 
      rename xs2 into xs';
      specialize (project_vec_els_length len2 xs') as Hlen_eq;
      rewrite -Hxs !length_fmap in Hlen_eq
    end.
  (*all: rewrite project_vec_els_length in Hlen_cap.*)

  Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal.
  all: try solve_goal with (lia).
  all: try (unfold_common_defs; solve_goal with (lia)).

  (*{ rewrite project_vec_els_length in Hlen_eq. solve_goal. }*)
  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply list_lookup_insert_Some'.
    split;normalize_and_simpl_goal.
    1: lia.
    rewrite Hxs.
    erewrite project_vec_els_lookup_mono; [solve_goal|lia|].
    rewrite lookup_app_l; [done|lia].
  }
  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply (list_eq_split (length self)).
    - rewrite take_insert_ge/=; [|lia]. 
      rewrite !fmap_app.
      rewrite take_app_length' ?project_vec_els_length; last solve_goal.
      rewrite project_vec_els_take project_vec_els_take_r.
      rewrite take_app_le; [|lia]. 
      rewrite take_ge; [|lia].
      rewrite Nat.min_l; last lia.
      rewrite -Hxs list_fmap_compose//.
    - rewrite drop_insert_ge/=; [|lia].
      rewrite !fmap_app.
      rewrite drop_app_length' ?project_vec_els_length; last solve_goal.
      rewrite project_vec_els_drop. apply list_eq_singleton. 
      split; solve_goal.
  }
  { revert select (ly_size (mk_array_layout _ _) ≤ _).
    move: Hcap. 
    rewrite ly_size_mk_array_layout.
    clear. nia. }
  { revert select (ly_size (mk_array_layout _ _) ≤ _).
    move: Hcap. 
    rewrite ly_size_mk_array_layout.
    clear. nia. }
  {
    (* TODO *)
    assert (length self < length xs') as Hlt.
    { opose proof* (Hlook_2 (length self)) as Hlook_3; first (simpl; lia).
      apply lookup_lt_Some in Hlook_3.
      lia. }
    simpl in Hlt.

    rewrite project_vec_els_insert_lt /=; [|lia].
    apply list_lookup_insert_Some'. split; normalize_and_simpl_goal. 
    { lia. }
    { rewrite Hxs. erewrite project_vec_els_lookup_mono; [solve_goal|lia|done]. }
  }
  {
    (* TODO should get this in a different way *)
    assert (length self < length xs') as Hlt.
    { opose proof* (Hlook_2 (length self)) as Hlook_3; first (simpl; lia).
      apply lookup_lt_Some in Hlook_3.
      lia. }
    simpl in *. lia. }
  {
    (* TODO we should get this in a different way *)
    assert (length self < length xs') as Hlt.
    { opose proof* (Hlook_2 (length self)) as Hlook_3; first (simpl; lia).
      apply lookup_lt_Some in Hlook_3.
      lia. }
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply (list_eq_split (length self)).
    - rewrite take_insert_ge/=; [|lia]. 
      rewrite !fmap_app.
      rewrite take_app_length' ?project_vec_els_length; last solve_goal.
      rewrite project_vec_els_take. rewrite Hxs. f_equal. lia.
    - rewrite drop_insert_ge/=; [|lia]. rewrite !fmap_app drop_app_length' ?project_vec_els_length; [|solve_goal].
      rewrite project_vec_els_drop.
      apply list_eq_singleton. split; first solve_goal.
      normalize_and_simpl_goal. solve_goal.
  }

  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
