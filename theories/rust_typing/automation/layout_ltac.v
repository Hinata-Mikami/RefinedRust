Require Import Stdlib.Strings.String.
From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export type ltypes hlist.
From refinedrust.automation Require Import ident_to_string lookup_definition proof_state.
From refinedrust Require Import int programs.
Set Default Proof Using "Type".


(* Reduced version of simplify_eq *)
Ltac subst_with Heq :=
  (* TODO: better implementation? *)
  try match type of Heq with
  | ?a = ?b =>
      is_var a;
      subst a
  | ?a = ?b =>
      is_var b;
      subst b
  end;
  try match type of Heq with
  | ?a = ?a =>
      clear Heq
  end
.

(** ** Layout sidecondition solver *)
Section solve_layout_alg_tac.
  Context `{!LayoutAlg}.

  Lemma use_layout_alg'_layout_tac st ly :
    syn_type_has_layout st ly → use_layout_alg' st = ly.
  Proof.
    rewrite /syn_type_has_layout /use_layout_alg'.
    move => -> //.
  Qed.

  Lemma use_layout_alg_layout_tac st ly :
    syn_type_has_layout st ly → use_layout_alg st = Some ly.
  Proof. done. Qed.

  Local Definition syn_type_has_layout_multi_pred : (var_name * syn_type) → (var_name * layout) → Prop :=
    λ '(field_name, field_spec) res,
      ∃ field_name2 field_ly,
      syn_type_has_layout field_spec field_ly ∧ field_name = field_name2 ∧ res = (field_name2, field_ly).

  (* structs *)
  Lemma syn_type_has_layout_struct_tac name fields fields' repr ly ly' :
    Forall2 syn_type_has_layout_multi_pred fields fields' →
    struct_layout_alg name fields' repr = Some ly' →
    ly = layout_of ly' →
    syn_type_has_layout (StructSynType name fields repr) ly.
  Proof.
    intros Ha Hb ->.
    eapply syn_type_has_layout_struct; last done.
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma struct_layout_spec_has_layout_tac (sls : struct_layout_spec) fields' (sl sl' : struct_layout) :
    Forall2 syn_type_has_layout_multi_pred sls.(sls_fields) fields' →
    struct_layout_alg sls.(sls_name) fields' sls.(sls_repr) = Some sl' →
    sl = sl' →
    struct_layout_spec_has_layout sls sl.
  Proof.
    intros Ha Hb ->.
    eapply use_struct_layout_alg_Some; last done.
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma use_struct_layout_alg_layout_tac (sls : struct_layout_spec) (sl : struct_layout) :
    struct_layout_spec_has_layout sls sl → use_struct_layout_alg sls = Some sl.
  Proof. done. Qed.

  (* enums *)
  Lemma syn_type_has_layout_enum_tac name variants variants' (it : int_type) ly ul sl repr struct_repr union_repr :
    Forall2 syn_type_has_layout_multi_pred variants variants' →
    union_repr = union_repr_of_enum_repr repr →
    struct_repr = struct_repr_of_enum_repr repr →
    union_layout_alg name variants' union_repr = Some ul →
    struct_layout_alg name [("discriminant", it_layout it); ("data", ul : layout)] struct_repr = Some sl →
    ly = layout_of sl →
    syn_type_has_layout (EnumSynType name it variants repr) ly.
  Proof.
    intros Ha -> -> Hb Hc ->.
    eapply syn_type_has_layout_enum; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma enum_layout_spec_has_layout_tac (els : enum_layout_spec) variants' (ul : union_layout) (sl sl' : struct_layout) struct_repr union_repr :
    Forall2 syn_type_has_layout_multi_pred els.(els_variants) variants' →
    union_repr = union_repr_of_enum_repr els.(els_repr) →
    struct_repr = struct_repr_of_enum_repr els.(els_repr) →
    union_layout_alg els.(els_name) variants' union_repr = Some ul →
    struct_layout_alg els.(els_name) [("discriminant", it_layout els.(els_tag_it)); ("data", ul : layout)] struct_repr = Some sl' →
    sl = sl' →
    enum_layout_spec_has_layout els sl.
  Proof.
    intros Ha -> -> Hb Hc ->.
    eapply use_enum_layout_alg_Some; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma use_enum_layout_alg_layout_tac (els : enum_layout_spec) (el : struct_layout) :
    enum_layout_spec_has_layout els el → use_enum_layout_alg els = Some el.
  Proof. done. Qed.

  (* unions *)
  Lemma syn_type_has_layout_union_tac name variants variants' ly ul repr :
    Forall2 syn_type_has_layout_multi_pred variants variants' →
    union_layout_alg name variants' repr = Some ul →
    ly = ul_layout ul →
    syn_type_has_layout (UnionSynType name variants repr) ly.
  Proof.
    intros Ha Hb ->.
    eapply syn_type_has_layout_union; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma union_layout_spec_has_layout_tac (uls : union_layout_spec) variants' (ul ul' : union_layout) :
    Forall2 syn_type_has_layout_multi_pred uls.(uls_variants) variants' →
    union_layout_alg uls.(uls_name) variants' uls.(uls_repr) = Some ul' →
    ul = ul' →
    union_layout_spec_has_layout uls ul.
  Proof.
    intros Ha Hb ->.
    eapply use_union_layout_alg_Some; [ | done..].
    eapply Forall2_impl; first apply Ha.
    intros [] [] (? & ? & ? & -> & [= -> ->]). eauto.
  Qed.
  Lemma use_union_layout_alg_layout_tac (uls : union_layout_spec) (ul : union_layout) :
    union_layout_spec_has_layout uls ul → use_union_layout_alg uls = Some ul.
  Proof. done. Qed.

  Lemma syn_type_has_layout_untyped_alg_tac st ly ly' :
    ly = ly' →
    syn_type_has_layout st ly →
    syn_type_has_layout (UntypedSynType (use_layout_alg' st)) ly'.
  Proof.
    intros <- Hst. eapply (syn_type_has_layout_make_untyped st).
    - rewrite /use_layout_alg' Hst //.
    - rewrite /use_layout_alg' Hst//.
  Qed.
  Lemma syn_type_has_layout_untyped_struct_alg_tac (sls : struct_layout_spec) sl ly' :
    ly' = sl →
    syn_type_has_layout sls sl →
    syn_type_has_layout (UntypedSynType (use_struct_layout_alg' sls)) ly'.
  Proof.
    intros -> Hst.
    rewrite /use_struct_layout_alg'.
    specialize (use_layout_alg_struct_Some_inv _ _  Hst) as (sl' & -> & <-).
    eapply (syn_type_has_layout_make_untyped sls); done.
  Qed.

  Lemma syn_type_has_layout_untyped_enum_alg_tac (els : enum_layout_spec) el ly' :
    ly' = el →
    syn_type_has_layout els el →
    syn_type_has_layout (UntypedSynType (use_enum_layout_alg' els)) ly'.
  Proof.
    intros -> Hst.
    rewrite /use_enum_layout_alg'.
    specialize (use_layout_alg_enum_Some_inv _ _  Hst) as (sl' & -> & <-).
    eapply (syn_type_has_layout_make_untyped els); done.
  Qed.

  Lemma syn_type_has_layout_untyped_ptr_tac ly' :
    ly' = void* →
    syn_type_has_layout (UntypedSynType void*) ly'.
  Proof.
    intros ->.
    eapply (syn_type_has_layout_make_untyped PtrSynType); first done.
    by apply syn_type_has_layout_ptr.
  Qed.
  Lemma syn_type_has_layout_untyped_unit_tac ly' :
    ly' = layout_of unit_sl →
    syn_type_has_layout (UntypedSynType unit_sl) ly'.
  Proof.
    intros ->.
    eapply (syn_type_has_layout_make_untyped UnitSynType); first done.
    by apply syn_type_has_layout_unit.
  Qed.
  Lemma syn_type_has_layout_untyped_int_tac ly' it :
    ly' = it_layout it →
    syn_type_has_layout (UntypedSynType (it_layout it)) ly'.
  Proof.
    intros ->.
    eapply (syn_type_has_layout_make_untyped (IntSynType it)); first done.
    by apply syn_type_has_layout_int.
  Qed.
End solve_layout_alg_tac.

Section simplify_layout_tac.
  Context `{!LayoutAlg}.

  Lemma simplify_use_layout_alg' T_st T_ly :
    use_layout_alg T_st = Some T_ly →
    use_layout_alg' T_st = T_ly.
  Proof.
    rewrite /use_layout_alg' => -> //.
  Qed.

  Lemma simplify_use_struct_layout_alg' sls sl :
    use_struct_layout_alg sls = Some sl →
    use_struct_layout_alg' sls = sl.
  Proof.
    rewrite /use_struct_layout_alg' => -> //.
  Qed.

  Lemma simplify_use_enum_layout_alg' els el :
    use_enum_layout_alg els = Some el →
    use_enum_layout_alg' els = el.
  Proof.
    rewrite /use_enum_layout_alg' => -> //.
  Qed.

  Lemma simplify_use_union_layout_alg' uls ul :
    use_union_layout_alg uls = Some ul →
    use_union_layout_alg' uls = ul.
  Proof.
    rewrite /use_union_layout_alg' => -> //.
  Qed.

  Lemma simplify_ot_layout ot ot' :
    ot = ot' →
    ot_layout ot = (ot_layout ot').
  Proof.
    intros ->; done.
  Qed.

  Lemma simplify_ot_layout_var T_st ly :
    use_layout_alg T_st = Some ly →
    ot_layout (use_op_alg' T_st) = ly.
  Proof.
    intros Hst.
    rewrite /use_op_alg'.
    apply syn_type_has_layout_op_alg in Hst as (ot & -> & <-).
    done.
  Qed.
End simplify_layout_tac.

(** Solve goals of the forms
  - [use_layout_alg st = Some ?ly]
  - [use_layout_alg' st = ?ly]
  - [syn_type_has_layout st ?ly]
  where [ly] may or may not be an evar.
  *)
(* Declaration, definition is below. *)
Ltac solve_layout_alg := idtac.

Ltac solve_ot_eq := idtac.

(* We assume a let-binding [H_ly] has been introduced into the context in which we can rewrite *)
Ltac simplify_layout' H_ly :=
  repeat match type of H_ly with
  | _ = use_layout_alg' ?st =>
      erewrite (simplify_use_layout_alg' st) in H_ly;
      [ | solve_layout_alg]
  | _ = use_struct_layout_alg' ?sls =>
      erewrite (simplify_use_struct_layout_alg' sls) in H_ly;
      [ | solve_layout_alg]
  | _ = use_enum_layout_alg' ?els =>
      erewrite (simplify_use_enum_layout_alg' els) in H_ly;
      [ | solve_layout_alg]
  | _ = use_union_layout_alg' ?uls =>
      erewrite (simplify_use_union_layout_alg' uls) in H_ly;
      [ | solve_layout_alg]
  | _ = ot_layout (use_op_alg' ?st) =>
      match st with
      | ty_syn_type ?ty =>
          is_var ty;
          erewrite (simplify_ot_layout_var st) in H_ly;
          [ | solve_layout_alg ]
      | _ =>
          erewrite (simplify_ot_layout (use_op_alg' st)) in H_ly;
          [ | solve_ot_eq ]
      end
  | _ => idtac
  end.
(** Simplify a layout [ly] in the goal. *)
Ltac simplify_layout_go ly :=
  let Hly := fresh in
  let ly_term := fresh in
  remember ly as ly_term eqn:Hly;
  simplify_layout' Hly;
  subst ly_term.
Ltac simplify_layout ly :=
  match ly with
  | ?ly => is_var ly
  | layout_of (?sl) => is_var sl
  | ul_layout ?ul => is_var ul
  | it_layout ?it => idtac
  | _ => simplify_layout_go ly
  end.

Ltac maybe_simplify_layout ly :=
  match ly with
  | use_layout_alg' _ => simplify_layout_go ly
  | use_struct_layout_alg' _ => simplify_layout_go ly
  | use_enum_layout_alg' _ => simplify_layout_go ly
  | use_union_layout_alg' _ => simplify_layout_go ly
  | ot_layout _ => simplify_layout_go ly
  end.
Ltac simplify_layout_assum_step :=
  match goal with
  | H: context[?ly] |- _ =>
      assert_is_not_cached H;
      match type of ly with
      | layout => maybe_simplify_layout ly
      end
  end.
Ltac simplify_layout_assum :=
  repeat simplify_layout_assum_step.

Ltac simplify_layout_in A :=
  match A with
  | context[use_layout_alg' ?st] => simplify_layout_go (use_layout_alg' st)
  | context[use_struct_layout_alg' ?st] => simplify_layout_go (use_struct_layout_alg' st)
  | context[use_enum_layout_alg' ?st] => simplify_layout_go (use_enum_layout_alg' st)
  | context[use_union_layout_alg' ?st] => simplify_layout_go (use_union_layout_alg' st)
  | context[ot_layout ?ot] => simplify_layout_go (ot_layout ot)
  end.
Ltac simplify_layout_goal_step :=
  match goal with
  (* If we are working on a Lithium goal, don't simplify in the continuation *)
  | |- envs_entails _ (?A _) =>
      simplify_layout_in A
  | |- envs_entails ?H _ =>
      simplify_layout_in H
  | |- ?H ∧ envs_entails _ _ =>
      simplify_layout_in H
  | |- ?H → envs_entails _ _ =>
      simplify_layout_in H
  | |- ?G => simplify_layout_in G
  end.
Ltac simplify_layout_goal :=
  repeat simplify_layout_goal_step.
Ltac simplify_layout_normalize :=
  repeat match goal with
  | |- ?G =>
      simplify_layout_in G
  end.


Ltac solve_layout_alg_from_assumption :=
  match goal with
  | |- use_layout_alg ?st = Some ?ly =>
    match goal with
    | H : use_layout_alg ?st2 = Some ly |- _ =>
        unify st st2; apply H
    | H : CACHED (use_layout_alg ?st2 = Some ly) |- _ =>
        unify st st2; apply H
    end 
  end.

(** Solve goals of the form [layout_wf ly]. *)
Section layout.
  Lemma layout_wf_unit :
    layout_wf unit_sl.
  Proof.
    rewrite /layout_wf/ly_align/ly_size/=.
    apply Z.divide_0_r.
  Qed.
  Lemma layout_wf_ptr :
    layout_wf void*.
  Proof.
    rewrite /layout_wf/ly_align/ly_size/=.
    rewrite /bytes_per_addr/bytes_per_addr_log/=.
    done.
  Qed.
  Lemma layout_wf_bool :
    layout_wf bool_layout.
  Proof.
    rewrite /layout_wf/ly_align/ly_size/=.
    done.
  Qed.
End layout.
Ltac layout_is_var ly :=
  match ly with
  | layout_of ?sl =>
      is_var sl 
  | ul_layout ?ul =>
      is_var ul 
  | _ => is_var ly 
  end.
Ltac solve_layout_wf :=
  unfold_no_enrich;
  match goal with
  | |- layout_wf ?ly =>
      simplify_layout ly
  end;
  match goal with
  | |- layout_wf ?ly =>
      layout_is_var ly;
      refine (use_layout_alg_wf _ _ _);
      [solve_layout_alg_from_assumption]
  | |- layout_wf (it_layout ?it) =>
      refine (int_type_layout_wf it)
  | |- layout_wf (mk_array_layout _ _) =>
      refine (array_layout_wf _ _ _);
      solve_layout_wf
  | |- layout_wf (layout_of unit_sl) =>
      notypeclasses refine layout_wf_unit
  | |- layout_wf void* =>
      notypeclasses refine layout_wf_ptr
  | |- layout_wf bool_layout =>
      notypeclasses refine layout_wf_bool
  | |- _ =>
      (* TODO *)
      try fast_done
  end.

(** Solve goals of the form [ly_align_in_bounds ly]. *)
Section layout.
  Lemma ly_align_unit :
    ly_align_in_bounds unit_sl.
  Proof.
    done.
  Qed.
  Lemma ly_align_ptr :
    ly_align_in_bounds void*.
  Proof.
    done.
  Qed.
  Lemma ly_align_bool :
    ly_align_in_bounds bool_layout.
  Proof.
    done.
  Qed.
  Lemma ly_align_int it :
    ly_align_in_bounds (it_layout it).
  Proof.
    destruct it; done.
  Qed.
End layout.


Ltac solve_ly_align_ib :=
  unfold_no_enrich;
  match goal with
  | |- ly_align_in_bounds ?ly =>
      simplify_layout ly
  end;
  match goal with
  | |- ly_align_in_bounds (layout_of unit_sl) =>
      notypeclasses refine (ly_align_unit)
  | |- ly_align_in_bounds void* =>
      notypeclasses refine (ly_align_ptr)
  | |- ly_align_in_bounds bool_layout =>
      notypeclasses refine (ly_align_bool)
  | |- ly_align_in_bounds (it_layout _) =>
      notypeclasses refine (ly_align_int)
  | |- ly_align_in_bounds ?ly =>
      layout_is_var ly;
      refine (use_layout_alg_align _ _ _);
      [solve_layout_alg_from_assumption]
  | |- _ => idtac
  end;
  try first [eassumption | fast_done ].

(** Solve equalities and inequalities involving [ly_size]. *)
Ltac solve_layout_size :=
  unfold_no_enrich;

  first [
    match goal with 
    | |- (Z.of_nat (ly_size ?ly) ≤ MaxInt ISize)%Z =>
      layout_is_var ly;
      refine (use_layout_alg_size _ _ _);
      [solve_layout_alg_from_assumption]
    end
  |

  (* unfold [size_of_st] in the context *)
  repeat match goal with
  | H : context[size_of_st ?st] |- _ =>
      rewrite /size_of_st in H;
      simplify_layout (use_layout_alg' st)
  end;
  (* unfold [size_of_st] in the goal *)
  rewrite /size_of_st;
  (* simplify layouts by abstracting them into variables *)
  repeat match goal with
         | |- context[ly_size ?ly] =>
              assert_fails (is_var ly);
              let Hly := fresh in
              let ly_term := fresh in
              remember ly as ly_term eqn:Hly;
              simplify_layout' Hly
          end;
  (* substitute the equalities again as lia can't deal with that *)
  subst;
  try assumption;
  (* call into lia *)
  try (simpl; lia)
  ]
.

Global Arguments ly_size : simpl nomatch.

(** Solve goals of the form [Forall2 syn_type_has_layout_multi_pred xs ?fields], by instantiating [?fields]. *)
(* Definition below. *)
Ltac solve_layout_alg_forall :=
  idtac.

(** Solve goals of the form [ly1 = ly2]. *)
Ltac solve_layout_eq :=
  unfold_no_enrich;
  (* simplify both sides *)
  match goal with
  | |- ?ly1 = ?ly2 =>
      simplify_layout ly1;
      simplify_layout ly2
  end;
  (* TODO *)
  try reflexivity.

Ltac solve_layout_alg_prepare :=
  try match goal with
  | |- syn_type_has_layout ?st ?ly =>
      simplify_layout ly
  end;
  unfold_no_enrich;
  (* normalize goal *)
  lazymatch goal with
  | |- use_layout_alg ?st = Some ?ly => refine (use_layout_alg_layout_tac st ly _)
  | |- use_layout_alg' ?st = ?ly => refine (use_layout_alg'_layout_tac st ly _)
  | |- syn_type_has_layout ?st ?ly => idtac
  (* structs *)
  | |- use_struct_layout_alg ?sls = ?Some ?sl => refine (use_struct_layout_alg_layout_tac _ _ _)
  | |- struct_layout_spec_has_layout ?sls ?sl => idtac
  (* enums *)
  | |- use_enum_layout_alg ?els = ?Some ?el => refine (use_enum_layout_alg_layout_tac _ _ _)
  | |- enum_layout_spec_has_layout ?els ?el => idtac
  (* unions *)
  | |- use_union_layout_alg ?uls = ?Some ?ul => refine (use_union_layout_alg_layout_tac _ _ _)
  | |- union_layout_spec_has_layout ?uls ?ul => idtac
  end.

Ltac solve_layout_alg_core_step1 :=
  (* For primitive goals for which we have an assumption in the context *)
  try eassumption.
Ltac solve_layout_alg_core_step2 :=
  (* Simplify *)
  try match goal with
  | |- syn_type_has_layout ?st ?ly =>
      let st_eval := eval hnf in st in
      change_no_check st with st_eval
  | |- Forall2 syn_type_has_layout_multi_pred ?fields ?fields' =>
      let fields_eval := eval hnf in fields in
      change_no_check fields with fields_eval
  end.
Ltac fast_solve_layout_eq :=
  try notypeclasses refine eq_refl;
  shelve.
  (*solve_layout_eq.*)
Ltac solve_layout_alg_core_step3 :=
  (* match on st *)
  lazymatch goal with
  | |- Forall2 syn_type_has_layout_multi_pred [] ?fields' =>
      econstructor
  | |- Forall2 syn_type_has_layout_multi_pred (?f :: ?fields) ?fields' =>
    econstructor;
    [ eexists _, _; split_and!; [ | refine eq_refl | refine eq_refl] | ]
  | |- syn_type_has_layout (IntSynType ?it) ?ly =>
      notypeclasses refine (syn_type_has_layout_int _ _ _);
      [ fast_solve_layout_eq ]
  | |- syn_type_has_layout BoolSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_bool _ _);
      [fast_solve_layout_eq ]
  | |- syn_type_has_layout CharSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_char _ _);
      [fast_solve_layout_eq ]
  | |- syn_type_has_layout PtrSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_ptr _ _);
      [fast_solve_layout_eq ]
  | |- syn_type_has_layout FnPtrSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_fnptr _ _);
      [fast_solve_layout_eq ]
  | |- syn_type_has_layout (StructSynType ?name ?fields ?repr) ?ly =>
      notypeclasses refine (syn_type_has_layout_struct_tac name fields _ repr _ _  _ _ _);
      [| | fast_solve_layout_eq]
  | |- struct_layout_spec_has_layout ?sls ?sl =>
      notypeclasses refine (struct_layout_spec_has_layout_tac sls _ sl _ _ _ _);
      [| | fast_solve_layout_eq]
  | |- syn_type_has_layout UnitSynType ?ly =>
      notypeclasses refine (syn_type_has_layout_unit _ _);
      [fast_solve_layout_eq ]
  | |- syn_type_has_layout (ArraySynType ?st ?len) ?ly =>
      notypeclasses refine (syn_type_has_layout_array st len _ ly _ _ _);
      [ fast_solve_layout_eq | | solve_layout_size; shelve ]
  | |- syn_type_has_layout (UnsafeCell ?st) ?ly =>
      notypeclasses refine (syn_type_has_layout_unsafecell st ly _);
      []
  | |- syn_type_has_layout (UntypedSynType ?ly) ?ly' =>
      lazymatch ly with
      | use_layout_alg' ?st' =>
          notypeclasses refine (syn_type_has_layout_untyped_alg_tac st' _ ly' _ _);
            [fast_solve_layout_eq | ]
      | use_struct_layout_alg' ?sls' =>
          notypeclasses refine (syn_type_has_layout_untyped_struct_alg_tac sls' _ ly' _ _);
            [fast_solve_layout_eq | ]
      | use_enum_layout_alg' ?sls' =>
          notypeclasses refine (syn_type_has_layout_untyped_enum_alg_tac sls' _ ly' _ _);
            [fast_solve_layout_eq | ]
      | void* =>
          notypeclasses refine (syn_type_has_layout_untyped_ptr_tac _ _);
          fast_solve_layout_eq
      | layout_of unit_sl =>
          notypeclasses refine (syn_type_has_layout_untyped_unit_tac _ _);
          fast_solve_layout_eq
      | it_layout _ =>
          notypeclasses refine (syn_type_has_layout_untyped_int_tac _ _ _);
          fast_solve_layout_eq
      | _ =>
          notypeclasses refine (syn_type_has_layout_untyped ly ly' _ _ _ _);
            [fast_solve_layout_eq
            | solve_layout_wf; shelve
            | solve_layout_size; shelve
            | solve_ly_align_ib; shelve ]
      end
  | |- syn_type_has_layout (EnumSynType ?name ?it ?variants ?repr) ?ly =>
      notypeclasses refine (syn_type_has_layout_enum_tac name variants _ it _ _ _ _ _ _ _ _ _ _ _ _ );
      [| refine eq_refl | refine eq_refl | | | fast_solve_layout_eq]
  | |- enum_layout_spec_has_layout ?els ?el =>
      notypeclasses refine (enum_layout_spec_has_layout_tac els _ _ _ _ _ _ _ _ _ _ _ _ );
      [| refine eq_refl | refine eq_refl | | | fast_solve_layout_eq]
  | |- syn_type_has_layout (UnionSynType ?name ?variants ?repr) ?ly =>
      notypeclasses refine (syn_type_has_layout_union_tac name variants _ _ _ _ _ _ _ );
      [| | fast_solve_layout_eq]
  | |- union_layout_spec_has_layout ?uls ?ul =>
      notypeclasses refine (union_layout_spec_has_layout_tac uls _ _ _ _ _ _);
      [| | fast_solve_layout_eq]
  end.

Ltac solve_layout_alg_core_step :=
  solve_layout_alg_core_step1;
  solve_layout_alg_core_step2;
  solve_layout_alg_core_step3.

Ltac solve_layout_alg_core :=
  repeat solve_layout_alg_core_step.
Ltac solve_layout_alg ::=
  solve_layout_alg_prepare;
  solve[solve_layout_alg_core].

Ltac solve_layout_alg_forall ::=
  unfold_no_enrich;
  simpl;
  solve_layout_alg_core
  .

Ltac solve_compute_layout ::=
  unfold_no_enrich;
  open_scache;
  first [eassumption | 
  simplify_layout_goal;
  first [eassumption | progress solve_layout_alg; shelve]].

Ltac solve_compute_struct_layout ::=
  unfold_no_enrich;
  open_scache;
  first [eassumption |
  simplify_layout_goal;
  first [eassumption | progress solve_layout_alg; shelve]].

Ltac solve_compute_enum_layout ::=
  unfold_no_enrich;
  open_scache;
  first [eassumption | 
  simplify_layout_goal;
  first [eassumption | progress solve_layout_alg; shelve]].

(** syn_type_compat solver *)
Section syntype_compat.
  Context `{!LayoutAlg}.
  Lemma syn_type_compat_refl st :
    syn_type_compat st st.
  Proof. left. done. Qed.

  Lemma syn_type_compat_untyped_r st ly ly' :
    syn_type_has_layout st ly' →
    ly = ly' →
    syn_type_compat st (UntypedSynType ly).
  Proof. intros ? ->. right. eauto. Qed.
End syntype_compat.
Global Arguments syn_type_compat : simpl never.

Ltac solve_syn_type_compat :=
  unfold_no_enrich;
  lazymatch goal with
  | |- syn_type_compat ?st ?st =>
      refine (syn_type_compat_refl _)
  | |- syn_type_compat ?st1 (UntypedSynType ?ly2) =>
      refine (syn_type_compat_untyped_r _ _ _ _ _);
      [solve_layout_alg | solve_layout_eq ]
  end.


(** ** Op-alg solver *)

Section opalg.
  Context `{!typeGS Σ}.

  Lemma use_op_alg'_ot_tac st ot :
    use_op_alg st = Some ot → use_op_alg' st = ot.
  Proof. rewrite /use_op_alg' => -> //. Qed.

  (* Use for tyvars *)
  Lemma use_op_alg_tyvar_tac st ly ot :
    syn_type_has_layout st ly →
    ot = use_op_alg' st →
    use_op_alg st = Some ot.
  Proof.
    intros Hly%syn_type_has_layout_op_alg ->.
    destruct Hly as (ot & Hot & <-).
    rewrite /use_op_alg' Hot //.
  Qed.

  Lemma simplify_use_op_alg' T_st T_ly :
    use_op_alg T_st = Some T_ly →
    use_op_alg' T_st = T_ly.
  Proof.
    rewrite /use_op_alg' => -> //.
  Qed.
End opalg.

Ltac solve_op_alg := idtac.

(* We assume a let-binding [H_ly] has been introduced into the context in which we can rewrite *)
Ltac simplify_optype' H_ly :=
  repeat match type of H_ly with
  | _ = use_op_alg' ?st =>
      erewrite (simplify_use_op_alg' st) in H_ly;
      [ | solve_op_alg]
  | _ => idtac
  end.
(** Simplify a layout [ly] in the goal. *)
Ltac simplify_optype_go ly :=
  let Hly := fresh in
  let ly_term := fresh in
  remember ly as ly_term eqn:Hly;
  simplify_optype' Hly;
  subst ly_term.
Ltac simplify_optype ly :=
  match ly with
  | ?ly => is_var ly
  | _ => simplify_optype_go ly
  end.

(** Solve goals of the form [ot1 = ot2]. *)
Ltac solve_ot_eq ::=
  unfold_no_enrich;
  (* simplify both sides *)
  try match goal with
  | |- ?ot1 = ?ot2 =>
      assert_fails (is_evar ot1);
      assert_fails (is_evar ot2);
      simplify_optype ot1;
      simplify_optype ot2
  end;
  (* TODO? *)
  try reflexivity.

(** Solve goals of the form [Forall2 _ xs ?fields], by instantiating [?fields]. *)
Ltac assert_is_atomic_st st :=
  first [is_var st | match st with | ty_syn_type ?T => is_var T end].
Ltac assert_is_atomic_sls sls :=
  is_var sls.
Ltac assert_is_atomic_els els :=
  is_var els.
Ltac assert_is_atomic_uls uls :=
  is_var uls.

(* Definition below. *)
Ltac solve_op_alg_forall :=
  idtac.

Ltac solve_op_alg_prepare :=
  (* normalize goal *)
  lazymatch goal with
  | |- use_op_alg ?st = Some ?ot => idtac
  | |- use_op_alg' ?st = ?ot => refine (use_op_alg'_ot_tac st ot _)
  end.

Ltac solve_op_alg_core_step :=
  (* TODO: needed? *)
  try eassumption;
  (* Revert to deriving it from layout algorithms for atomics *)
  try lazymatch goal with
    | |- use_op_alg ?st = Some ?ot =>
      assert_is_atomic_st st;
      refine (use_op_alg_tyvar_tac st _ _ _ _);
      [solve_layout_alg | solve_ot_eq]
  end;
  (* Unfold *)
  try lazymatch goal with
  | |- Forall2 use_op_alg_struct_pred ?fields ?fields' =>
      let fields_eval := eval hnf in fields in
      change_no_check fields with fields_eval
  | |- use_op_alg ?st = Some ?op =>
      let st_eval := eval hnf in st in
      change_no_check st with st_eval
  end;
  (* match on st *)
  lazymatch goal with
  | |- Forall2 use_op_alg_struct_pred [] ?fields' =>
      econstructor
  | |- Forall2 use_op_alg_struct_pred (?f :: ?fields) ?fields' =>
    econstructor; [ unfold use_op_alg_struct_pred | ]
  | |- use_op_alg (IntSynType ?it) = Some ?ot =>
      notypeclasses refine (use_op_alg_int _ _ _);
      [ solve_ot_eq ]
  | |- use_op_alg BoolSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_bool _ _);
      [solve_ot_eq ]
  | |- use_op_alg CharSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_char _ _);
      [solve_ot_eq ]
  | |- use_op_alg PtrSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_ptr _ _);
      [solve_ot_eq ]
  | |- use_op_alg FnPtrSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_fnptr _ _);
      [solve_ot_eq ]
  | |- use_op_alg (StructSynType ?name ?fields ?repr) = Some ?ot =>
      notypeclasses refine (use_op_alg_struct name fields _ _ _ _  _ _ _);
      [ | solve_layout_alg | solve_ot_eq ]
  | |- use_op_alg UnitSynType = Some ?ot =>
      notypeclasses refine (use_op_alg_unit _ _);
      [solve_ot_eq ]
  | |- use_op_alg (ArraySynType ?st ?len) = Some ?ot =>
      fail 1000 "implement solve_op_alg for ArraySynType"
  | |- use_op_alg (UnsafeCell ?st) = Some ?ot =>
      notypeclasses refine (use_op_alg_unsafecell st _ _);
      [ ]
  | |- use_op_alg (UntypedSynType ?ly) = Some ?ot =>
      simplify_layout ly;
      notypeclasses refine (use_op_alg_untyped _ ot _);
      [solve_ot_eq ]
  | |- use_op_alg (EnumSynType ?name ?it ?fields ?repr) = Some ?ot =>
      notypeclasses refine (use_op_alg_enum _ _ _ _ _ _ _ _);
      [solve_layout_alg | solve_ot_eq]
  | |- use_op_alg (UnionSynType ?name ?fields ?repr) = Some ?ot =>
      notypeclasses refine (use_op_alg_union _ _ _ _ _ _ _);
      [solve_layout_alg | solve_ot_eq]
  | |- use_op_alg (ty_syn_type _) = Some ?ot =>
      notypeclasses refine (use_op_alg_tyvar_tac (ty_syn_type _) _ ot _ _);
      [solve_layout_alg | solve_ot_eq]
  | |- use_op_alg ?st = Some ?ot =>
      is_var st;
      notypeclasses refine (use_op_alg_tyvar_tac st _ ot _ _);
      [solve_layout_alg | solve_ot_eq]
  end.

Ltac solve_op_alg_core :=
  repeat solve_op_alg_core_step.
Ltac solve_op_alg ::=
  solve_op_alg_prepare;
  solve_op_alg_core.

Ltac solve_op_alg_forall ::=
  simpl;
  lazymatch goal with
  | |- Forall2 use_op_alg_struct_pred [] ?fields' =>
      econstructor
  | |- Forall2 use_op_alg_struct_pred (?f :: ?fields) ?fields' =>
    econstructor;
    [ simpl; solve_op_alg_core
    | solve_op_alg_forall]
  end.




(** * Tactics for inverting layout assumptions *)
Global Arguments use_layout_alg : simpl never.

(** Check for already solved cached results for layout alg applications *)
Section remove_duplicates.
  Context `{!LayoutAlg}.
  Lemma enter_cache_resolve_layout_alg_dup st ly1 ly2 :
    use_layout_alg st = Some ly1 →
    CACHED (use_layout_alg st = Some ly2) →
    ly1 = ly2.
  Proof.
    intros. unfold CACHED in *. by eapply syn_type_has_layout_inj.
  Qed.

  Lemma enter_cache_resolve_struct_layout_alg_dup sls ly1 ly2 :
    use_struct_layout_alg sls = Some ly1 →
    CACHED (use_struct_layout_alg sls = Some ly2) →
    ly1 = ly2.
  Proof.
    intros H1 H2. unfold CACHED in *.
    rewrite H1 in H2. naive_solver.
  Qed.
  Lemma enter_cache_resolve_enum_layout_alg_dup els ly1 ly2 :
    use_enum_layout_alg els = Some ly1 →
    CACHED (use_enum_layout_alg els = Some ly2) →
    ly1 = ly2.
  Proof.
    intros H1 H2. unfold CACHED in *.
    rewrite H1 in H2. naive_solver.
  Qed.
  Lemma enter_cache_resolve_union_layout_alg_dup uls ly1 ly2 :
    use_union_layout_alg uls = Some ly1 →
    CACHED (use_union_layout_alg uls = Some ly2) →
    ly1 = ly2.
  Proof.
    intros H1 H2. unfold CACHED in *.
    rewrite H1 in H2. naive_solver.
  Qed.
End remove_duplicates.

Ltac check_for_cached_layout H :=
  lazymatch type of H with
    | use_layout_alg ?st = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_layout_alg st = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
    | use_struct_layout_alg ?sls = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_struct_layout_alg sls = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_struct_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
    | use_enum_layout_alg ?els = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_enum_layout_alg els = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_enum_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
    | use_union_layout_alg ?uls = Some ?ly1 =>
        lazymatch goal with
        | H2: CACHED (use_union_layout_alg uls = Some ?ly2) |- _ =>
          let Heq := fresh "Heq" in
          specialize (enter_cache_resolve_union_layout_alg_dup _ _ _ H H2) as Heq;
          subst_with Heq;
          clear H
        end
  end.

Ltac simplify_layout_alg := fail "impl simplify_layout_alg".
Ltac inv_multi_fields_rec Hrec :=
  simpl in Hrec;
  match type of Hrec with
  | Forall2 _ (?x :: ?L1) (?L2) =>
      let Harg := fresh in
      let Hrec2 := fresh "Hrec" in
      let Heq := fresh "Heq" in
      let Hnameeq := fresh "Heq" in
      apply Forall2_cons_inv_l in Hrec as ([] & ? & [Hnameeq Harg] & Hrec2 & Heq);
      subst_with Hnameeq;
      subst_with Heq;
      inv_multi_fields_rec Hrec2;
      simplify_layout_alg Harg
  | Forall2 _ [] _ =>
      apply Forall2_nil_inv_l in Hrec as ->
  end.
Ltac inv_multi_fields Hrec :=
  simpl in Hrec; inv_multi_fields_rec Hrec.


From iris.proofmode Require Import string_ident.
Ltac rename_layouts_core H cont :=
  lazymatch type of H with
  | struct_layout_alg ?name ?fields ?repr = Some ?sl =>
      let Hfields := fresh in
      apply struct_layout_alg_has_fields in H as Hfields;
      clear Hfields;
      (*enter_jcache Hfields;*)

      let sl_name := eval cbv in (append name "_sl") in
      let fields_name := eval cbv in (append name "_fields") in
      let H_name := eval cbv in (append name "_salg") in
      string_to_ident_cps sl_name ltac:(fun sl_n =>
      string_to_ident_cps fields_name ltac:(fun fields_n =>
      string_to_ident_cps H_name ltac:(fun H_n =>
      try rename sl into sl_n;
      try rename Hfields into fields_N;
      first [rename H into H_n; cont H_n | cont H]
      )))
  | union_layout_alg ?name ?variants ?repr = Some ?ul =>
      let Hvariants := fresh in
      apply union_layout_alg_has_variants in H as Hvariants;
      clear Hvariants;
      (*enter_jcache Hvariants;*)

      let ul_name := eval cbv in (append name "_ul") in
      let variants_name := eval cbv in (append name "_variants") in
      let H_name := eval cbv in (append name "_ualg") in
      string_to_ident_cps ul_name ltac:(fun ul_n =>
      string_to_ident_cps variants_name ltac:(fun variants_n =>
      string_to_ident_cps H_name ltac:(fun H_n =>
      try rename ul into ul_n;
      try rename Hvariants into variants_n;
      first [rename H into H_n; cont H_n | cont H]
      )))
  | use_layout_alg ?T = Some ?ly =>
      assert_is_atomic_st T;
      is_var ly;
      first [
        is_var T;
        let st_name := constr:(ident_to_string! T) in
        let ly_name := eval cbv in (append st_name "_ly") in
        let H_name := eval cbv in (append st_name "_alg") in
        string_to_ident_cps ly_name ltac:(fun ly_n =>
        string_to_ident_cps H_name ltac:(fun H_n =>
        try rename ly into ly_n;
        rename H into H_n; cont H_n))
      | cont H]
  end.
Tactic Notation "rename_layouts" "in" hyp(H) "with" tactic(cont) :=
  rename_layouts_core H cont.
Tactic Notation "rename_layouts" "in" hyp(H) :=
  rename_layouts in H with (fun x => idtac).

Ltac is_duplicate H :=
  match type of H with
  | use_layout_alg ?st = Some _ =>
      match goal with
      | H2 : NO_ENRICH (use_layout_alg st = Some _) |- _ =>
          idtac
      end
  | struct_layout_alg ?name ?fields ?repr = Some _ =>
      match goal with
      | H2 : NO_ENRICH (struct_layout_alg name fields repr = Some _) |- _ =>
          idtac
      end
  | union_layout_alg ?name ?variants ?repr = Some _ =>
      match goal with
      | H2 : NO_ENRICH (union_layout_alg name variants repr = Some _) |- _ =>
          idtac
      end
  end.

Section handle_duplicate.
  Context `{!LayoutAlg}.

  Lemma handle_duplicate_use_layout_alg_tac st ly0 ly1 :
    use_layout_alg st = Some ly0 →
    CACHED (use_layout_alg st = Some ly1) →
    ly0 = ly1.
  Proof.
    rewrite /CACHED.
    intros ??. by eapply syn_type_has_layout_inj.
  Qed.

  Lemma handle_duplicate_struct_layout_alg_tac name fields repr sl0 sl1 :
    struct_layout_alg name fields repr = Some sl0 →
    CACHED (struct_layout_alg name fields repr = Some sl1) →
    sl0 = sl1.
  Proof.
    rewrite /CACHED.
    intros ??. by simplify_eq.
  Qed.

  Lemma handle_duplicate_union_layout_alg_tac name variants repr ul0 ul1 :
    union_layout_alg name variants repr = Some ul0 →
    CACHED (union_layout_alg name variants repr = Some ul1) →
    ul0 = ul1.
  Proof.
    rewrite /CACHED.
    intros ??. by simplify_eq.
  Qed.

End handle_duplicate.

Ltac postprocess_new_struct_assum H Halg :=
  lazymatch type of Halg with
  | struct_layout_alg ?name ?field_lys ?repr = Some _ =>
    first [
      (* if this is a duplicate, remove it *)
      lazymatch goal with
      | H2 : CACHED (struct_layout_alg name field_lys repr = Some _) |- _ =>
        let Heq := fresh "_Heq" in
        specialize (handle_duplicate_struct_layout_alg_tac _ _ _ _ _ Halg H2) as Heq;
        subst_with Heq;
        clear Halg
      end
    |
      (* derive some information from the original assumption *)
      (*lazymatch type of H with*)
      (*| use_layout_alg _ = Some _  =>*)
        (*specialize_cache (use_layout_alg_wf _ _ H);*)
        (*specialize_cache (use_layout_alg_size _  _ H);*)
        (*specialize_cache (use_layout_alg_align _  _ H)*)
      (*| use_struct_layout_alg _ = Some _ =>*)
        (*specialize_cache (use_struct_layout_alg_wf _ _ H);*)
        (*specialize_cache (use_struct_layout_alg_size _  _ H)*)
      (*| use_enum_layout_alg _ = Some _ =>*)
        (*specialize_cache (use_enum_layout_alg_wf _ _ H);*)
        (*specialize_cache (use_enum_layout_alg_size _  _ H)*)
      (*end;*)
      rename_layouts in Halg with (fun Halg => enter_cache_unsafe Halg)
    ]
  end.
Ltac postprocess_new_union_assum H Halg :=
  lazymatch type of Halg with
  | union_layout_alg ?name ?variant_lys ?repr = Some _ =>
    first [
      (* if this is a duplicate, remove it *)
      lazymatch goal with
      | H2 : CACHED (union_layout_alg name variant_lys repr = Some _) |- _ =>
        let Heq := fresh "_Heq" in
        specialize (handle_duplicate_union_layout_alg_tac _ _ _ _ _ Halg H2) as Heq;
        subst_with Heq;
        clear Halg
      end
    |
      (* derive some information from the original assumption *)
      (*lazymatch type of H with*)
      (*| use_layout_alg _ = Some _ =>*)
        (*specialize_cache (use_layout_alg_wf _ _ H);*)
        (*specialize_cache (use_layout_alg_size _  _ H);*)
        (*specialize_cache (use_layout_alg_align _  _ H)*)
      (*| use_union_layout_alg _ = Some _ =>*)
        (*specialize_cache (use_union_layout_alg_wf _ _ H);*)
        (*specialize_cache (use_union_layout_alg_size _ _ H)*)
      (*end;*)
      rename_layouts in Halg with (fun Halg => enter_cache_unsafe Halg)
    ]
  end.


Ltac simplify_layout_alg_prepare H :=
  simpl in H;
  try lazymatch type of H with
  | syn_type_has_layout ?spec ?ly =>
     change_no_check (use_layout_alg spec = Some ly) in H
  | struct_layout_spec_has_layout ?sls ?sl =>
      change_no_check (use_struct_layout_alg sls = Some sl) in H
  | union_layout_spec_has_layout ?uls ?ul =>
      change_no_check (use_union_layout_alg uls = Some ul) in H
  | enum_layout_spec_has_layout ?els ?el =>
      change_no_check (use_enum_layout_alg els = Some el) in H
  end;
  try lazymatch type of H with
  | use_layout_alg ?spec = Some _ =>
      unfold syn_type_of_sls, syn_type_of_els, syn_type_of_uls in H
  end.

Ltac simplify_layout_alg_simpl_step H :=
  (* simplify head *)
  try lazymatch type of H with
  | use_layout_alg ?spec = Some _ =>
      first [assert_is_atomic_st spec
      | let spec_eval := eval hnf in spec in
        change_no_check spec with spec_eval in H ]
  | use_struct_layout_alg ?spec = Some _ =>
      let spec_eval := eval hnf in spec in
      change_no_check spec with spec_eval in H
      (*is_var spec; rewrite /spec in H*)
  | use_union_layout_alg ?spec = Some _ =>
      let spec_eval := eval hnf in spec in
      change_no_check spec with spec_eval in H
  | use_enum_layout_alg ?spec = Some _ =>
      let spec_eval := eval hnf in spec in
      change_no_check spec with spec_eval in H
  end.

Ltac simplify_layout_alg_atomic H :=
  (* Handle atomic alg applications *)
  lazymatch type of H with
  | use_layout_alg (ty_syn_type ?ty) = Some _ =>
      is_var ty;
      enter_cache H
  | use_layout_alg ?st = Some _ =>
      (*assert_is_atomic_st st;*)
      is_var st;
      specialize_cache (use_layout_alg_size _ _ H);
      specialize_cache (use_layout_alg_wf _ _ H);
      specialize_cache (use_layout_alg_align _ _ H);
      (* stop exploiting this further to prevent divergence *)
      rename_layouts in H with (fun H_n => enter_cache_unsafe H_n)
  end.

Ltac simplify_layout_alg_nonatomic H :=
    (* Handle non-atomic alg applications *)
    lazymatch type of H with
    | use_struct_layout_alg ?sls = Some _ =>
        first [
          (* don't do anything *)
          assert_is_atomic_sls sls;
          (*specialize_cache (use_struct_layout_alg_size _ _ H);*)
          (*specialize_cache (use_struct_layout_alg_wf _ _ H);*)
          rename_layouts in H with (fun H_n => enter_cache H_n)
        |
          let Hrec := fresh "_Hrec" in
          let Halg := fresh "_Halg" in
          specialize (use_struct_layout_alg_inv _ _ H) as (? & Halg & Hrec);
          simpl in Halg;
          inv_multi_fields Hrec;
          postprocess_new_struct_assum H Halg;
          enter_cache H
        ]

    | use_enum_layout_alg ?els = Some _ =>
        first [
          (* don't do anything *)
          assert_is_atomic_els els;
          (*specialize_cache (use_enum_layout_alg_size _ _ H);*)
          (*specialize_cache (use_enum_layout_alg_wf _ _ H);*)
          (* stop exploiting this further to prevent divergence *)
          rename_layouts in H with (fun H_n => enter_cache H_n)
        |
          let Hrec := fresh "_Hrec" in
          let Halg_ul := fresh "_Halg" in
          let Halg_sl := fresh "_Halg" in
          specialize (use_enum_layout_alg_inv _ _ H) as (? & ? & Halg_ul & Halg_sl & Hrec);
          simpl in Halg_ul, Halg_sl;
          inv_multi_fields Hrec;
          postprocess_new_union_assum H Halg_ul;
          postprocess_new_struct_assum H Halg_sl;
          enter_cache H
        ]

    | use_union_layout_alg ?uls = Some _ =>
        first [
          (* don't do anything *)
          assert_is_atomic_uls uls;
          (*specialize_cache (use_union_layout_alg_size _ _ H);*)
          (*specialize_cache (use_union_layout_alg_wf _ _ H);*)
          rename_layouts in H with (fun H_n => enter_cache H_n)
        |
          let Hrec := fresh "_Hrec" in
          let Halg_ul := fresh "_Halg" in
          specialize (use_union_layout_alg_inv _ _ H) as (? & Halg_ul & Hrec);
          simpl in Halg_ul;
          inv_multi_fields Hrec;
          postprocess_new_union_assum H Halg_ul;
          enter_cache H
        ]

    | use_layout_alg (IntSynType ?it) = Some _ =>
        apply syn_type_has_layout_int_inv in H;
        subst_with H
    | use_layout_alg (BoolSynType) = Some _ =>
        apply syn_type_has_layout_bool_inv in H;
        subst_with H
    | use_layout_alg (CharSynType) = Some _ =>
        apply syn_type_has_layout_char_inv in H;
        subst_with H
    | use_layout_alg PtrSynType = Some _ =>
        apply syn_type_has_layout_ptr_inv in H;
        subst_with H
    | use_layout_alg FnPtrSynType = Some _ =>
        apply syn_type_has_layout_fnptr_inv in H;
        subst_with H

    | use_layout_alg (StructSynType _ ?fields ?repr) = Some _ =>
        let Hrec := fresh "_Hrec" in
        let Halg := fresh "_Halg" in
        let Heq := fresh "_Heq" in
        specialize (syn_type_has_layout_struct_inv _ _ _ _ H) as (? & ? & Heq & Halg & Hrec);
        simpl in Halg;
        inv_multi_fields Hrec;
        subst_with Heq;

        postprocess_new_struct_assum H Halg;
        enter_cache H

    | use_layout_alg UnitSynType = Some _ =>
        apply syn_type_has_layout_unit_inv in H;
        subst_with H

    | use_layout_alg (ArraySynType ?st ?len) = Some _ =>
        let ly' := fresh "ly" in let H' := fresh "H" in
        let Heq := fresh "_Heq" in
        let Hsz := fresh "_Hsz" in
        apply syn_type_has_layout_array_inv in H as (ly' & H' & Heq & Hsz);
        subst_with Heq;
        enter_jcache Hsz;
        simplify_layout_alg H'

    | use_layout_alg (UnsafeCell ?st) = Some _ =>
        apply syn_type_has_layout_unsafecell in H;
        simplify_layout_alg H

    | use_layout_alg (UntypedSynType ?ly) = Some _ =>
        let Heq := fresh "_Heq" in
        let Hwf := fresh "_Hwf" in
        let Hsz := fresh "_Hsz" in
        let Hib := fresh "_Hib" in
        apply syn_type_has_layout_untyped_inv in H as (Heq & Hwf & Hsz & Hib);
        subst_with Heq;
        enter_cache Hwf;
        enter_cache Hsz;
        enter_cache Hib 

    | use_layout_alg (EnumSynType _ ?it ?variants ?repr) = Some ?ly =>
        let Hrec := fresh "_Hrec" in
        let Halg_ul := fresh "_Halg" in
        let Halg_sl := fresh "_Halg" in
        let Heq := fresh "_Heq" in
        specialize (syn_type_has_layout_enum_inv _ _ _ _ _ H) as (? & ? & ? & Halg_ul & Halg_sl & Heq & Hrec);
        simpl in Halg_ul, Halg_sl;
        inv_multi_fields Hrec;
        subst_with Heq;
        postprocess_new_union_assum H Halg_ul;
        postprocess_new_struct_assum H Halg_sl;
        enter_cache H

    | use_layout_alg (UnionSynType _ ?variants ?repr) = Some _ =>
        let Hrec := fresh "_Hrec" in
        let Halg_ul := fresh "_Halg" in
        let Heq := fresh "_Heq" in
        specialize (syn_type_has_layout_union_inv _ _ _ _ H) as (? & ? & Heq & Halg_ul & Hrec);
        simpl in Halg_ul;
        inv_multi_fields Hrec;
        subst_with Heq;
        postprocess_new_union_assum H Halg_ul;
        enter_cache H
    | use_layout_alg ?st = Some _ =>
        fail 1000 "Unimplemented case in simplify_layout_alg"
    end.

Ltac simplify_layout_alg H ::=
  simplify_layout_alg_prepare H;
  simplify_layout_alg_simpl_step H;
  first
  [ (* Check for cached applications *)
    check_for_cached_layout H
  | simplify_layout_alg_atomic H
  | simplify_layout_alg_nonatomic H
  ].

(* TODO: we currently need this because we introduce syn_type equalities on generic args in preconditions of functions and not before, so we may get duplicates.
  Once this is fixed, we can remove this hack *)
Section remove_duplicates.
  Lemma remove_generic_layout_duplicate `{!typeGS Σ} {T_rt} (T_ty : type T_rt) ly1 ly2 :
    CACHED (use_layout_alg (ty_syn_type T_ty) = Some ly1) →
    CACHED (use_layout_alg (ty_syn_type T_ty) = Some ly2) →
    ly2 = ly1.
  Proof.
    intros Ha Hb. by eapply syn_type_has_layout_inj.
  Qed.
End remove_duplicates.

Ltac remove_duplicate_layout_assumptions :=
  repeat match goal with
  | H : CACHED (use_layout_alg (ty_syn_type ?T_ty) = Some ?Hly1),
      H2 : CACHED (use_layout_alg (ty_syn_type ?T_ty) = Some ?Hly2) |- _ =>
    is_var Hly1;
    is_var Hly2;
    is_var T_ty;
    let Heq := fresh "_Heq" in
    specialize (remove_generic_layout_duplicate _ _ _ H H2) as Heq;
    subst_with Heq;
    clear H2
  end.

Ltac inv_layout_alg_in H :=
  try lazymatch type of H with
  | syn_type_has_layout ?st ?ly =>
      change_no_check (use_layout_alg st = Some ly) in H
  | struct_layout_spec_has_layout ?sls ?sl =>
      change_no_check (use_struct_layout_alg sls = Some sl) in H
  | enum_layout_spec_has_layout ?els ?el =>
      change_no_check (use_enum_layout_alg els = Some el) in H
  | union_layout_spec_has_layout ?uls ?ul =>
      change_no_check (use_union_layout_alg uls = Some ul) in H
  end;
  lazymatch type of H with
  | use_layout_alg _ = Some _ =>
      simplify_layout_alg H
  | use_struct_layout_alg _ = Some _ =>
      simplify_layout_alg H
  | use_enum_layout_alg _ = Some _ =>
      simplify_layout_alg H
  | use_union_layout_alg _ = Some _ =>
      simplify_layout_alg H
  end.

Ltac inv_layout_alg :=
  repeat match goal with
  | H : syn_type_has_layout ?st ?ly |- _ =>
      change_no_check (use_layout_alg st = Some ly) in H
  | H : syn_type_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : use_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  (* struct *)
  | H : struct_layout_spec_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : struct_layout_spec_has_layout ?sls ?sl |- _ =>
      change_no_check (use_struct_layout_alg sls = Some sl) in H
  | H : use_struct_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  (* enum *)
  | H : enum_layout_spec_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : enum_layout_spec_has_layout ?els ?el |- _ =>
      change_no_check (use_enum_layout_alg els = Some el) in H
  | H : use_enum_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  (* union *)
  | H : union_layout_spec_is_layoutable _ |- _ =>
      let st := fresh "_st" in
      destruct H as [st H]
  | H : union_layout_spec_has_layout ?uls ?ul |- _ =>
      change_no_check (use_union_layout_alg uls = Some ul) in H
  | H : use_union_layout_alg _ = Some _ |- _ =>
      progress (simplify_layout_alg H)
  end;
  remove_duplicate_layout_assumptions.

Global Arguments syn_type_has_layout : simpl never.
