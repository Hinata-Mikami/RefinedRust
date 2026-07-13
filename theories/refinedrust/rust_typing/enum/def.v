From refinedrust Require Export type.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import struct.def struct.subtype.
From refinedrust Require Import options.

(** * Enums *)
Section enum_computed_lfts.
  Context `{!typeGS Σ}.

  Definition enum_tag_ty_lfts {rt} (tag_tys : list (var_name * enum_tag_sem rt)) : list lft :=
    fold_right (λ tag_ty acc, ty_lfts tag_ty.2.(enum_tag_sem_ty) ++ acc) [] tag_tys.

  Definition enum_tag_ty_wf_E {rt} (tag_tys : list (var_name * enum_tag_sem rt)) : elctx :=
    fold_right (λ tag_ty acc, ty_wf_E tag_ty.2.(enum_tag_sem_ty) ++ acc) [] tag_tys.

  Lemma enum_tag_ty_find_elem {rt} (tag_tys : list (var_name * enum_tag_sem rt)) tag sem :
    enum_tag_ty_find tag_tys tag = Some sem →
    (tag, sem) ∈ tag_tys.
  Proof.
    rewrite /enum_tag_ty_find.
    intros ([i [tag' sem']] & Hfind & Heq)%fmap_Some. simpl in Heq. subst sem'.
    apply list_find_Some in Hfind as (Hlook & Htag & _). simpl in Htag. subst tag'.
    by eapply list_elem_of_lookup_2.
  Qed.

  Lemma enum_tag_ty_lfts_elem {rt} (tag_tys : list (var_name * enum_tag_sem rt)) tag sem :
    (tag, sem) ∈ tag_tys →
    ty_lfts sem.(enum_tag_sem_ty) ⊆ enum_tag_ty_lfts tag_tys.
  Proof.
    induction tag_tys as [|[tag' sem'] tag_tys IH]; first set_solver.
    intros [Heq | Hin]%elem_of_cons; simpl.
    - simplify_eq/=. set_solver.
    - specialize (IH Hin). set_solver.
  Qed.

  Lemma enum_tag_ty_wf_E_elem {rt} (tag_tys : list (var_name * enum_tag_sem rt)) tag sem :
    (tag, sem) ∈ tag_tys →
    ty_wf_E sem.(enum_tag_sem_ty) ⊆ enum_tag_ty_wf_E tag_tys.
  Proof.
    induction tag_tys as [|[tag' sem'] tag_tys IH]; first set_solver.
    intros [Heq | Hin]%elem_of_cons; simpl.
    - simplify_eq/=. set_solver.
    - specialize (IH Hin). set_solver.
  Qed.

  Lemma enum_tag_ty_find_lfts {rt} (tag_tys : list (var_name * enum_tag_sem rt)) tag sem :
    enum_tag_ty_find tag_tys tag = Some sem →
    ty_lfts sem.(enum_tag_sem_ty) ⊆ enum_tag_ty_lfts tag_tys.
  Proof.
    intros Hfind. by eapply enum_tag_ty_lfts_elem, enum_tag_ty_find_elem.
  Qed.

  Lemma enum_tag_ty_find_wf_E {rt} (tag_tys : list (var_name * enum_tag_sem rt)) tag sem :
    enum_tag_ty_find tag_tys tag = Some sem →
    ty_wf_E sem.(enum_tag_sem_ty) ⊆ enum_tag_ty_wf_E tag_tys.
  Proof.
    intros Hfind. by eapply enum_tag_ty_wf_E_elem, enum_tag_ty_find_elem.
  Qed.

  Lemma enum_ty_lfts_incl_tag_ty_lfts {rt} (en : enum rt) r tag :
    enum_tag en r = Some tag →
    ty_lfts (enum_ty en r) ⊆ enum_tag_ty_lfts en.(enum_tag_ty).
  Proof.
    intros Htag.
    destruct (enum_tag_compat _ en r tag Htag) as [vinj Hfind].
    by eapply enum_tag_ty_find_lfts in Hfind.
  Qed.

  Lemma enum_ty_wf_E_incl_tag_ty_wf_E {rt} (en : enum rt) r tag :
    enum_tag en r = Some tag →
    ty_wf_E (enum_ty en r) ⊆ enum_tag_ty_wf_E en.(enum_tag_ty).
  Proof.
    intros Htag.
    destruct (enum_tag_compat _ en r tag Htag) as [vinj Hfind].
    by eapply enum_tag_ty_find_wf_E in Hfind.
  Qed.

  Record enum_tag_tys_lifecycle {rt} := mk_enum_tag_tys_lifecycle {
    enum_tag_tys_of_lifecycle : list (var_name * enum_tag_sem rt);
  }.
  Global Arguments mk_enum_tag_tys_lifecycle {_} _.
  Global Arguments enum_tag_tys_of_lifecycle {_} _.

  Global Instance lifecycle_enum_tag_tys {rt} : Lifecycle (enum_tag_tys_lifecycle (rt:=rt)) := {|
    lifecycle_lfts tag_tys := enum_tag_ty_lfts tag_tys.(enum_tag_tys_of_lifecycle);
    lifecycle_wf_E tag_tys := enum_tag_ty_wf_E tag_tys.(enum_tag_tys_of_lifecycle);
  |}.

  Class DepEnumTagTyLftMorphism {rts rt}
      (deps : gset nat)
      (F : mut_types rts → list (var_name * enum_tag_sem rt)) : Type := {
    dep_enum_tag_ty_lft_morphism_lft :
      DepLftMorphism deps (λ tys, mk_enum_tag_tys_lifecycle (F tys));
  }.

  Global Instance DepEnumTagTyLftMorphism_nil {rts rt} :
    DepEnumTagTyLftMorphism ∅ (λ _ : mut_types rts, @nil (var_name * enum_tag_sem rt)).
  Proof.
    constructor. apply _.
  Defined.

  Global Program Instance DepEnumTagTyLftMorphism_cons {rts rt rt'} depsG depsGs tag
      (G : mut_types rts → type rt')
      (inj : rt' → rt)
      (Gs : mut_types rts → list (var_name * enum_tag_sem rt)) :
    DepLftMorphism depsG G →
    DepEnumTagTyLftMorphism depsGs Gs →
    DepEnumTagTyLftMorphism (depsG ∪ depsGs)
      (λ tys, (tag, mk_enum_tag_sem rt' (G tys) inj) :: Gs tys) :=
    λ HG HGs,
      let HGs := dep_enum_tag_ty_lft_morphism_lft (DepEnumTagTyLftMorphism:=HGs) in
      {| dep_enum_tag_ty_lft_morphism_lft :=
          mk_dep_lft_morph
            (dep_lft_morph_α HG ⊓ dep_lft_morph_α HGs)
            (dep_lft_morph_E HG ++ dep_lft_morph_E HGs)
            (dep_lft_morph_βdeps HG ++ dep_lft_morph_βdeps HGs) _ _ |}.
  Next Obligation.
    iIntros (rts rt rt' depsG depsGs tag G inj Gs HG Htag_tys HGs tys).
    simpl. rewrite lft_intersect_list_app.
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
    intros rts rt rt' depsG depsGs tag G inj Gs HG Htag_tys HGs tys.
    simpl. rewrite !elctx_interp_app.
    rewrite (dep_lft_morph_wf_E HG tys) (dep_lft_morph_wf_E HGs tys).
    rewrite /dep_beta_interp big_sepL_app dep_wf_E_union.
    rewrite -!assoc.
    iSplit.
    - iIntros "(HE & HW & Hβ & HEs & HWs & Hβs)". iFrame.
    - iIntros "(HE & HEs & HW & HWs & Hβ & Hβs)". iFrame.
  Qed.
End enum_computed_lfts.

Section enum.
  Context `{!typeGS Σ}.

  Import EqNotations.

  Definition enum_tag_ty_has_op_types {rt} (tag_tys : list (var_name * enum_tag_sem rt))
      (variant_ots : list (var_name * op_type)) : Prop :=
    Forall2 (λ tag_ty variant_ot,
      tag_ty.1 = variant_ot.1 ∧ ty_has_op_type tag_ty.2.(enum_tag_sem_ty) variant_ot.2)
      tag_tys variant_ots.

  Definition enum_tag_ty_has_op_type_rel {rt}
      (tag_ty tag_ty' : var_name * enum_tag_sem rt) : Prop :=
    tag_ty.1 = tag_ty'.1 ∧
    ∀ ot, ty_has_op_type tag_ty.2.(enum_tag_sem_ty) ot ↔
      ty_has_op_type tag_ty'.2.(enum_tag_sem_ty) ot.

  Definition enum_tag_tys_has_op_type_rel {rt}
      (tag_tys tag_tys' : list (var_name * enum_tag_sem rt)) : Prop :=
    Forall2 enum_tag_ty_has_op_type_rel tag_tys tag_tys'.

  Lemma enum_tag_ty_has_op_types_transfer_forall2 {rt}
      (tag_tys tag_tys' : list (var_name * enum_tag_sem rt)) variant_ots :
    enum_tag_tys_has_op_type_rel tag_tys tag_tys' →
    enum_tag_ty_has_op_types tag_tys variant_ots →
    enum_tag_ty_has_op_types tag_tys' variant_ots.
  Proof.
    intros Hrel Hot.
    unfold enum_tag_tys_has_op_type_rel, enum_tag_ty_has_op_types in *.
    apply Forall2_same_length_lookup. split.
    { etrans; first symmetry; first by eapply Forall2_length.
      by eapply Forall2_length. }
    intros i [variant' sem'] [variant_ot variant_ot_ty] Hlookup' Hvariant_ot_lookup.
    destruct (Forall2_lookup_r _ _ _ _ _ Hrel Hlookup') as ([variant sem] & Hlookup & [Hvariant_eq Hcompat]).
    destruct (Forall2_lookup_l _ _ _ _ _ Hot Hlookup) as ([variant_ot' variant_ot_ty'] & Hvariant_ot_lookup' & [Hvariant_ot_eq Hot_payload]).
    simpl in Hvariant_eq, Hvariant_ot_eq. subst variant_ot'.
    rewrite Hvariant_ot_lookup in Hvariant_ot_lookup'. inversion Hvariant_ot_lookup'. subst variant_ot variant_ot_ty'.
    split; first done.
    by apply Hcompat.
  Qed.

  Lemma enum_tag_ty_find_lookup {rt} (tag_tys : list (var_name * enum_tag_sem rt)) i variant sem :
    NoDup tag_tys.*1 →
    tag_tys !! i = Some (variant, sem) →
    enum_tag_ty_find tag_tys variant = Some sem.
  Proof.
    intros Hnodup Hlookup.
    rewrite /enum_tag_ty_find.
    assert (list_find (λ x : var_name * enum_tag_sem rt, x.1 = variant) tag_tys = Some (i, (variant, sem))) as ->; last done.
    apply list_find_Some. split_and!; simpl; try done.
    intros j [variant' sem'] Hlookup' Hlt Hvariant'. simpl in Hvariant'. subst variant'.
    assert (tag_tys.*1 !! i = Some variant) as Hi.
    { by rewrite list_lookup_fmap Hlookup. }
    assert (tag_tys.*1 !! j = Some variant) as Hj.
    { by rewrite list_lookup_fmap Hlookup'. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hi Hj). lia.
  Qed.

  Lemma enum_tag_ty_has_op_types_transfer {rt}
      (tag_tys tag_tys' : list (var_name * enum_tag_sem rt)) variant_ots :
    tag_tys.*1 = tag_tys'.*1 →
    NoDup tag_tys.*1 →
    enum_tag_ty_has_op_types tag_tys variant_ots →
    (∀ variant sem sem' ot,
      enum_tag_ty_find tag_tys variant = Some sem →
      enum_tag_ty_find tag_tys' variant = Some sem' →
      ty_has_op_type sem.(enum_tag_sem_ty) ot ↔ ty_has_op_type sem'.(enum_tag_sem_ty) ot) →
    enum_tag_ty_has_op_types tag_tys' variant_ots.
  Proof.
    intros Hnames Hnodup Hot Hcompat.
    unfold enum_tag_ty_has_op_types in *.
    apply Forall2_same_length_lookup. split.
    { pose proof (Forall2_length _ _ _ Hot) as Hlen.
      rewrite -Hlen. rewrite -(length_fmap fst tag_tys') -Hnames length_fmap //. }
    intros i [variant' sem'] [variant_ot variant_ot_ty] Hlookup' Hvariant_ot_lookup.
    assert (∃ sem, tag_tys !! i = Some (variant', sem)) as (sem & Hlookup).
    { assert (tag_tys'.*1 !! i = Some variant') as Hname'.
      { by rewrite list_lookup_fmap Hlookup'. }
      rewrite -Hnames in Hname'.
      destruct (tag_tys !! i) as [[variant'' sem]|] eqn:Hlookup; rewrite list_lookup_fmap Hlookup in Hname'; simplify_eq/=.
      eauto. }
    destruct (Forall2_lookup_l _ _ _ _ _ Hot Hlookup) as ([variant_ot' variant_ot_ty'] & Hvariant_ot_lookup' & [Hvariant_eq Hot_payload]).
    simpl in Hvariant_eq. subst variant_ot'.
    rewrite Hvariant_ot_lookup in Hvariant_ot_lookup'. inversion Hvariant_ot_lookup'. subst variant_ot variant_ot_ty'.
    split; first done.
    assert (ty_has_op_type sem.(enum_tag_sem_ty) variant_ot_ty ↔ ty_has_op_type sem'.(enum_tag_sem_ty) variant_ot_ty) as Hiff.
    { eapply Hcompat.
      - by eapply enum_tag_ty_find_lookup.
      - eapply enum_tag_ty_find_lookup; last done. by rewrite -Hnames. }
    by apply Hiff.
  Qed.

  Definition is_enum_ot {rt} (en : enum rt) (ot : op_type) :=
    match ot with
    | EnumOp el variant_ots tag_int =>
        use_enum_layout_alg en.(enum_els) = Some el ∧
        tag_int = en.(enum_els).(els_tag_int) ∧
        op_type_wf (EnumOp el variant_ots tag_int) ∧
        enum_tag_ty_has_op_types en.(enum_tag_ty) variant_ots
    | UntypedOp ly =>
        ∃ el : enum_layout, use_enum_layout_alg en.(enum_els) = Some el ∧
        ly = el
    | _ => False
    end.
  Global Typeclasses Opaque is_enum_ot.

  Lemma is_enum_ot_layout {rt} (en : enum rt) ot :
    is_enum_ot en ot →
    syn_type_has_layout en.(enum_els) (ot_layout ot).
  Proof.
    rewrite /is_enum_ot.
    destruct ot as [|it| | |sl ots|el variant_ots tag_int|ly|]; simpl; try done.
    - intros (Halg & _). by eapply use_enum_layout_alg_Some_inv.
    - intros (el & Halg & ->). by eapply use_enum_layout_alg_Some_inv.
  Qed.

  Lemma is_enum_ot_wf {rt} (en : enum rt) ot :
    is_enum_ot en ot →
    op_type_wf ot.
  Proof.
    rewrite /is_enum_ot.
    destruct ot as [|it| | |sl ots|el variant_ots tag_int|ly|]; simpl; try done.
    intros (_ & _ & Hwf & _). done.
  Qed.

  Lemma is_enum_ot_variant_has_op_type {rt} (en : enum rt)
      el variant_ots tag_int r variant variant_ot :
    is_enum_ot en (EnumOp el variant_ots tag_int) →
    en.(enum_tag) r = Some variant →
    enum_variant_ot_lookup variant_ots variant = Some variant_ot →
    ty_has_op_type (en.(enum_ty) r) variant_ot.
  Proof.
    rewrite /is_enum_ot.
    intros (Halg & _ & Hwf & Hot) Htag Hvariant_ot.
    destruct (enum_tag_compat _ en r variant Htag) as (vinj & Hsem).
    unfold enum_tag_ty_has_op_types in Hot.
    apply enum_tag_ty_find_elem in Hsem as Hsem_elem.
    apply list_elem_of_lookup_1 in Hsem_elem as (i & Hsem_lookup).
    destruct (Forall2_lookup_l _ _ _ _ _ Hot Hsem_lookup) as ([variant' variant_ot'] & Hvariant_ot_lookup & [Hvariant_eq Hot_payload]).
    simpl in Hvariant_eq. subst variant'.
    rewrite /enum_variant_ot_lookup in Hvariant_ot.
    apply fmap_Some in Hvariant_ot as ([j [variant'' variant_ot'']] & Hfind & Hvariant_ot_eq).
    simpl in Hvariant_ot_eq. subst variant_ot''.
    apply list_find_Some in Hfind as (Hvariant_ot_lookup' & Hvariant_eq' & _).
    simpl in Hvariant_eq'. subst variant''.
    assert (NoDup variant_ots.*1) as Hnodup.
    { destruct Hwf as (Hvariant_names & _).
      rewrite Hvariant_names.
      apply enum_variant_names_NoDup. }
    assert (variant_ots.*1 !! i = Some variant) as Hi.
    { by rewrite list_lookup_fmap Hvariant_ot_lookup. }
    assert (variant_ots.*1 !! j = Some variant) as Hj.
    { by rewrite list_lookup_fmap Hvariant_ot_lookup'. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hi Hj) as ->.
    rewrite Hvariant_ot_lookup in Hvariant_ot_lookup'. inversion Hvariant_ot_lookup'. subst.
    done.
  Qed.

  Lemma is_enum_ot_enum_layout_agree {rt} (en : enum rt)
      el variant_ots tag_int el' :
    is_enum_ot en (EnumOp el variant_ots tag_int) →
    use_enum_layout_alg en.(enum_els) = Some el' →
    el = el'.
  Proof.
    rewrite /is_enum_ot. intros (Halg & _) Halg'. congruence.
  Qed.

  Lemma is_enum_ot_enum_tag_int {rt} (en : enum rt)
      el variant_ots tag_int :
    is_enum_ot en (EnumOp el variant_ots tag_int) →
    tag_int = en.(enum_els).(els_tag_int).
  Proof. rewrite /is_enum_ot. intros (_ & Htag_int & _). done. Qed.

  Lemma is_enum_ot_variant_payload_wf {rt} (en : enum rt)
      el variant_ots tag_int variant variant_ly variant_ot :
    is_enum_ot en (EnumOp el variant_ots tag_int) →
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    enum_variant_ot_lookup variant_ots variant = Some variant_ot →
    op_type_wf variant_ot ∧ ot_layout variant_ot = variant_ly.
  Proof.
    intros Hot Hvariant Hvariant_ot.
    eapply enum_variant_payload_wf; [by eapply is_enum_ot_wf|done|done].
  Qed.

  Lemma enum_tag_lookup_els_lookup_tag (els : enum_layout_spec) variant :
    variant ∈ els.(els_variants).*1 →
    enum_tag_lookup els.(els_tag_int) (els_lookup_tag els variant) = Some variant.
  Proof.
    intros Hin.
    pose proof (els_tag_int_agree els) as Hagree.
    assert (variant ∈ els.(els_tag_int).*1) as Htag_in.
    { by rewrite Hagree. }
    assert (NoDup els.(els_tag_int).*1) as Htag_nodup.
    { rewrite Hagree. apply els_variants_nodup. }
    destruct (list_to_map_lookup_fst els.(els_tag_int) variant Htag_in Htag_nodup) as (tag & Hmap).
    assert ((variant, tag) ∈ els.(els_tag_int)) as Hin_pair.
    { eapply elem_of_list_to_map; done. }
    assert (els_lookup_tag els variant = tag) as ->.
    { rewrite /els_lookup_tag Hmap //. }
    apply list_elem_of_lookup_1 in Hin_pair as (i & Hlook).
    rewrite /enum_tag_lookup.
    assert (list_find (λ x : string * Z, x.2 = tag) els.(els_tag_int) = Some (i, (variant, tag))) as ->; last done.
    apply list_find_Some. split_and!; simpl; try done.
      intros j [variant' tag'] Hlook' Hlt Htag'. simpl in Htag'. subst tag'.
      assert (els.(els_tag_int).*2 !! i = Some tag) as Hi.
      { by rewrite list_lookup_fmap Hlook. }
      assert (els.(els_tag_int).*2 !! j = Some tag) as Hj.
      { by rewrite list_lookup_fmap Hlook'. }
      pose proof (NoDup_lookup els.(els_tag_int).*2 i j tag (els_tag_int_nodup els) Hi Hj).
      lia.
  Qed.

  Lemma enum_variant_ot_lookup_is_Some el variant_ots tag_int variant variant_ly :
    op_type_wf (EnumOp el variant_ots tag_int) →
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    ∃ variant_ot, enum_variant_ot_lookup variant_ots variant = Some variant_ot.
  Proof.
    intros (Hvariant_names & _) Hvariant.
    apply enum_variant_lookup_in in Hvariant.
    assert (variant ∈ enum_variant_names el.(el_variants)) as Hin_names.
    { apply list_elem_of_lookup_1 in Hvariant as (i & Hlook).
      apply (list_elem_of_lookup_2 _ i). rewrite /enum_variant_names list_lookup_fmap Hlook //. }
    rewrite -Hvariant_names in Hin_names.
    apply list_elem_of_fmap in Hin_names as ([variant' variant_ot] & ? & Hin); simpl in *; subst variant'.
    destruct (list_find_elem_of (λ x : var_name * op_type, x.1 = variant)
      variant_ots (variant, variant_ot) Hin eq_refl) as ([i [variant' variant_ot']] & Hfind).
    exists variant_ot'.
    by rewrite /enum_variant_ot_lookup Hfind /=.
  Qed.

  Lemma use_enum_layout_alg_variant_names (els : enum_layout_spec) el :
    use_enum_layout_alg els = Some el →
    enum_variant_names el.(el_variants) = els.(els_variants).*1.
  Proof.
    intros (variant_lys & Halg & Hvariants)%use_enum_layout_alg_inv.
    pose proof (enum_layout_alg_has_variants _ _ _ _ _ Halg) as (_ & ->).
    rewrite /enum_variant_names.
    clear Halg.
    induction Hvariants as [|[name st] [name' ly] variants variant_lys [? _] _ IH]; simpl; first done.
    by subst name'; f_equal.
  Qed.

  Lemma enum_tag_padding_syn_type_has_layout el variant variant_ly :
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    syn_type_has_layout (LiteralSynType (enum_tag_padding_ly el)) (enum_tag_padding_ly el).
  Proof.
    intros Hvariant.
    pose proof (enum_variant_lookup_in_bounds _ _ _ Hvariant) as Hvariant_bound.
    apply syn_type_has_layout_literal; first done.
    - rewrite /enum_tag_padding_ly /layout_wf /ly_align /=. apply Z.divide_1_l.
    - rewrite /enum_tag_padding_ly /=.
      change (ly_size {| ly_size := el_data_offset el - ly_size (el_tag_it el); ly_align_log := 0 |}) with (el_data_offset el - ly_size (el_tag_it el))%nat.
      assert (el_data_offset el - ly_size (el_tag_it el) ≤ el_size el)%nat as Hpad_bound.
      { change (ly_size el) with (el_size el) in Hvariant_bound. lia. }
      apply Nat2Z.inj_le in Hpad_bound. pose proof (el_size_bounded el). rewrite MaxInt_eq. lia.
    - rewrite /ly_align_in_bounds /ly_align /enum_tag_padding_ly /=. unfold_common_radium_defs. simpl. nia.
  Qed.

  Lemma enum_tail_padding_syn_type_has_layout el variant variant_ly :
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    syn_type_has_layout (LiteralSynType (enum_tail_padding_ly el variant_ly)) (enum_tail_padding_ly el variant_ly).
  Proof.
    intros Hvariant.
    pose proof (enum_variant_lookup_in_bounds _ _ _ Hvariant) as Hvariant_bound.
    apply syn_type_has_layout_literal; first done.
    - rewrite /enum_tail_padding_ly /layout_wf /ly_align /=. apply Z.divide_1_l.
    - rewrite /enum_tail_padding_ly /=.
      change (ly_size {| ly_size := el_size el - el_data_offset el - ly_size variant_ly; ly_align_log := 0 |}) with (el_size el - el_data_offset el - ly_size variant_ly)%nat.
      assert (el_size el - el_data_offset el - ly_size variant_ly ≤ el_size el)%nat as Hpad_bound.
      { change (ly_size el) with (el_size el) in Hvariant_bound. lia. }
      apply Nat2Z.inj_le in Hpad_bound. pose proof (el_size_bounded el). rewrite MaxInt_eq. lia.
    - rewrite /ly_align_in_bounds /ly_align /enum_tail_padding_ly /=. unfold_common_radium_defs. simpl. nia.
  Qed.

  Lemma enum_tag_padding_uninit_syn_type_has_layout el variant variant_ly :
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    syn_type_has_layout
      (ty_syn_type (uninit (LiteralSynType (enum_tag_padding_ly el))) MetaNone)
      (enum_tag_padding_ly el).
  Proof.
    intros Hvariant. simpl.
    apply syn_type_has_layout_untyped.
    by apply enum_tag_padding_syn_type_has_layout with variant variant_ly.
  Qed.

  Lemma enum_tail_padding_uninit_syn_type_has_layout el variant variant_ly :
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    syn_type_has_layout
      (ty_syn_type (uninit (LiteralSynType (enum_tail_padding_ly el variant_ly))) MetaNone)
      (enum_tail_padding_ly el variant_ly).
  Proof.
    intros Hvariant. simpl.
    apply syn_type_has_layout_untyped.
    by apply enum_tail_padding_syn_type_has_layout with variant.
  Qed.

  Lemma enum_tag'_Some {rt} (en : enum rt) r variant :
    enum_tag en r = Some variant →
    enum_tag' en r = variant.
  Proof. by rewrite /enum_tag' => ->. Qed.

  Lemma enum_val_has_layout_from_parts el variant variant_ly v :
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    take (ly_size (it_layout el.(el_tag_it))) v `has_layout_val` it_layout el.(el_tag_it) →
    take (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it)))
      (drop (ly_size (it_layout el.(el_tag_it))) v) `has_layout_val` enum_tag_padding_ly el →
    take (ly_size variant_ly) (drop el.(el_data_offset) v) `has_layout_val` variant_ly →
    drop (el.(el_data_offset) + ly_size variant_ly) v `has_layout_val` enum_tail_padding_ly el variant_ly →
    v `has_layout_val` el.
  Proof.
    rewrite /has_layout_val /enum_tag_padding_ly /enum_tail_padding_ly /=.
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    intros Hvariant Htag Htag_pad Hvariant_val Htail.
    pose proof (el_tag_before_data el) as Htag_before.
    pose proof (enum_variant_lookup_in_bounds el variant variant_ly Hvariant) as Hvariant_bound.
    fold tag_size data_offset in Htag_before.
    fold data_offset variant_size in Hvariant_bound.
    rewrite length_take in Htag.
    rewrite length_take length_drop in Htag_pad.
    rewrite length_take length_drop in Hvariant_val.
    rewrite length_drop in Htail.
    change (ly_size {| ly_size := data_offset - tag_size; ly_align_log := 0 |}) with
      (data_offset - tag_size) in Htag_pad.
    change (ly_size {| ly_size := el.(el_size) - data_offset - variant_size; ly_align_log := 0 |}) with
      (el.(el_size) - data_offset - variant_size) in Htail.
    assert (tag_size ≤ length v) as Htag_bound.
    { rewrite <-Htag. apply Nat.le_min_r. }
    assert (data_offset ≤ length v) as Hdata_bound.
    { assert (data_offset - tag_size ≤ length v - tag_size) as Hpad_bound.
      { rewrite <-Htag_pad. apply Nat.le_min_r. }
      lia. }
    assert (data_offset + variant_size ≤ length v) as Hpayload_bound.
    { assert (variant_size ≤ length v - data_offset) as Hvariant_bound'.
      { rewrite <-Hvariant_val. apply Nat.le_min_r. }
      lia. }
    change (ly_size el) with el.(el_size).
    lia.
  Qed.

  Lemma enum_pointsto_val_split {rt} (e : enum rt) π r l el variant variant_ly :
    enum_variant_lookup el.(el_variants) variant = Some variant_ly →
    syn_type_has_layout (ty_syn_type (e.(enum_ty) r) MetaNone) variant_ly →
    (∃ v : val,
      l ↦ v ∗
      take (ly_size (it_layout el.(el_tag_it))) v
        ◁ᵥ{π, MetaNone} els_lookup_tag e.(enum_els) variant @ int el.(el_tag_it) ∗
      take (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it)))
        (drop (ly_size (it_layout el.(el_tag_it))) v)
        ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el)) ∗
      take (ly_size variant_ly) (drop el.(el_data_offset) v)
        ◁ᵥ{π, MetaNone} e.(enum_r) r @ e.(enum_ty) r ∗
      drop (el.(el_data_offset) + ly_size variant_ly) v
        ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly)))
    ⊣⊢
    ((∃ vtag : val, l ↦ vtag ∗
        vtag ◁ᵥ{π, MetaNone} els_lookup_tag e.(enum_els) variant @ int el.(el_tag_it)) ∗
     (∃ vtag_pad : val, (l +ₗ ly_size (it_layout el.(el_tag_it))) ↦ vtag_pad ∗
        vtag_pad ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el))) ∗
     (∃ vvariant : val, (l +ₗ el.(el_data_offset)) ↦ vvariant ∗
        vvariant ◁ᵥ{π, MetaNone} e.(enum_r) r @ e.(enum_ty) r) ∗
     (∃ vtail : val, (l +ₗ (el.(el_data_offset) + ly_size variant_ly)%nat) ↦ vtail ∗
        vtail ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly))))%I.
  Proof.
    iIntros (Hvariant Hst).
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (tag_pad_size := el.(el_data_offset) - tag_size).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    iSplit.
    - iIntros "(%v & Hl & Htag & Htag_pad & Hvariant & Htail)".
      iPoseProof (ty_own_val_has_layout with "Htag") as "%Htag_val".
      { simpl. apply syn_type_has_layout_int. done. }
      iPoseProof (ty_has_layout with "Htag_pad") as "(%tag_pad_ly & %Htag_pad_st & %Htag_pad_val)".
      apply syn_type_has_layout_untyped_inv in Htag_pad_st.
      apply syn_type_has_layout_literal_inv in Htag_pad_st as (-> & _ & _ & _).
      iPoseProof (ty_own_val_has_layout with "Hvariant") as "%Hvariant_val"; first done.
      iPoseProof (ty_has_layout with "Htail") as "(%tail_ly & %Htail_st & %Htail_val)".
      apply syn_type_has_layout_untyped_inv in Htail_st.
      apply syn_type_has_layout_literal_inv in Htail_st as (-> & _ & _ & _).
      rewrite -{1}(take_drop tag_size v) heap_pointsto_app.
      iDestruct "Hl" as "(Hl_tag & Hl_rest)".
      rewrite /has_layout_val in Htag_val.
      fold tag_size in Htag_val.
      rewrite Htag_val.
      rewrite -{1}(take_drop tag_pad_size (drop tag_size v)) heap_pointsto_app.
      iDestruct "Hl_rest" as "(Hl_tag_pad & Hl_rest)".
      rewrite /has_layout_val /enum_tag_padding_ly /= in Htag_pad_val.
      fold tag_size in Htag_pad_val. fold tag_pad_size in Htag_pad_val.
      change (ly_size {| ly_size := tag_pad_size; ly_align_log := 0 |}) with tag_pad_size in Htag_pad_val.
      rewrite Htag_pad_val.
      rewrite shift_loc_assoc_nat.
      replace (tag_size + tag_pad_size)%nat with data_offset by
        (symmetry; rewrite /tag_pad_size /data_offset Nat.add_comm; apply Nat.sub_add; apply Nat2Z.inj_le; apply el_tag_before_data).
      replace (drop tag_pad_size (drop tag_size v)) with (drop data_offset v) by
        (rewrite drop_drop; replace (tag_size + tag_pad_size)%nat with data_offset; first done;
         symmetry; rewrite /tag_pad_size /data_offset Nat.add_comm; apply Nat.sub_add; apply Nat2Z.inj_le; apply el_tag_before_data).
      rewrite -{1}(take_drop variant_size (drop data_offset v)) heap_pointsto_app.
      iDestruct "Hl_rest" as "(Hl_variant & Hl_tail)".
      rewrite /has_layout_val in Hvariant_val.
      fold variant_size in Hvariant_val.
      rewrite Hvariant_val.
      rewrite shift_loc_assoc_nat.
      replace (drop variant_size (drop data_offset v)) with (drop (data_offset + variant_size) v) by by rewrite drop_drop.
      iSplitL "Hl_tag Htag".
      { iExists _. iFrame. }
      iSplitL "Hl_tag_pad Htag_pad".
      { iExists _. iFrame. }
      iSplitL "Hl_variant Hvariant".
      { iExists _. iFrame. }
      iExists (drop (data_offset + variant_size) v).
      iFrame.
    - iIntros "((%vtag & Hl_tag & Htag) & (%vtag_pad & Hl_tag_pad & Htag_pad) & (%vvariant & Hl_variant & Hvariant) & (%vtail & Hl_tail & Htail))".
      iPoseProof (ty_own_val_has_layout with "Htag") as "%Htag_val".
      { simpl. apply syn_type_has_layout_int. done. }
      iPoseProof (ty_has_layout with "Htag_pad") as "(%tag_pad_ly & %Htag_pad_st & %Htag_pad_val)".
      apply syn_type_has_layout_untyped_inv in Htag_pad_st.
      apply syn_type_has_layout_literal_inv in Htag_pad_st as (-> & _ & _ & _).
      iPoseProof (ty_own_val_has_layout with "Hvariant") as "%Hvariant_val"; first done.
      iPoseProof (ty_has_layout with "Htail") as "(%tail_ly & %Htail_st & %Htail_val)".
      apply syn_type_has_layout_untyped_inv in Htail_st.
      apply syn_type_has_layout_literal_inv in Htail_st as (-> & _ & _ & _).
      iExists (vtag ++ vtag_pad ++ vvariant ++ vtail).
      rewrite heap_pointsto_app.
      rewrite /has_layout_val in Htag_val.
      fold tag_size in Htag_val.
      rewrite Htag_val.
      rewrite heap_pointsto_app.
      rewrite /has_layout_val /enum_tag_padding_ly /= in Htag_pad_val.
      fold tag_size in Htag_pad_val. fold tag_pad_size in Htag_pad_val.
      change (ly_size {| ly_size := tag_pad_size; ly_align_log := 0 |}) with tag_pad_size in Htag_pad_val.
      rewrite Htag_pad_val.
      rewrite shift_loc_assoc_nat.
      replace (tag_size + tag_pad_size)%nat with data_offset by
        (symmetry; rewrite /tag_pad_size /data_offset Nat.add_comm; apply Nat.sub_add; apply Nat2Z.inj_le; apply el_tag_before_data).
      rewrite heap_pointsto_app.
      rewrite /has_layout_val in Hvariant_val.
      fold variant_size in Hvariant_val.
      rewrite Hvariant_val.
      rewrite shift_loc_assoc_nat.
      iFrame.
      rewrite take_app_length'; last lia.
      iSplitL "Htag"; first done.
      rewrite drop_app_length'; last lia.
      rewrite take_app_length'; last lia.
      iSplitL "Htag_pad"; first done.
      replace data_offset with (length (vtag ++ vtag_pad)).
      2: { rewrite length_app Htag_val Htag_pad_val.
           rewrite /tag_pad_size /data_offset Nat.add_comm. apply Nat.sub_add. apply Nat2Z.inj_le. apply el_tag_before_data. }
      replace (drop (length (vtag ++ vtag_pad)) (vtag ++ vtag_pad ++ vvariant ++ vtail)) with (vvariant ++ vtail) by
        (rewrite app_assoc; rewrite drop_app_length'; done).
      rewrite take_app_length'; last lia.
      iSplitL "Hvariant"; first done.
      replace (length (vtag ++ vtag_pad) + variant_size)%nat with (length (vtag ++ vtag_pad ++ vvariant)).
      2: { rewrite !length_app Hvariant_val. lia. }
      replace (drop (length (vtag ++ vtag_pad ++ vvariant)) (vtag ++ vtag_pad ++ vvariant ++ vtail)) with vtail by
        (rewrite !app_assoc; rewrite drop_app_length'; done).
      done.
  Qed.

  Definition enum_own_val_def {rt} (e : enum rt) π r m v : iProp Σ :=
    (∃ el variant variant_ly,
      ⌜m = MetaNone⌝ ∗
      ⌜use_enum_layout_alg e.(enum_els) = Some el⌝ ∗
      ⌜e.(enum_tag) r = Some variant⌝ ∗
      ⌜enum_variant_lookup el.(el_variants) variant = Some variant_ly⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type (e.(enum_ty) r) MetaNone) variant_ly⌝ ∗
      take (ly_size (it_layout el.(el_tag_it))) v
        ◁ᵥ{π, MetaNone} els_lookup_tag e.(enum_els) variant @ int el.(el_tag_it) ∗
      take (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it)))
        (drop (ly_size (it_layout el.(el_tag_it))) v)
        ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el)) ∗
      take (ly_size variant_ly) (drop el.(el_data_offset) v)
        ◁ᵥ{π, MetaNone} e.(enum_r) r @ e.(enum_ty) r ∗
      drop (el.(el_data_offset) + ly_size variant_ly) v
        ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly)))%I.
  Definition enum_own_val_aux : seal (@enum_own_val_def).
  Proof. by eexists. Qed.
  Definition enum_own_val := enum_own_val_aux.(unseal).
  Definition enum_own_val_unfold : @enum_own_val = @enum_own_val_def := enum_own_val_aux.(seal_eq).
  Global Arguments enum_own_val {_}.

  Lemma enum_own_val_has_layout {rt} (e : enum rt) π r m v :
    enum_own_val e π r m v -∗
    ∃ el, ⌜m = MetaNone ∧ use_enum_layout_alg e.(enum_els) = Some el ∧ v `has_layout_val` el⌝.
  Proof.
    rewrite enum_own_val_unfold.
    iIntros "(%el & %variant & %variant_ly & -> & %Halg & %Htag & %Hvariant & %Hst & Htag & Htag_pad & Hvariant & Htail)".
    iPoseProof (ty_own_val_has_layout with "Htag") as "%Htag_val".
    { simpl. apply syn_type_has_layout_int. done. }
    rewrite uninit_own_spec.
    iDestruct "Htag_pad" as "(_ & %tag_pad_ly & %Htag_pad_ly & %Htag_pad_val)".
    apply syn_type_has_layout_literal_inv in Htag_pad_ly as (-> & _ & _ & _).
    iPoseProof (ty_own_val_has_layout with "Hvariant") as "%Hvariant_val"; first done.
    rewrite uninit_own_spec.
    iDestruct "Htail" as "(_ & %tail_ly & %Htail_ly & %Htail_val)".
    apply syn_type_has_layout_literal_inv in Htail_ly as (-> & _ & _ & _).
    iExists el. iPureIntro. split_and!; [done..|].
    by eapply enum_val_has_layout_from_parts.
  Qed.

  Definition enum_shr_def {rt} (e : enum rt) κ π r m l : iProp Σ :=
    (∃ el variant variant_ly,
      ⌜m = MetaNone⌝ ∗
      ⌜use_enum_layout_alg e.(enum_els) = Some el⌝ ∗
      ⌜e.(enum_tag) r = Some variant⌝ ∗
      ⌜enum_variant_lookup el.(el_variants) variant = Some variant_ly⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type (e.(enum_ty) r) MetaNone) variant_ly⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      l ◁ₗ{π, MetaNone, κ} els_lookup_tag e.(enum_els) variant @ int el.(el_tag_it) ∗
      (l +ₗ Z.of_nat (ly_size (it_layout el.(el_tag_it))))
        ◁ₗ{π, MetaNone, κ} () @ uninit (LiteralSynType (enum_tag_padding_ly el)) ∗
      (l +ₗ Z.of_nat el.(el_data_offset))
        ◁ₗ{π, MetaNone, κ} e.(enum_r) r @ e.(enum_ty) r ∗
      (l +ₗ Z.of_nat (el.(el_data_offset) + ly_size variant_ly))
        ◁ₗ{π, MetaNone, κ} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly)))%I.
  Definition enum_shr_aux : seal (@enum_shr_def).
  Proof. by eexists. Qed.
  Definition enum_shr := enum_shr_aux.(unseal).
  Definition enum_shr_unfold : @enum_shr = @enum_shr_def := enum_shr_aux.(seal_eq).
  Global Arguments enum_shr {_}.


  Program Definition enum_t {rt} (e : enum rt) : type rt := {|
    ty_xt_inhabited := enum_xt_inhabited e;
    ty_metadata_kind := MetadataNone;
    ty_trivial_drop := true;
    ty_own_val π r m v :=
      enum_own_val e π r m v;
    ty_shr κ π r m l :=
      enum_shr e κ π r m l;
    ty_syn_type _ := e.(enum_els);
    _ty_has_op_type ot :=
      is_enum_ot e ot ;
    ty_sidecond := True%I;
    _ty_ghost_drop π r :=
      (* TODO *)
      True%I;
    _ty_lfts := enum_tag_ty_lfts e.(enum_tag_ty);
    _ty_wf_E := enum_tag_ty_wf_E e.(enum_tag_ty);
  |}.
  Next Obligation.
    intros rt en. econstructor.
    - iIntros (π r m v).
      rewrite enum_own_val_unfold.
      iIntros "(%el & %variant & %variant_ly & -> & %Halg & %Htag & %Hvariant & %Hst & Htag & Htag_pad & Hvariant & Htail)".
      iPoseProof (ty_own_val_has_layout with "Htag") as "%Htag_val".
      { simpl. apply syn_type_has_layout_int. done. }
      rewrite uninit_own_spec.
      iDestruct "Htag_pad" as "(_ & %tag_pad_ly & %Htag_pad_ly & %Htag_pad_val)".
      apply syn_type_has_layout_literal_inv in Htag_pad_ly as (-> & _ & _ & _).
      iPoseProof (ty_own_val_has_layout with "Hvariant") as "%Hvariant_val"; first done.
      rewrite uninit_own_spec.
      iDestruct "Htail" as "(_ & %tail_ly & %Htail_ly & %Htail_val)".
      apply syn_type_has_layout_literal_inv in Htail_ly as (-> & _ & _ & _).
      iClear "Htag Hvariant".
      iExists el. iPureIntro. split.
      + by eapply use_enum_layout_alg_Some_inv.
      + by eapply enum_val_has_layout_from_parts.
    - intros ot Hot.
      by apply is_enum_ot_layout.
    - intros ot Hot.
      by eapply is_enum_ot_wf.
    - iIntros (π r m v) "_". done.
    - iIntros (κ π r m l) "_". done.
    - unfold TCNoResolve. rewrite enum_shr_unfold /enum_shr_def. apply _.
    - iIntros (κ π l r m) "Hshr".
      rewrite enum_shr_unfold.
      iDestruct "Hshr" as "(%el & %variant & %variant_ly & -> & %Halg & %Htag & %Hvariant & %Hst & %Hly & _)".
      iExists el. iPureIntro. split; first done.
      by eapply use_enum_layout_alg_Some_inv.
    - iIntros (E κ l ly π r m q ?) "#CTX #Hna Htok %Halg %Hly Hlb Hb".
    set (bor_contents :=
      (∃ el variant variant_ly,
        ⌜m = MetaNone⌝ ∗
        ⌜use_enum_layout_alg en.(enum_els) = Some el⌝ ∗
        ⌜en.(enum_tag) r = Some variant⌝ ∗
        ⌜enum_variant_lookup el.(el_variants) variant = Some variant_ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type (en.(enum_ty) r) MetaNone) variant_ly⌝ ∗
        ∃ v : val, l ↦ v ∗
          take (ly_size (it_layout el.(el_tag_it))) v
            ◁ᵥ{π, MetaNone} els_lookup_tag en.(enum_els) variant @ int el.(el_tag_it) ∗
          take (el.(el_data_offset) - ly_size (it_layout el.(el_tag_it)))
            (drop (ly_size (it_layout el.(el_tag_it))) v)
            ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el)) ∗
          take (ly_size variant_ly) (drop el.(el_data_offset) v)
            ◁ᵥ{π, MetaNone} en.(enum_r) r @ en.(enum_ty) r ∗
          drop (el.(el_data_offset) + ly_size variant_ly) v
            ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly)))%I).
    iPoseProof (bor_iff _ _ bor_contents with "[] Hb") as "Hb".
    { iNext. iModIntro. rewrite /bor_contents enum_own_val_unfold /enum_own_val_def.
      iSplit.
      - iIntros "(%v & Hl & %el & %variant & %variant_ly & %Hmeta & %Halg' & %Htag' & %Hvariant' & %Hst' & Htag & Htag_pad & Hvariant & Htail)".
        iExists el, variant, variant_ly. do 5 (iSplit; first done).
        iExists v. iFrame.
      - iIntros "(%el & %variant & %variant_ly & %Hmeta & %Halg' & %Htag' & %Hvariant' & %Hst' & %v & Hl & Htag & Htag_pad & Hvariant & Htail)".
        iExists v. iSplitL "Hl"; first done.
        iExists el, variant, variant_ly.
        do 5 (iSplit; first done). iFrame. }
    rewrite /bor_contents.
    simpl. iEval (rewrite -lft_tok_sep) in "Htok". iDestruct "Htok" as "(Htok1 & Htok2)".
    iApply fupd_logical_step.
    iDestruct "CTX" as "(LFT & LLCTX)".
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%el & Hb & Htok1)"; first done.
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%variant & Hb & Htok1)"; first done.
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%variant_ly & Hb & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Halg & Hb)"; first done.
    iMod (bor_persistent with "LFT Halg Htok1") as "(>-> & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Halg & Hb)"; first done.
    iMod (bor_persistent with "LFT Halg Htok1") as "(>%Halg' & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Htag & Hb)"; first done.
    iMod (bor_persistent with "LFT Htag Htok1") as "(>%Htag & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hvariant & Hb)"; first done.
    iMod (bor_persistent with "LFT Hvariant Htok1") as "(>%Hvariant & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok1") as "(>%Hst & Htok1)"; first done.
    apply use_layout_alg_enum_Some_inv in Halg as (el' & Halg'' & ->).
    assert (el' = el) as -> by naive_solver.
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    iPoseProof (bor_iff _ _
      ((∃ vtag : val, l ↦ vtag ∗
          vtag ◁ᵥ{π, MetaNone} els_lookup_tag en.(enum_els) variant @ int el.(el_tag_it)) ∗
       (∃ vtag_pad : val, (l +ₗ tag_size) ↦ vtag_pad ∗
          vtag_pad ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tag_padding_ly el))) ∗
       (∃ vvariant : val, (l +ₗ data_offset) ↦ vvariant ∗
          vvariant ◁ᵥ{π, MetaNone} en.(enum_r) r @ en.(enum_ty) r) ∗
       (∃ vtail : val, (l +ₗ (data_offset + variant_size)%nat) ↦ vtail ∗
          vtail ◁ᵥ{π, MetaNone} () @ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly))))%I
      with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "H". rewrite /tag_size /data_offset /variant_size. iApply (enum_pointsto_val_split with "H"); done.
      - iIntros "H". rewrite /tag_size /data_offset /variant_size. iApply (enum_pointsto_val_split with "H"); done. }
    iMod (bor_sep with "LFT Hb") as "(Hb_tag & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hb_tag_pad & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hb_variant & Hb_tail)"; first done.

    iDestruct "Hlb" as "#Hlb".

    iDestruct "Htok1" as "(Htok_tag & Htok1)".
    iDestruct "Htok1" as "(Htok_tag_pad & Htok1)".
    iDestruct "Htok1" as "(Htok_variant_κ & Htok_tail)".

    iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna [Htok_tag] [] [] [] Hb_tag") as "Htag_step"; first done.
    { simpl. rewrite ty_lfts_unfold. rewrite right_id. iFrame. }
    { simpl. iPureIntro. apply syn_type_has_layout_int. done. }
    { iPureIntro. by apply enum_tag_has_layout_loc. }
    { iApply (loc_in_bounds_enum_tag with "Hlb"). done. }

    iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna [Htok_tag_pad] [] [] [] Hb_tag_pad") as "Htag_pad_step"; first done.
    { simpl. rewrite ty_lfts_unfold/=. rewrite right_id. iFrame. }
    { iPureIntro. by apply enum_tag_padding_uninit_syn_type_has_layout with variant variant_ly. }
    { iPureIntro. apply has_layout_loc_1. rewrite /enum_tag_padding_ly /ly_align /=. done. }
    { iApply (loc_in_bounds_enum_tag_padding with "Hlb"). done. }

    iPoseProof (list_incl_lft_incl_list (ty_lfts (en.(enum_ty) r)) (enum_tag_ty_lfts en.(enum_tag_ty))) as "Hincl".
    { etrans; last by eapply (enum_ty_lfts_incl_tag_ty_lfts en r _ Htag). done. }
    iMod (lft_incl_acc _ _ (lft_intersect_list (ty_lfts (en.(enum_ty) r))) with "[] Htok2") as "(%q' & Htok_variant_lfts & Hcl_variant_lfts)"; first done.
    { iApply "Hincl". }
    set (q0 := Qp.min (q / 2 / 2 / 2)%Qp q').
    iPoseProof (Fractional_fractional_le (λ q, q.[κ])%I (q / 2 / 2 / 2)%Qp q0 with "Htok_variant_κ") as "(Htok_variant_κ & Hcl_variant_κ)".
    { apply Qp.le_min_l. }
    iPoseProof (Fractional_fractional_le (λ q, q.[lft_intersect_list (ty_lfts (en.(enum_ty) r))])%I q' q0 with "Htok_variant_lfts") as "(Htok_variant_lfts & Hcl_variant_lfts')".
    { apply Qp.le_min_r. }
    iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna [Htok_variant_κ Htok_variant_lfts] [] [] [] Hb_variant") as "Hvariant_step"; first done.
    { rewrite ty_lfts_unfold -lft_tok_sep. iFrame. }
    { done. }
    { iPureIntro. by eapply enum_payload_has_layout_loc. }
    { iApply (loc_in_bounds_enum_payload with "Hlb"). done. }

    iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna [Htok_tail] [] [] [] Hb_tail") as "Htail_step"; first done.
    { simpl. rewrite ty_lfts_unfold/=. rewrite right_id. iFrame. }
    { iPureIntro. by apply enum_tail_padding_uninit_syn_type_has_layout with variant. }
    { iPureIntro. apply has_layout_loc_1. rewrite /enum_tail_padding_ly /ly_align /=. done. }
    { rewrite -/data_offset -/variant_size -shift_loc_assoc_nat.
      iApply (loc_in_bounds_enum_tail_padding with "Hlb"). done. }
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Htag_step").
    iApply (logical_step_compose with "Htag_pad_step").
    iApply (logical_step_compose with "Hvariant_step").
    iApply (logical_step_compose with "Htail_step").
    iApply logical_step_intro.
    iModIntro.
    iIntros "(Htag & Htok_tag) (Htag_pad & Htok_tag_pad) (Hvariant & Htok_variant) (Htail & Htok_tail)".
    iEval (rewrite -lft_tok_sep) in "Htok_variant".
    iDestruct "Htok_variant" as "(Htok_variant_κ & Htok_variant_lfts)".
    iEval (rewrite -lft_tok_sep) in "Htok_tag_pad".
    iDestruct "Htok_tag_pad" as "(Htok_tag_pad_κ & Htok_tag_pad_lfts)".
    iPoseProof ("Hcl_variant_κ" with "[$]") as "Htok_variant_κ'".
    (*iEval (rewrite -ty_lfts_unfold) in "Htok_tag_pad_lfts".*)
    iPoseProof ("Hcl_variant_lfts'" with "[$]") as "Hvariant_lfts'".
    iMod ("Hcl_variant_lfts" with "[$]") as "Htok2".
    rewrite enum_shr_unfold.
    iSplitL "Htag Htag_pad Hvariant Htail".
    { iExists el, variant, variant_ly. iFrame. done. }
    simpl. rewrite ty_lfts_unfold/=. rewrite right_id.
    iCombine "Htok_tag Htok_variant_κ'" as "Htok1".
    iCombine "Htok1 Htok_variant_κ" as "Htok1".
    iCombine "Htok1 Htok_tail" as "Htok1". rewrite -lft_tok_sep.
    by iFrame.
  - iIntros (κ κ' π r m l) "#Hincl Hshr".
    rewrite enum_shr_unfold.
    iDestruct "Hshr" as "(%el & %variant & %variant_ly & -> & %Halg & %Htag & %Hvariant & %Hst & %Hly & Htag & Htag_pad & Hvariant & Htail)".
    iExists el, variant, variant_ly. do 6 (iSplit; first done).
    iSplitL "Htag"; first by iApply (ty_shr_mono with "Hincl Htag").
    iSplitL "Htag_pad"; first by iApply (ty_shr_mono with "Hincl Htag_pad").
    iSplitL "Hvariant"; first by iApply (ty_shr_mono with "Hincl Hvariant").
    by iApply (ty_shr_mono with "Hincl Htail").
  - intros. iIntros "_". by iApply logical_step_intro.
  - intros ot st π r v Hot.
    rewrite /is_enum_ot in Hot.
    destruct ot as [ | | | | ? ? | ? ? ? | el | ]; try done.
    + destruct Hot as (Halg & Htag_int & Hwf & Hot).
      iIntros "Hv".
      iPoseProof (enum_own_val_has_layout with "Hv") as "(%elv & %_ & %Halgv & %Hlyv)".
      assert (elv = el) as -> by congruence.
      iEval (rewrite enum_own_val_unfold /enum_own_val_def) in "Hv".
      iDestruct "Hv" as "(%el0 & %variant & %variant_ly & Hv)".
      iDestruct "Hv" as "(%Hmeta & %Halg0 & %Htag & %Hvariant & %Hst & Htag & Htag_pad & Hvariant & Htail)".
      assert (el0 = el) as -> by congruence.
      destruct (enum_variant_ot_lookup_is_Some el variant_ots tag_int variant variant_ly Hwf Hvariant) as (variant_ot & Hvariant_ot).
      iPoseProof (ty_decodable _ (en.(enum_ty) r) variant_ot st π _ _ with "Hvariant") as (payload_ov) "%Hpayload_dec".
      { eapply is_enum_ot_variant_has_op_type; [rewrite /is_enum_ot; split_and!; done|done|done]. }
      iEval (rewrite /ty_own_val /= int_own_val_unfold) in "Htag".
      iDestruct "Htag" as "%Htag_val".
      destruct Htag_val as [_ Htag_val].
      iExists (OVEnum el variant (els_lookup_tag en.(enum_els) variant) payload_ov). iPureIntro.
      simp decode_op_val.
      rewrite bool_decide_true; last done.
      rewrite Htag_val Htag_int /=.
      rewrite enum_tag_lookup_els_lookup_tag /=.
      2: { rewrite -(use_enum_layout_alg_variant_names _ _ Halg).
           pose proof (enum_variant_lookup_in _ _ _ Hvariant) as Hvariant_in.
           apply list_elem_of_lookup_1 in Hvariant_in as (i & Hvariant_lookup).
           apply (list_elem_of_lookup_2 _ i). rewrite /enum_variant_names list_lookup_fmap Hvariant_lookup //. }
      rewrite Hvariant /lookup_enum_variant_ot Hvariant_ot /= Hpayload_dec //.
    + destruct Hot as (el' & Hel & ->).
      iIntros "Hv".
      iPoseProof (enum_own_val_has_layout with "Hv") as "(%elv & %_ & %Halgv & %Hlyv)".
      assert (elv = el') as -> by congruence.
      iExists (OVUntyped el' v). iPureIntro.
      simp decode_op_val. by rewrite bool_decide_true.
  - intros ot st π r v v' Hot Hsame.
    rewrite /is_enum_ot in Hot.
    destruct ot as [ | | | | ? ? | ? ? ? | el | ]; try done.
    + destruct Hot as (Halg & Htag_int & Hwf & Hot).
      iIntros "Hv".
      iPoseProof (enum_own_val_has_layout with "Hv") as "(%elv & %_ & %Halgv & %Hlyv)".
      assert (elv = el) as -> by congruence.
      pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hlyv'.
      rewrite /has_layout_val /= in Hlyv'.
      iEval (rewrite enum_own_val_unfold /enum_own_val_def) in "Hv".
      iDestruct "Hv" as "(%el0 & %variant & %variant_ly & Hv)".
      iDestruct "Hv" as "(%Hmeta & %Halg0 & %Htag & %Hvariant & %Hst & Htag & Htag_pad & Hvariant & Htail)".
      assert (el0 = el) as -> by congruence.
      destruct (enum_variant_ot_lookup_is_Some el variant_ots tag_int variant variant_ly Hwf Hvariant) as (variant_ot & Hvariant_ot).
      iPoseProof (ty_decodable _ (en.(enum_ty) r) variant_ot st π _ _ with "Hvariant") as (payload_ov) "%Hpayload_dec".
      { eapply is_enum_ot_variant_has_op_type; [rewrite /is_enum_ot; split_and!; done|done|done]. }
      iEval (rewrite /ty_own_val /= int_own_val_unfold) in "Htag".
      iDestruct "Htag" as "%Htag_val".
      destruct Htag_val as [_ Htag_val].
      assert (Hdec_v : decode_op_val v (EnumOp el variant_ots tag_int) st =
        Some (OVEnum el variant (els_lookup_tag en.(enum_els) variant) payload_ov)).
      { simp decode_op_val.
        rewrite bool_decide_true; last done.
        rewrite Htag_val Htag_int /=.
        rewrite enum_tag_lookup_els_lookup_tag /=.
        2: { rewrite -(use_enum_layout_alg_variant_names _ _ Halg).
             pose proof (enum_variant_lookup_in _ _ _ Hvariant) as Hvariant_in.
             apply list_elem_of_lookup_1 in Hvariant_in as (i & Hvariant_lookup).
             apply (list_elem_of_lookup_2 _ i). rewrite /enum_variant_names list_lookup_fmap Hvariant_lookup //. }
        rewrite Hvariant /lookup_enum_variant_ot Hvariant_ot /= Hpayload_dec //. }
      destruct Hsame as [Hsame_eq _].
      assert (Hdec_v' : decode_op_val v' (EnumOp el variant_ots tag_int) st =
        Some (OVEnum el variant (els_lookup_tag en.(enum_els) variant) payload_ov)).
      { by rewrite -Hsame_eq. }
      pose proof Hdec_v' as Hdec_v'_inv.
      simp decode_op_val in Hdec_v'_inv.
      rewrite bool_decide_true in Hdec_v'_inv; last done.
      destruct (val_to_Z (take (ly_size (el_tag_it el)) v') (el_tag_it el)) as [tag'|] eqn:Htag_val'; simpl in Hdec_v'_inv; try done.
      destruct (enum_tag_lookup tag_int tag') as [variant'|] eqn:Htag_lookup'; simpl in Hdec_v'_inv; try done.
      destruct (enum_variant_lookup (el_variants el) variant') as [variant_ly'|] eqn:Hvariant'; simpl in Hdec_v'_inv; try done.
      destruct (lookup_enum_variant_ot variant_ots variant') as [[variant_ot' Hvariant_ot']|] eqn:Hvariant_ot_sig; simpl in Hdec_v'_inv; try done.
      destruct (decode_op_val (take (ly_size variant_ly') (drop (el_data_offset el) v')) variant_ot' st) as [payload_ov'|] eqn:Hpayload_dec'; simpl in Hdec_v'_inv; try done.
      inversion Hdec_v'_inv; subst; clear Hdec_v'_inv.
      assert (variant_ly' = variant_ly) as -> by congruence.
      assert (variant_ot' = variant_ot) as -> by congruence.
      assert (Hpayload_same : is_same_decoded_val_at st
        (take (ly_size variant_ly) (drop (el_data_offset el) v)) variant_ot
        (take (ly_size variant_ly) (drop (el_data_offset el) v'))).
      { split; first by rewrite Hpayload_dec Hpayload_dec'. eauto. }
      rewrite enum_own_val_unfold /enum_own_val_def.
      iExists el, variant, variant_ly. iSplit; first done.
      iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
      iSplitL "".
      { iEval (rewrite /ty_own_val /= int_own_val_unfold). iPureIntro. split; done. }
      iSplitL "".
      { rewrite uninit_own_spec. iSplit; first done. iExists (enum_tag_padding_ly el). iPureIntro. split.
        - by apply enum_tag_padding_syn_type_has_layout with variant variant_ly.
        - rewrite /has_layout_val /enum_tag_padding_ly /= length_take length_drop.
          change (ly_size {| ly_size := el_data_offset el - ly_size (it_layout (el_tag_it el)); ly_align_log := 0 |}) with
            (el_data_offset el - ly_size (it_layout (el_tag_it el)))%nat.
          rewrite Nat.min_l; first done.
          pose proof (enum_variant_lookup_in_bounds _ _ _ Hvariant).
          change (ly_size el) with el.(el_size) in Hlyv'. lia. }
      iSplitL "Hvariant".
      { by iApply (ty_decode_compat with "Hvariant"); [eapply is_enum_ot_variant_has_op_type; [rewrite /is_enum_ot; split_and!; done|done|done]|]. }
      rewrite uninit_own_spec. iSplit; first done. iExists (enum_tail_padding_ly el variant_ly). iPureIntro. split.
      { by apply enum_tail_padding_syn_type_has_layout with variant. }
      rewrite /has_layout_val /enum_tail_padding_ly /= length_drop.
      change (ly_size {| ly_size := el_size el - el_data_offset el - ly_size variant_ly; ly_align_log := 0 |}) with
        (el_size el - el_data_offset el - ly_size variant_ly)%nat.
      change (ly_size el) with el.(el_size) in Hlyv'. lia.
    + destruct Hot as (el' & Hel & ->).
      iIntros "Hv".
      iPoseProof (enum_own_val_has_layout with "Hv") as "(%elv & %_ & %Halgv & %Hlyv)".
      assert (elv = el') as -> by congruence.
      pose proof (is_same_decoded_val_at_has_layout_r _ _ _ _ Hsame) as Hlyv'.
      rewrite /has_layout_val /= in Hlyv'.
      pose proof (is_same_decoded_val_at_untyped_inv st v v' el' Hlyv Hlyv' Hsame) as ->.
      done.
  - intros ly _ Hst.
    apply syn_type_has_layout_enum_inv in Hst as (el & ul & variants & Hul & Hsl & -> & Hf).
    simpl. exists el. split; last done.
    by eapply use_enum_layout_alg_Some.
  - apply _.
  - apply _.
  Qed.

  Local Instance enum_t_copy_pers {rt} (e : enum rt) m :
    (∀ r : rt, Copyable ((e.(enum_ty) r))) →
    ∀ π v r, Persistent (v ◁ᵥ{π, m} r @ enum_t e).
  Proof.
    iIntros (Hcopy).
    iIntros (???).
    rewrite /ty_own_val/= enum_own_val_unfold /enum_own_val_def.
    apply bi.exist_persistent => el.
    apply bi.exist_persistent => variant.
    apply bi.exist_persistent => variant_ly.
    repeat (apply bi_sep_persistent_pure_l => ?).
    apply bi.sep_persistent; first apply _.
    apply bi.sep_persistent; first apply _.
    apply bi.sep_persistent; first apply Hcopy.
    apply _.
  Qed.

  Lemma enum_t_copyable {rt} (e : enum rt):
    (∀ r : rt, Copyable ((e.(enum_ty) r))) →
    Copyable (enum_t e).
  Proof.
    iIntros (Hcopy). split; first apply _.
    iIntros (κ π E l r m q ?) "#CTX Hshr Htok".
    rewrite /ty_shr /= enum_shr_unfold /enum_shr_def.
    iDestruct "Hshr" as "(%el & %variant & %variant_ly & -> & %Halg & %Htag & %Hvariant & %Hst & %Hly & Htag & Htag_pad & Hvariant & Htail)".
    set (tag_size := ly_size (it_layout el.(el_tag_it))).
    set (tag_pad_size := el.(el_data_offset) - tag_size).
    set (data_offset := el.(el_data_offset)).
    set (variant_size := ly_size variant_ly).
    pose proof (enum_variant_lookup_in _ _ _ Hvariant) as Hvariant_in.
    pose proof (proj1 (Forall_forall _ _) (el_variants_in_bounds el) _ Hvariant_in) as Hvariant_bound.
    assert (tag_size ≤ data_offset)%nat as Htag_data.
    { rewrite /tag_size /data_offset. apply Nat2Z.inj_le. apply el_tag_before_data. }
    assert (data_offset + variant_size ≤ ly_size el)%nat as Hvariant_bound'.
    { apply Nat2Z.inj_le. rewrite Nat2Z.inj_add /data_offset /variant_size. exact Hvariant_bound. }
    iPoseProof (Fractional_split_big_sepL (λ q, q.[κ])%I 4 with "Htok") as "(%qs & %Hlen_qs & Htoks & Htoks_cl)".
    destruct qs as [|q_tag [|q_tag_pad [|q_variant [|q_tail qs]]]]; simpl in Hlen_qs; try lia.
    destruct qs; simpl in Hlen_qs; try lia.
    iDestruct "Htoks" as "(Htok_tag & Htok_tag_pad & Htok_variant & Htok_tail & _)".
    iMod (copy_shr_acc with "CTX Htag Htok_tag") as "(%ly_tag & >%Hst_tag & >%Hly_tag & %q_tag' & %vtag & Htag_own & Htag_cl)"; first done.
    iMod (copy_shr_acc with "CTX Htag_pad Htok_tag_pad") as "(%ly_tag_pad & >%Hst_tag_pad & >%Hly_tag_pad & %q_tag_pad' & %vtag_pad & Htag_pad_own & Htag_pad_cl)"; first done.
    iMod (copy_shr_acc with "CTX Hvariant Htok_variant") as "(%ly_variant & >%Hst_variant & >%Hly_variant & %q_variant' & %vvariant & Hvariant_own & Hvariant_cl)"; first done.
    iMod (copy_shr_acc with "CTX Htail Htok_tail") as "(%ly_tail & >%Hst_tail & >%Hly_tail & %q_tail' & %vtail & Htail_own & Htail_cl)"; first done.
    set (q' := Qp.min q_tag' (Qp.min q_tag_pad' (Qp.min q_variant' q_tail'))).
    iAssert (▷ (((l ↦{q'} vtag ∗ vtag ◁ᵥ{π, MetaNone} els_lookup_tag e.(enum_els) variant @ int el.(el_tag_it)) ∗
      (l ↦{q'} vtag -∗ l ↦{q_tag'} vtag)) ∗ ⌜length vtag = tag_size⌝))%I with "[Htag_own]" as "Htag_own".
    { iNext. iDestruct "Htag_own" as "(Hl_tag & Htag_own)".
      iDestruct "Htag_own" as "#Htag_own".
      iPoseProof (Fractional_fractional_le (λ q, l ↦{q} vtag)%I q_tag' q' with "Hl_tag") as "(Hl_tag & Htag_q_cl)".
      { unfold q'. etrans; first apply Qp.le_min_l. done. }
      iPoseProof (ty_own_val_has_layout with "Htag_own") as "%Htag_val".
      { simpl. apply syn_type_has_layout_int. done. }
      rewrite /has_layout_val in Htag_val. fold tag_size in Htag_val.
      iSplitL "Hl_tag Htag_q_cl"; last done.
      iSplitL "Hl_tag"; first by iFrame "#∗".
      iIntros "Hl_tag". by iApply "Htag_q_cl". }
    iEval (rewrite bi.later_sep) in "Htag_own".
    iDestruct "Htag_own" as "(Htag_own & >%Htag_val)".
    iEval (rewrite bi.later_sep) in "Htag_own".
    iDestruct "Htag_own" as "(Htag_own & Htag_q_cl)".
    iAssert (▷ ((((l +ₗ tag_size) ↦{q'} vtag_pad ∗ vtag_pad ◁ᵥ{π, MetaNone} .@ uninit (LiteralSynType (enum_tag_padding_ly el))) ∗
      ((l +ₗ tag_size) ↦{q'} vtag_pad -∗ (l +ₗ tag_size) ↦{q_tag_pad'} vtag_pad)) ∗ ⌜length vtag_pad = tag_pad_size⌝))%I with "[Htag_pad_own]" as "Htag_pad_own".
    { iNext. iDestruct "Htag_pad_own" as "(Hl_tag_pad & Htag_pad_own)".
      iDestruct "Htag_pad_own" as "#Htag_pad_own".
      iPoseProof (Fractional_fractional_le (λ q, (l +ₗ tag_size) ↦{q} vtag_pad)%I q_tag_pad' q' with "Hl_tag_pad") as "(Hl_tag_pad & Htag_pad_q_cl)".
      { unfold q'. etrans; first apply Qp.le_min_r. apply Qp.le_min_l. }
      iPoseProof (ty_has_layout with "Htag_pad_own") as "(%tag_pad_ly & %Htag_pad_st & %Htag_pad_val)".
      apply syn_type_has_layout_untyped_inv in Htag_pad_st.
      apply syn_type_has_layout_literal_inv in Htag_pad_st as (-> & _ & _ & _).
      rewrite /has_layout_val /enum_tag_padding_ly /= in Htag_pad_val.
      fold tag_size in Htag_pad_val. fold tag_pad_size in Htag_pad_val.
      change (ly_size {| ly_size := tag_pad_size; ly_align_log := 0 |}) with tag_pad_size in Htag_pad_val.
      iSplitL "Hl_tag_pad Htag_pad_q_cl"; last done.
      iSplitL "Hl_tag_pad"; first by iFrame "#∗".
      iIntros "Hl_tag_pad". by iApply "Htag_pad_q_cl". }
    iEval (rewrite bi.later_sep) in "Htag_pad_own".
    iDestruct "Htag_pad_own" as "(Htag_pad_own & >%Htag_pad_val)".
    iEval (rewrite bi.later_sep) in "Htag_pad_own".
    iDestruct "Htag_pad_own" as "(Htag_pad_own & Htag_pad_q_cl)".
    iAssert (▷ ((((l +ₗ data_offset) ↦{q'} vvariant ∗ vvariant ◁ᵥ{π, MetaNone} e.(enum_r) r @ e.(enum_ty) r) ∗
      ((l +ₗ data_offset) ↦{q'} vvariant -∗ (l +ₗ data_offset) ↦{q_variant'} vvariant)) ∗ ⌜length vvariant = variant_size⌝))%I with "[Hvariant_own]" as "Hvariant_own".
    { iNext. iDestruct "Hvariant_own" as "(Hl_variant & Hvariant_own)".
      iDestruct "Hvariant_own" as "#Hvariant_own".
      iPoseProof (Fractional_fractional_le (λ q, (l +ₗ data_offset) ↦{q} vvariant)%I q_variant' q' with "Hl_variant") as "(Hl_variant & Hvariant_q_cl)".
      { unfold q'. etrans; first apply Qp.le_min_r. etrans; first apply Qp.le_min_r. apply Qp.le_min_l. }
      iPoseProof (ty_own_val_has_layout with "Hvariant_own") as "%Hvariant_val"; first done.
      assert (ly_variant = variant_ly) as -> by by eapply syn_type_has_layout_inj.
      rewrite /has_layout_val in Hvariant_val. fold variant_size in Hvariant_val.
      iSplitL "Hl_variant Hvariant_q_cl"; last done.
      iSplitL "Hl_variant"; first by iFrame "#∗".
      iIntros "Hl_variant". by iApply "Hvariant_q_cl". }
    iEval (rewrite bi.later_sep) in "Hvariant_own".
    iDestruct "Hvariant_own" as "(Hvariant_own & >%Hvariant_val)".
    iEval (rewrite bi.later_sep) in "Hvariant_own".
    iDestruct "Hvariant_own" as "(Hvariant_own & Hvariant_q_cl)".
    iAssert (▷ (((l +ₗ (data_offset + variant_size)%nat) ↦{q'} vtail ∗ vtail ◁ᵥ{π, MetaNone} .@ uninit (LiteralSynType (enum_tail_padding_ly el variant_ly))) ∗
      ((l +ₗ (data_offset + variant_size)%nat) ↦{q'} vtail -∗ (l +ₗ (data_offset + variant_size)%nat) ↦{q_tail'} vtail)))%I with "[Htail_own]" as "Htail_own".
    { iNext. iDestruct "Htail_own" as "(Hl_tail & Htail_own)".
      iDestruct "Htail_own" as "#Htail_own".
      iPoseProof (Fractional_fractional_le (λ q, (l +ₗ (data_offset + variant_size)%nat) ↦{q} vtail)%I q_tail' q' with "Hl_tail") as "(Hl_tail & Htail_q_cl)".
      { unfold q'. etrans; first apply Qp.le_min_r. etrans; first apply Qp.le_min_r. apply Qp.le_min_r. }
      iSplitL "Hl_tail"; first by iFrame "#∗".
      iIntros "Hl_tail". by iApply "Htail_q_cl". }
    iEval (rewrite bi.later_sep) in "Htail_own".
    iDestruct "Htail_own" as "(Htail_own & Htail_q_cl)".
    iModIntro. iExists el. iSplitR.
    { iNext. iPureIntro. by eapply use_enum_layout_alg_Some_inv. }
    iSplitR.
    { iNext. iPureIntro. done. }
    iExists q', (vtag ++ vtag_pad ++ vvariant ++ vtail).
    iSplitL "Htag_own Htag_pad_own Hvariant_own Htail_own".
    { iNext.
      iDestruct "Htag_own" as "(Hl_tag & Htag_own)".
      iDestruct "Htag_pad_own" as "(Hl_tag_pad & Htag_pad_own)".
      iDestruct "Hvariant_own" as "(Hl_variant & Hvariant_own)".
      iDestruct "Htail_own" as "(Hl_tail & Htail_own)".
      rewrite heap_pointsto_app.
      rewrite Htag_val.
      rewrite heap_pointsto_app.
      rewrite Htag_pad_val.
      rewrite shift_loc_assoc_nat.
      replace (tag_size + tag_pad_size)%nat with data_offset by (symmetry; rewrite /tag_pad_size /data_offset Nat.add_comm; apply Nat.sub_add; done).
      rewrite heap_pointsto_app.
      rewrite Hvariant_val.
      rewrite shift_loc_assoc_nat.
      iFrame.
      rewrite /ty_own_val /= enum_own_val_unfold /enum_own_val_def.
      iExists el, variant, variant_ly. do 5 (iSplit; first done).
      rewrite take_app_length'; last lia.
      iSplitL "Htag_own"; first done.
      rewrite drop_app_length'; last lia.
      rewrite take_app_length'; last lia.
      iSplitL "Htag_pad_own"; first done.
      change (el_data_offset el) with data_offset.
      change (ly_size variant_ly) with variant_size.
      replace data_offset with (length (vtag ++ vtag_pad)).
      2: { rewrite length_app Htag_val Htag_pad_val. rewrite /tag_pad_size /data_offset Nat.add_comm. apply Nat.sub_add. done. }
      replace (drop (length (vtag ++ vtag_pad)) (vtag ++ vtag_pad ++ vvariant ++ vtail)) with (vvariant ++ vtail) by (rewrite app_assoc; rewrite drop_app_length'; done).
      rewrite take_app_length'; last lia.
      iSplitL "Hvariant_own"; first done.
      replace (length (vtag ++ vtag_pad) + variant_size)%nat with (length (vtag ++ vtag_pad ++ vvariant)).
      2: { rewrite !length_app Hvariant_val. lia. }
      replace (drop (length (vtag ++ vtag_pad ++ vvariant)) (vtag ++ vtag_pad ++ vvariant ++ vtail)) with vtail by (rewrite !app_assoc; rewrite drop_app_length'; done).
      done. }
    iIntros "Hl".
    iAssert (▷ (l ↦{q'} vtag ∗ (l +ₗ tag_size) ↦{q'} vtag_pad ∗
      (l +ₗ data_offset) ↦{q'} vvariant ∗
      (l +ₗ (data_offset + variant_size)%nat) ↦{q'} vtail))%I with "[Hl]" as "Hparts".
    { iNext.
      rewrite heap_pointsto_app Htag_val.
      rewrite heap_pointsto_app Htag_pad_val.
      rewrite shift_loc_assoc_nat.
      replace (tag_size + tag_pad_size)%nat with data_offset by (symmetry; rewrite /tag_pad_size /data_offset Nat.add_comm; apply Nat.sub_add; done).
      rewrite heap_pointsto_app Hvariant_val.
      rewrite shift_loc_assoc_nat.
      done. }
    iEval (rewrite !bi.later_sep) in "Hparts".
    iDestruct "Hparts" as "(Hl_tag & Hl_tag_pad & Hl_variant & Hl_tail)".
    iPoseProof (bi.later_wand with "Htag_q_cl Hl_tag") as "Hl_tag".
    iPoseProof (bi.later_wand with "Htag_pad_q_cl Hl_tag_pad") as "Hl_tag_pad".
    iPoseProof (bi.later_wand with "Hvariant_q_cl Hl_variant") as "Hl_variant".
    iPoseProof (bi.later_wand with "Htail_q_cl Hl_tail") as "Hl_tail".
    iMod ("Htag_cl" with "Hl_tag") as "Htok_tag".
    iMod ("Htag_pad_cl" with "Hl_tag_pad") as "Htok_tag_pad".
    iMod ("Hvariant_cl" with "Hl_variant") as "Htok_variant".
    iMod ("Htail_cl" with "Hl_tail") as "Htok_tail".
    iApply "Htoks_cl". simpl. iFrame. done.
  Qed.

  Global Instance enum_t_sized {rt} (e : enum rt) :
    TySized (enum_t e).
  Proof.
    econstructor; done.
  Qed.

  Global Program Instance enum_t_dep_lft_morphism {rts rt} deps
      (En : mut_types rts → enum rt) :
    DepEnumTagTyLftMorphism deps (λ x, (En x).(enum_tag_ty)) →
    DepLftMorphism deps (λ x, enum_t (En x)) :=
    λ Htag_tys,
      let Htag_tys := dep_enum_tag_ty_lft_morphism_lft (DepEnumTagTyLftMorphism:=Htag_tys) in
      mk_dep_lft_morph (dep_lft_morph_α Htag_tys) (dep_lft_morph_E Htag_tys)
        (dep_lft_morph_βdeps Htag_tys) _ _.
  Next Obligation.
    iIntros (rts rt deps En Htag_mor Htag_tys x).
    change (lifecycle_lfts (enum_t (En x))) with (ty_lfts (enum_t (En x))).
    rewrite ty_lfts_unfold/=.
    iApply (dep_lft_morph_lfts (dep_enum_tag_ty_lft_morphism_lft (DepEnumTagTyLftMorphism:=Htag_mor))).
  Qed.
  Next Obligation.
    intros rts rt deps En Htag_mor Htag_tys x.
    change (elctx_interp (ty_wf_E (enum_t (En x))) ≡
      (elctx_interp (dep_lft_morph_E (dep_enum_tag_ty_lft_morphism_lft (DepEnumTagTyLftMorphism:=Htag_mor))) ∗
       elctx_interp (dep_wf_E deps x) ∗
       dep_beta_interp (dep_lft_morph_βdeps (dep_enum_tag_ty_lft_morphism_lft (DepEnumTagTyLftMorphism:=Htag_mor))) x)%I).
    rewrite ty_wf_E_unfold/=.
    apply (dep_lft_morph_wf_E (dep_enum_tag_ty_lft_morphism_lft (DepEnumTagTyLftMorphism:=Htag_mor))).
  Qed.

  Lemma ty_has_op_type_enum_canonical {rt} (en : enum rt) variant_ots ot el tag_int :
    use_op_alg en.(enum_els) = Some (EnumOp el variant_ots tag_int) →
    ot = EnumOp el variant_ots tag_int →
    Forall2 (λ tag_ty variant_ot,
      tag_ty.1 = variant_ot.1 ∧
      ty_has_op_type tag_ty.2.(enum_tag_sem_ty) variant_ot.2)
      en.(enum_tag_ty) variant_ots →
    ty_has_op_type (enum_t en) ot.
  Proof.
    intros Hot -> Ha.
    pose proof Hot as Hwf.
    apply use_op_alg_wf in Hwf.
    rewrite ty_has_op_type_unfold. simpl.
    rewrite /is_enum_ot.
    unfold use_op_alg in Hot.
    simpl in Hot.
    unfold syn_type_of_els in Hot.
    simpl in Hot.
    fold use_op_alg in Hot.
    apply bind_Some in Hot as (variant_lys & Hlys & Hot).
    apply bind_Some in Hot as (el' & Halg & Hot).
    apply bind_Some in Hot as (variant_ots' & _ & Hot).
    destruct (decide (enum_tag_int_wf (els_tag_it (enum_els en)) (els_variants (enum_els en)) (els_tag_int (enum_els en)))) as [_|Htag]; last done.
    injection Hot as <- <- <-.
    simpl in Hwf.
    destruct Hwf as (Hnames1 & Hnames2 & Hnodup & Hrange & Hpayload).
    rewrite /enum_tag_ty_has_op_types in Ha.
    split_and!; try done.
    - by rewrite /use_enum_layout_alg Hlys /= Halg.
  Qed.
End enum.

Global Hint Extern 10 (Copyable _) => (refine (enum_t_copyable _ _); intros []; apply _) : typeclass_instances.

Section ne.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Class EnumNonExpansive {rt1 rt2} (F : type rt1 → enum rt2) := {
    enum_ne_els :
      ∀ ty ty' : type rt1, (∀ m, st_of ty m = st_of ty' m) → enum_els (F ty) = enum_els (F ty');
    (* the tag of the variant should not depend on the ty *)
    enum_ne_tag_consistent :
      ∀ ty ty', (F ty).(enum_tag) = (F ty').(enum_tag);
    (* the rt of the variant should not depend on the ty *)
    enum_ne_rt_consistent :
      ∀ ty ty' r, (F ty).(enum_rt) r = (F ty').(enum_rt) r;
    (* the refinement of the variant should not depend on the ty *)
    enum_ne_r_consistent :
      ∀ ty ty' r, rew [RT_rt] (enum_ne_rt_consistent ty ty' r) in (F ty).(enum_r) r = (F ty').(enum_r) r;

    (* the functor on types is non-expansive *)
    enum_ne_ty_dist :
      ∀ r n ty ty',
      TypeDist n ty ty' →
      TypeDist
        n
        (rew [λ x, type x] (enum_ne_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
    (* same for Dist2, for the sharing predicate *)
    (* [enum_ne_ty_dist] and [enum_ne_ty_dist2] are incomparable in strength *)
    enum_ne_ty_dist2 :
      ∀ r n ty ty',
      TypeDist2 n ty ty' →
      TypeDist2
        n
        (rew [λ x, type x] (enum_ne_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
    enum_ne_tag_tys_has_op_type_rel :
      ∀ ty ty',
      ty.(ty_metadata_kind) = ty'.(ty_metadata_kind) →
      (∀ ot, ty_has_op_type ty ot ↔ ty_has_op_type ty' ot) →
      (∀ m : metadata, st_of ty m = st_of ty' m) →
      enum_tag_tys_has_op_type_rel (F ty).(enum_tag_ty) (F ty').(enum_tag_ty);
  }.
  Lemma enum_ne_lookup_tag_consistent {rt1 rt2} (F : type rt1 → enum rt2) ty ty' r :
    EnumNonExpansive F →
    (∀ m, st_of ty m = st_of ty' m) →
    enum_lookup_tag (F ty) r = enum_lookup_tag (F ty') r.
  Proof.
    intros Hne Hd.
    unfold enum_lookup_tag.
    erewrite enum_ne_els; last apply Hd.
    erewrite enum_ne_tag_consistent; done.
  Qed.

  Global Instance enum_ne_const {rt1 rt2} (en : enum rt2) :
    EnumNonExpansive (λ _ : type rt1, en).
  Proof.
    unshelve econstructor.
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
    - intros ???. unfold enum_tag_tys_has_op_type_rel, enum_tag_ty_has_op_type_rel.
      induction (enum_tag_ty en) as [|[variant sem] tag_tys IH]; constructor; done.
  Qed.

  Class EnumContractive {rt1 rt2} (F : type rt1 → enum rt2) := {
    enum_contr_els :
      ∀ ty ty' : type rt1, enum_els (F ty) = enum_els (F ty');
    (* the tag of the variant should not depend on the ty *)
    enum_contr_tag_consistent :
      ∀ ty ty', (F ty).(enum_tag) = (F ty').(enum_tag);
    (* the rt of the variant should not depend on the ty *)
    enum_contr_rt_consistent :
      ∀ ty ty' r, (F ty).(enum_rt) r = (F ty').(enum_rt) r;
    (* the refinement of the variant should not depend on the ty *)
    enum_contr_r_consistent :
      ∀ ty ty' r, rew [RT_rt] (enum_contr_rt_consistent ty ty' r) in (F ty).(enum_r) r = (F ty').(enum_r) r;

    enum_contr_ty_dist :
      ∀ r n ty ty',
      TypeDist2 n ty ty' →
      TypeDist
        n
        (rew [λ x, type x] (enum_contr_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
    (* same for Dist2, for the sharing predicate *)
    (* [enum_contr_ty_dist] and [enum_contr_ty_dist2] are incomparable in strength *)
    enum_contr_ty_dist2 :
      ∀ r n ty ty',
      TypeDistLater2 n ty ty' →
      TypeDist2
        n
        (rew [λ x, type x] (enum_contr_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
    enum_contr_tag_tys_has_op_type_rel :
      ∀ ty ty',
      enum_tag_tys_has_op_type_rel (F ty).(enum_tag_ty) (F ty').(enum_tag_ty);
  }.
  Lemma enum_contractive_lookup_tag_consistent {rt1 rt2} (F : type rt1 → enum rt2) ty ty' r :
    EnumContractive F →
    enum_lookup_tag (F ty) r = enum_lookup_tag (F ty') r.
  Proof.
    intros Hne.
    unfold enum_lookup_tag.
    erewrite enum_contr_els.
    erewrite enum_contr_tag_consistent; done.
  Qed.

  Instance enum_t_ne {rt1 rt2} (F : type rt1 → enum rt2) :
    EnumNonExpansive F →
    TypeNonExpansive (λ ty : type rt1, enum_t (F ty)).
  Proof.
    intros Hen. constructor.
    - done.
    - simpl. intros. erewrite enum_ne_els; done.
    (*- apply ty_lft_morphism_of_direct.*)
      (*rewrite /=ty_lfts_unfold/=.*)
      (*rewrite /=ty_wf_E_unfold.*)
      (*apply enum_ne_lft_mor.*)
    - rewrite !ty_has_op_type_unfold.
      intros ty ty' Hst ? Hot ot . simpl.
      assert (∀ ot, ty_has_op_type ty ot ↔ ty_has_op_type ty' ot) as Hot_ty.
      { intros ot'. rewrite !ty_has_op_type_unfold. apply Hot. }
      unfold is_enum_ot.
      destruct ot as [ | | | | ? ? | ? ? ? | ly | ]; try done.
      + split.
        * intros (Halg & Htag_int & Hwf & Hvariant). split_and!.
          -- erewrite <-enum_ne_els; done.
          -- rewrite Htag_int. erewrite <-enum_ne_els; done.
          -- done.
          -- eapply enum_tag_ty_has_op_types_transfer_forall2; last exact Hvariant.
             by apply enum_ne_tag_tys_has_op_type_rel.
        * intros (Halg & Htag_int & Hwf & Hvariant). split_and!.
          -- erewrite enum_ne_els; done.
          -- rewrite Htag_int. erewrite enum_ne_els; done.
          -- done.
          -- eapply enum_tag_ty_has_op_types_transfer_forall2; last exact Hvariant.
             apply enum_ne_tag_tys_has_op_type_rel.
             { done. }
             { intro; apply iff_sym, Hot_ty. }
             { done. }
      + split; intros (el & Halg & ->); exists el; split; [erewrite <-enum_ne_els| |erewrite enum_ne_els|]; done.
    - simpl. eauto.
    - intros n ty ty' Hd.
      iIntros (π r m v). rewrite /ty_own_val/=.
      rewrite enum_own_val_unfold /enum_own_val_def.
      do 3 f_equiv. intros variant. f_equiv. intros variant_ly. do 5 f_equiv.
      { apply enum_ne_els. apply Hd. }
      { rewrite (enum_ne_tag_consistent ty ty'). done. }
      { simpl. f_equiv.
        eapply (enum_ne_ty_dist r) in Hd.
        destruct Hd as [Hst _ _ _].
        rewrite -Hst.
        generalize (enum_ne_rt_consistent ty ty' r) as Heq.
        destruct Heq. done. }
      do 3 f_equiv.
      { apply enum_ne_els. apply Hd. }
      eapply (enum_ne_ty_dist r) in Hd.
      destruct Hd as [_ _ Hv _].
      rewrite -Hv.
      rewrite -(enum_ne_r_consistent ty ty' r).
      generalize (enum_ne_rt_consistent ty ty' r); intros Heq.
      destruct Heq. done.
    - intros n ty ty' Hd.
      iIntros (κ π r m l). rewrite /ty_shr/=.
      rewrite enum_shr_unfold /enum_shr_def.
      do 3 f_equiv. intros variant. f_equiv. intros variant_ly. do 5 f_equiv.
      { apply enum_ne_els. apply Hd. }
      { rewrite (enum_ne_tag_consistent ty ty'). done. }
      { simpl. f_equiv.
        eapply (enum_ne_ty_dist2 r) in Hd.
        destruct Hd as [Hst _ _ _].
        rewrite -Hst.
        generalize (enum_ne_rt_consistent ty ty' r) as Heq.
        destruct Heq. done. }
      do 4 f_equiv.
      { apply enum_ne_els. apply Hd. }
      eapply (enum_ne_ty_dist2 r) in Hd.
      destruct Hd as [_ _ _ Hshr].
      rewrite -Hshr.
      rewrite -(enum_ne_r_consistent ty ty' r).
      generalize (enum_ne_rt_consistent ty ty' r); intros Heq.
      destruct Heq. done.
  Qed.

  Instance enum_t_contr {rt1 rt2} (F : type rt1 → enum rt2) :
    EnumContractive F →
    TypeContractive (λ ty : type rt1, enum_t (F ty)).
  Proof.
    intros Hen. constructor.
    - done.
    - simpl. intros. erewrite enum_contr_els; done.
    (*- apply ty_lft_morphism_of_direct.*)
      (*rewrite /=ty_lfts_unfold/=.*)
      (*rewrite /=ty_wf_E_unfold.*)
      (*apply enum_contr_lft_mor.*)
    - rewrite !ty_has_op_type_unfold.
      intros ty ty' ot . simpl.
      unfold is_enum_ot.
      destruct ot as [ | | | | ? ? | ? ? ? | ly | ]; try done.
      + split.
        * intros (Halg & Htag_int & Hwf & Hvariant). split_and!.
          -- erewrite <-enum_contr_els; done.
          -- rewrite Htag_int. erewrite <-enum_contr_els; done.
          -- done.
          -- eapply enum_tag_ty_has_op_types_transfer_forall2; last exact Hvariant.
             by apply enum_contr_tag_tys_has_op_type_rel.
        * intros (Halg & Htag_int & Hwf & Hvariant). split_and!.
          -- erewrite enum_contr_els; done.
          -- rewrite Htag_int. erewrite enum_contr_els; done.
          -- done.
          -- eapply enum_tag_ty_has_op_types_transfer_forall2; last exact Hvariant.
             by apply enum_contr_tag_tys_has_op_type_rel.
      + split; intros (el & Halg & ->); exists el; split; [erewrite <-enum_contr_els| |erewrite enum_contr_els|]; done.
    - simpl. eauto.
    - intros n ty ty' Hd.
      iIntros (π r m v). rewrite /ty_own_val/=.
      rewrite enum_own_val_unfold /enum_own_val_def.
      do 3 f_equiv. intros variant. f_equiv. intros variant_ly. do 5 f_equiv.
      { apply enum_contr_els. }
      { rewrite (enum_contr_tag_consistent ty ty'). done. }
      { simpl. f_equiv.
        eapply (enum_contr_ty_dist r) in Hd.
        destruct Hd as [Hst _ _ _].
        rewrite -Hst.
        generalize (enum_contr_rt_consistent ty ty' r) as Heq.
        destruct Heq. done. }
      do 3 f_equiv.
      { apply enum_contr_els. }
      eapply (enum_contr_ty_dist r) in Hd.
      destruct Hd as [_ _ Hv _].
      rewrite -Hv.
      rewrite -(enum_contr_r_consistent ty ty' r).
      generalize (enum_contr_rt_consistent ty ty' r); intros Heq.
      destruct Heq. done.
    - intros n ty ty' Hd.
      iIntros (κ π r m l). rewrite /ty_shr/=.
      rewrite enum_shr_unfold /enum_shr_def.
      do 3 f_equiv. intros variant. f_equiv. intros variant_ly. do 5 f_equiv.
      { apply enum_contr_els. }
      { rewrite (enum_contr_tag_consistent ty ty'). done. }
      { simpl. f_equiv.
        eapply (enum_contr_ty_dist2 r) in Hd.
        destruct Hd as [Hst _ _ _].
        rewrite -Hst.
        generalize (enum_contr_rt_consistent ty ty' r) as Heq.
        destruct Heq. done. }
      do 4 f_equiv.
      { apply enum_contr_els. }
      eapply (enum_contr_ty_dist2 r) in Hd.
      destruct Hd as [_ _ _ Hshr].
      rewrite -Hshr.
      rewrite -(enum_contr_r_consistent ty ty' r).
      generalize (enum_contr_rt_consistent ty ty' r); intros Heq.
      destruct Heq. done.
  Qed.

End ne.
