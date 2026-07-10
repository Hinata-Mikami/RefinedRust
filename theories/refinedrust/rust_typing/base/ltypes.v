From Equations Require Import Equations.
From iris.bi Require Export fractional.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants na_invariants.
From radium Require Export proofmode notation.
From radium Require Import derived.
From lrust.lifetime Require Export frac_borrow.
From refinedrust Require Export lty.
From refinedrust Require Import int.
From refinedrust Require Export hlist.
From refinedrust Require Export base lft_contexts gvar_refinement type uninit_def.
From refinedrust Require Import options.

Section ltype_def.
  Context `{!typeGS Σ}.

  Import EqNotations.

  (** ** We define derived versions on top that expose the refinement type as an index.
     This is the variant that will be actually used by the type system. *)
  Record ltype (rt : RT) := mk_ltype {
    ltype_lty : lty;
    ltype_rt_agree : lty_rt ltype_lty = rt;
    ltype_lty_wf : lty_wf ltype_lty;
  }.
  Arguments ltype_lty {_}.
  Arguments ltype_rt_agree {_}.
  Arguments ltype_rt_agree : simpl never.

  Record enum_ltype_variant := mk_enum_ltype_variant {
    eltv_tag : var_name;
    eltv_rt : RT;
    eltv_ltype : ltype eltv_rt;
    eltv_rfn : eltv_rt;
  }.

  Definition enum_ltype_variant_lty (v : enum_ltype_variant) : enum_lty_variant :=
    mk_enum_lty_variant
      v.(eltv_tag)
      v.(eltv_rt)
      v.(eltv_ltype).(ltype_lty)
      v.(eltv_rfn).

  Definition enum_ltype_variant_tag_compat {rt : RT} (en : enum rt)
      (r : rt) (v : enum_ltype_variant) : Prop :=
    enum_tag en r = Some v.(eltv_tag).

  Definition enum_ltype_variant_payload_compat {rt : RT} (en : enum rt)
      (r : rt) (v : enum_ltype_variant) : Prop :=
    ∃ Heq : RT_rt (enum_rt en r) = RT_rt v.(eltv_rt),
      rew [id] Heq in enum_r en r = v.(eltv_rfn).

  Definition enum_ltype_variant_compat {rt : RT} (en : enum rt)
      (r : rt) (v : enum_ltype_variant) : Prop :=
    enum_ltype_variant_tag_compat en r v ∧
    enum_ltype_variant_payload_compat en r v.

  Lemma ltype_rt_agree' {rt : RT} (lt : ltype rt) :
    RT_rt (lty_rt (ltype_lty lt)) = RT_rt rt.
  Proof.
    by rewrite ltype_rt_agree.
  Qed.

  (* uses PI *)
  Lemma mk_ltype_irrel {rt} lt Heq1 Heq2 Hwf1 Hwf2 :
    mk_ltype rt lt Heq1 Hwf1 = mk_ltype rt lt Heq2 Hwf2.
  Proof.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.

  Program Definition OfTy {rt} (ty : type rt) : ltype rt := {|
    ltype_lty := OfTyLty ty;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Arguments OfTy : simpl never.
  Lemma OfTy_ltype_lty_eq {rt} (ty : type rt) :
    ltype_lty (OfTy ty) = OfTyLty ty.
  Proof. done. Qed.
  Global Typeclasses Opaque OfTy.

  Definition canonical_enum_ltype_variant {rt : RT} (en : enum rt) (r : rt) :
      enum_ltype_variant :=
    mk_enum_ltype_variant
      (enum_tag' en r)
      (enum_rt en r)
      (OfTy (enum_ty en r))
      (enum_r en r).

  Definition interp_enum_ltype_variant {rt : RT} (en : enum rt)
      (ov : option enum_ltype_variant) (r : rt) : enum_ltype_variant :=
    match ov with
    | Some v =>
        if decide (enum_tag en r = Some v.(eltv_tag))
        then v
        else canonical_enum_ltype_variant en r
    | None => canonical_enum_ltype_variant en r
    end.

  Lemma interp_enum_ltype_variant_None {rt : RT} (en : enum rt) r :
    interp_enum_ltype_variant en None r = canonical_enum_ltype_variant en r.
  Proof. done. Qed.

  Lemma interp_enum_ltype_variant_Some_match {rt : RT} (en : enum rt) v r
      (Htag : enum_tag en r = Some v.(eltv_tag)) :
    interp_enum_ltype_variant en (Some v) r = v.
  Proof. rewrite /interp_enum_ltype_variant decide_True //. Qed.

  Lemma interp_enum_ltype_variant_Some_mismatch {rt : RT} (en : enum rt) v r
      (Htag : enum_tag en r ≠ Some v.(eltv_tag)) :
    interp_enum_ltype_variant en (Some v) r = canonical_enum_ltype_variant en r.
  Proof. rewrite /interp_enum_ltype_variant decide_False //. Qed.

  Lemma canonical_enum_ltype_variant_lty {rt : RT} (en : enum rt) r :
    enum_ltype_variant_lty (canonical_enum_ltype_variant en r) =
      canonical_enum_lty_variant en r.
  Proof. rewrite /canonical_enum_ltype_variant /canonical_enum_lty_variant /enum_ltype_variant_lty /=. done. Qed.

  Lemma interp_enum_ltype_variant_lty {rt : RT} (en : enum rt) variant r :
    enum_ltype_variant_lty (interp_enum_ltype_variant en variant r) =
      interp_enum_lty_variant en (enum_ltype_variant_lty <$> variant) r.
  Proof.
    destruct variant as [v | ]; simpl.
    - destruct (decide (enum_tag en r = Some v.(eltv_tag))); simpl;
        rewrite ?canonical_enum_ltype_variant_lty //.
    -apply canonical_enum_ltype_variant_lty.
  Qed.

  Program Definition AliasLtype (rt : RT) (st : syn_type) (l : loc) : ltype rt := {|
    ltype_lty := AliasLty rt st l;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Global Typeclasses Opaque AliasLtype.

  Program Definition BlockedLtype {rt} (ty : type rt) (κ : lft) : ltype rt := {|
    ltype_lty := BlockedLty ty κ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Global Typeclasses Opaque BlockedLtype.

  Program Definition ShrBlockedLtype {rt} (ty : type rt) (κ : lft) : ltype rt := {|
    ltype_lty := ShrBlockedLty ty κ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Global Typeclasses Opaque ShrBlockedLtype.

  Program Definition MutLtype {rt} (lt : ltype rt) (κ : lft) : ltype (prodRT (place_rfnRT rt) gnameRT)%type := {|
    ltype_lty := MutLty (lt.(ltype_lty)) κ;
  |}.
  Next Obligation.
    by intros rt [lty <-].
  Qed.
  Next Obligation.
    by intros rt [lty <- Hwf].
  Qed.
  Arguments MutLtype : simpl never.
  Global Typeclasses Opaque MutLtype.

  Program Definition ShrLtype {rt} (lt : ltype rt) (κ : lft) : ltype (place_rfnRT rt) := {|
    ltype_lty := ShrLty (lt.(ltype_lty)) κ;
  |}.
  Next Obligation.
    by intros rt [lty <-].
  Qed.
  Next Obligation.
    by intros rt [lty <- Hwf].
  Qed.
  Arguments ShrLtype : simpl never.
  Global Typeclasses Opaque ShrLtype.

  Lemma ltype_rt_agree_hlist {rts} (lts : hlist ltype rts) :
    (lty_rt <$> (@ltype_lty +c<$> lts)) = rts.
  Proof.
    induction rts as [ | rt rts IH]; simpl.
    - inv_hlist lts. done.
    - inv_hlist lts. intros [lt <-] lts'.
      simpl.
      f_equiv. apply IH.
  Qed.
  Lemma struct_ltype_rt_agree {rts : list RT} (lts : hlist ltype rts) : plistRT (lty_rt <$> (@ltype_lty +c<$> lts)) = plistRT rts.
  Proof.
    f_equiv. apply ltype_rt_agree_hlist.
  Qed.

  #[universes(polymorphic)]
  Program Definition StructLtype {rts : list RT} (lts : hlist ltype rts) (sls : struct_layout_spec) : ltype (plistRT rts) := {|
    ltype_lty := StructLty (hcmap (@ltype_lty) lts) sls;
  |}.
  Next Obligation.
    intros rts lts sls. simpl.
    f_equiv. apply ltype_rt_agree_hlist.
  Qed.
  Next Obligation.
    intros rts lts sls. simpl.
    induction rts as [ | rt rts IH]; inv_hlist lts; simpl; first done.
    intros [lt <- Hwf] lts. split; first done. apply IH.
  Qed.
  Arguments StructLtype : simpl never.
  Global Typeclasses Opaque StructLtype.

  Program Definition ArrayLtype {rt : RT} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) : ltype (listRT (place_rfnRT rt)) := {|
    ltype_lty := @ArrayLty _ _ rt def len (map (λ '(i, lt), (i, lt.(ltype_lty))) lts);
  |}.
  Next Obligation.
    intros rt def len lts. simpl. done.
  Qed.
  Next Obligation.
    intros rt def len lts. simpl.
    induction lts as [ | [i lt] lts IH]; simpl; first done.
    split; last done. split_and!; [ apply ltype_lty_wf | rewrite !ltype_rt_agree// ].
  Qed.
  Global Arguments ArrayLtype : simpl never.
  Global Typeclasses Opaque ArrayLtype.

  Program Definition EnumLtype {rt : RT} (en : enum rt)
      (variant : option enum_ltype_variant) : ltype rt := {|
    ltype_lty := EnumLty en (enum_ltype_variant_lty <$> variant);
  |}.
  Next Obligation.
    intros rt en variant. simpl. done.
  Qed.
  Next Obligation.
    intros rt en [variant | ]; simpl.
    - split; [apply ltype_lty_wf | apply ltype_rt_agree].
    - done.
  Qed.
  Global Typeclasses Opaque EnumLtype.
  Global Arguments ArrayLtype : simpl never.

  Program Definition OpenedLtype {rt_cur rt_inner rt_full : RT} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ) : ltype rt_cur := {|
    ltype_lty := OpenedLty (ltype_lty lt_cur) (ltype_lty lt_inner) (ltype_lty lt_full) Cpre Cpost;
  |}.
  Next Obligation.
    intros rt_cur rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost. simpl.
    rewrite ltype_rt_agree; done.
  Qed.
  Next Obligation.
    intros rt_cur rt_inner rt_full [lt_cur <- Hcur] [lt_inner <- Hinner] [lt_full <- Hfull] Cpre Cpost; simpl.
    eauto.
  Qed.
  Global Typeclasses Opaque OpenedLtype.
  Global Arguments OpenedLtype : simpl never.

  Program Definition CoreableLtype {rt_full} (κs : list lft) (lt_full : ltype rt_full) : ltype rt_full := {|
    ltype_lty := CoreableLty κs (ltype_lty lt_full);
  |}.
  Next Obligation.
    intros rt_full κ lt_full. simpl. apply ltype_rt_agree.
  Qed.
  Next Obligation.
    intros rt_full κ [lt_full <- ?]. simpl. eauto.
  Qed.
  Global Arguments CoreableLtype : simpl never.
  Global Typeclasses Opaque CoreableLtype.

  Program Definition ShadowedLtype {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) : ltype rt_full := {|
    ltype_lty := ShadowedLty (ltype_lty lt_cur) r_cur (ltype_lty lt_full);
  |}.
  Next Obligation.
    intros rt_cur rt_full lt_cur r_cur lt_full. simpl. apply ltype_rt_agree.
  Qed.
  Next Obligation.
    intros rt_cur rt_full lt_cur r_cur lt_full. split_and!; [apply ltype_lty_wf.. | ].
    apply ltype_rt_agree.
  Qed.
  Global Arguments ShadowedLtype : simpl never.
  Global Typeclasses Opaque ShadowedLtype.

  Program Definition OpenedNaLtype {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
      (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ) : ltype rt_cur := {|
    ltype_lty := OpenedNaLty (ltype_lty lt_cur) (ltype_lty lt_inner) Cpre Cpost;
  |}.
  Next Obligation.
    intros rt_cur lt_cur Cpre Cpost. simpl.
    rewrite ltype_rt_agree. done.
  Qed.
  Next Obligation.
    intros rt_cur rt_inner [lt_cur <- Hcur] [lt_inner <- Hinner] Cpre Cpost; simpl.
    eauto.
  Qed.
  Global Typeclasses Opaque OpenedNaLtype.
  Global Arguments OpenedNaLtype : simpl never.

  Import EqNotations.
  Definition ltype_own_pre (core : bool) {rt} (lt : ltype rt) : bor_kind → thread_id → place_rfn rt → loc → iProp Σ :=
    λ k π r l, lty_own_pre core lt.(ltype_lty) k π (rew <- [place_rfnRT] lt.(ltype_rt_agree) in r) l.

  Local Definition ltype_own_core_def := @ltype_own_pre true.
  Local Definition ltype_own_core_aux : seal (@ltype_own_core_def). Proof. by eexists. Qed.
  Definition ltype_own_core := ltype_own_core_aux.(unseal).
  Lemma ltype_own_core_unseal : @ltype_own_core = ltype_own_core_def.
  Proof. rewrite -ltype_own_core_aux.(seal_eq) //. Qed.
  Global Arguments ltype_own_core {_}.
  Global Typeclasses Opaque ltype_own_core.

  Local Definition ltype_own_def := @ltype_own_pre false.
  Local Definition ltype_own_aux : seal (@ltype_own_def). Proof. by eexists. Qed.
  Definition ltype_own := ltype_own_aux.(unseal).
  Lemma ltype_own_unseal : @ltype_own = ltype_own_def.
  Proof. rewrite -ltype_own_aux.(seal_eq) //. Qed.
  Global Arguments ltype_own {_}.
  Global Typeclasses Opaque ltype_own.

  Definition ltype_st {rt} (lt : ltype rt) : syn_type := lty_st lt.(ltype_lty).
  Global Arguments ltype_st : simpl never.

  Program Definition ltype_core {rt} (lt : ltype rt) : ltype rt := {|
    ltype_lty := lty_core lt.(ltype_lty);
  |}.
  Next Obligation.
    intros rt lt. rewrite lty_core_rt_eq. apply ltype_rt_agree.
  Qed.
  Next Obligation.
    intros rt [lt <- Hwf]; simpl. by apply lty_core_wf.
  Qed.
  Global Arguments ltype_core : simpl never.
  Global Typeclasses Opaque ltype_core.

  Definition enum_ltype_variant_core (v : enum_ltype_variant) : enum_ltype_variant :=
    mk_enum_ltype_variant
      v.(eltv_tag)
      v.(eltv_rt)
      (ltype_core v.(eltv_ltype))
      v.(eltv_rfn).


  Section induction.
    Local Fixpoint make_ltype_hlist (lts : list lty) : Forall_cb lty_wf lts → hlist ltype (fmap lty_rt lts) :=
      match lts as lts' return Forall_cb lty_wf lts' → hlist ltype (fmap lty_rt lts') with
      | [] => λ _, +[]
      | lt :: lts => λ Hwf,
          (mk_ltype _ lt eq_refl (proj1 Hwf)) +:: make_ltype_hlist lts (proj2 Hwf)
      end.
    Local Lemma make_ltype_hlist_lift lts (Hwf : Forall_cb lty_wf lts) (P : ∀ rt, ltype rt → Prop) :
      (∀ (lt : lty) (Helt : lt ∈ lts) (Hwf : lty_wf lt), P (lty_rt lt) (mk_ltype _ lt eq_refl Hwf)) →
      (∀ lt0, lt0 ∈ hzipl _ (make_ltype_hlist lts Hwf) → P (projT1 lt0) (projT2 lt0)).
    Proof.
      induction lts as [ | lt lts IH]; simpl; intros Ha.
      - intros ? []%elem_of_nil.
      - intros [rt lt0]. rewrite elem_of_cons.
        intros [[= -> ->] | Hel].
        { apply Ha. apply elem_of_cons; eauto. }
        eapply IH; last done.
        intros. eapply Ha. apply elem_of_cons; eauto.
    Qed.
    Local Lemma make_ltype_hlist_map_proj_eq lts Hwf :
      (@ltype_lty +c<$> make_ltype_hlist lts Hwf) = lts.
    Proof.
      induction lts as [ | lt lts IH]; first done.
      simpl. by rewrite IH.
    Qed.

    Local Fixpoint make_ltype_list {rt} (lts : list (nat * lty)) : Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt) lts → list (nat * ltype rt) :=
      match lts as lts' return Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt) lts' → list (nat * ltype rt) with
      | [] => λ _, []
      | (i, lt) :: lts => λ Hwf,
          (i, mk_ltype _ lt (proj2 (proj1 Hwf)) (proj1 (proj1 Hwf))) :: make_ltype_list lts (proj2 Hwf)
      end.
    Local Lemma make_ltype_list_lift {rt} lts (Hwf : Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt) lts) (P : ∀ rt, ltype rt → Prop) :
      (∀ rt (lt : lty) Heq1 Heq2 Hwf1 Hwf2, P rt (mk_ltype rt lt Heq1 Hwf1) → P rt (mk_ltype rt lt Heq2 Hwf2)) →
      (∀ (i : nat) (lt : lty) (Helt : (i, lt) ∈ lts) (Hwf : lty_wf lt), P (lty_rt lt) (mk_ltype _ lt eq_refl Hwf)) →
      (∀ i lt0, (i, lt0) ∈ make_ltype_list lts Hwf → P _ lt0).
    Proof.
      intros P_irrel Ha. induction lts as [ | [i lt] lts IH]; simpl.
      - intros ? ? []%elem_of_nil.
      - intros i0 lt0. rewrite elem_of_cons. intros [[= -> ->] | Hel]; first last.
        { eapply IH; last done. intros. eapply Ha. apply elem_of_cons; by right. }
        destruct Hwf as [[Hwf Heq] ?].
        clear IH.
        unshelve opose proof* (Ha i lt) as Ha.
        { done. } { apply elem_of_cons; by left. }
        subst rt. eapply P_irrel; done.
    Qed.
    Local Lemma make_ltype_list_map_proj_eq {rt} lts Hwf :
      (map (λ '(i, lt), (i, ltype_lty lt)) (make_ltype_list (rt:=rt) lts Hwf)) = lts.
    Proof.
      induction lts as [ | [i lt] lts IH]; simpl; first done.
      f_equiv. apply IH.
    Qed.

    Lemma ltype_induction (P : ∀ rt, ltype rt → Prop) :
      (∀ (rt : RT) (t : type rt) κ, P _ (BlockedLtype t κ)) →
      (∀ (rt : RT) (t : type rt) κ, P _ (ShrBlockedLtype t κ)) →
      (∀ (rt : RT) (t : type rt), P _ (OfTy t)) →
      (∀ (rt : RT) (st : syn_type) (l : loc), P _ (AliasLtype rt st l)) →
      (∀ (rt : RT) (lt : ltype rt), P _ lt → ∀ κ, P _ (MutLtype lt κ)) →
      (∀ (rt : RT) (lt : ltype rt), P _ lt → ∀ κ, P _ (ShrLtype lt κ)) →
      (∀ (rts : list RT) (lts : hlist ltype rts),
        (∀ lt, lt ∈ hzipl rts lts → P _ (projT2 lt)) →
        ∀ sls : struct_layout_spec, P _ (StructLtype lts sls)) →
      (∀ (rt : RT) (def : type rt) (len : nat) (lts : list (nat * ltype rt)),
        (∀ i lt, (i, lt) ∈ lts → P _ lt) →
        P _ (ArrayLtype def len lts)) →
      (∀ (rt : RT) (en : enum rt) (variant : option enum_ltype_variant),
        match variant with
        | Some v => P _ v.(eltv_ltype)
        | None => True
        end → P _ (EnumLtype en variant)) →
      (∀ (rt_cur rt_inner rt_full : RT) (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
        (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ),
        P _ lt_cur → P _ lt_inner → P _ lt_full →
        P _ (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ (rt_full : RT) κs (lt_full : ltype rt_full), P _ lt_full → P _ (CoreableLtype κs lt_full)) →
      (∀ (rt_cur rt_full : RT) (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full),
        P _ lt_cur → P _ lt_full → P _ (ShadowedLtype lt_cur r_cur lt_full)) →
      (∀ (rt_cur rt_inner : RT) (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
        (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ),
        P _ lt_cur → P _ lt_inner →
        P _ (OpenedNaLtype lt_cur lt_inner Cpre Cpost)) →
      ∀ (rt : RT) (lt : ltype rt), P _ lt.
    Proof.
      intros Hblocked Hshrblocked Hofty Halias Hmut Hshr Hstruct Harr Hen Hopened Hcoreable Hshadow Hopened_na.

      assert (P_irrel:
        ∀ rt (lt : lty) Heq1 Heq2 Hwf1 Hwf2, P rt (mk_ltype rt lt Heq1 Hwf1) → P rt (mk_ltype rt lt Heq2 Hwf2)).
      { intros rt lt <- Heq2. rewrite (UIP_refl _ _ Heq2).
        intros Hwf1 Hwf2. rewrite (proof_irrelevance _ Hwf1 Hwf2). done. }

      intros rt [lt <- Hwf].
      induction lt as [ | | | | lt IH κ | lt IH κ | lts IH sls | rt def len lts IH | rt en variant IH | rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost IH_cur IH_inner IH_full | κ lt_full IH | rt_cur lt_cur r_cur lt_full IH_cur IH_full | rt_inner lt_cur lt_inner Cpre Cpost IH_cur IH_inner ] using lty_induction; simpl.
      - eapply P_irrel. apply Hblocked.
      - eapply P_irrel. apply Hshrblocked.
      - eapply P_irrel. apply Hofty.
      - eapply P_irrel. apply Halias.
      - specialize (Hmut _ _ (IH Hwf)). eapply P_irrel. apply Hmut.
      - specialize (Hshr _ _ (IH Hwf)). eapply P_irrel. apply Hshr.
      - specialize (make_ltype_hlist_lift lts Hwf P IH) as IH'.
        specialize (Hstruct _ _ IH' sls). clear -Hstruct P_irrel.
        move: Hstruct. unfold StructLtype.
        generalize (StructLtype_obligation_2 (lty_rt <$> lts) (make_ltype_hlist lts Hwf) sls) as Hwf'.
        generalize (StructLtype_obligation_1 (lty_rt <$> lts) (make_ltype_hlist lts Hwf) sls) as Heq.
        rewrite make_ltype_hlist_map_proj_eq.
        simpl. intros <- Hwf'.
        eapply P_irrel.
      - simpl in Hwf.
        specialize (make_ltype_list_lift lts Hwf P P_irrel IH) as IH2.
        specialize (Harr _ def len _ IH2).
        move: Harr. rewrite /ArrayLtype.
        generalize (ArrayLtype_obligation_2 _ def len (make_ltype_list lts Hwf)).
        generalize (ArrayLtype_obligation_1 _ def len (make_ltype_list lts Hwf)).
        rewrite make_ltype_list_map_proj_eq.
        simpl. intros <- Hwf'. eapply P_irrel.
      - (* enum *)
        destruct variant as [variant | ]; simpl in Hwf, IH.
        + destruct variant as [tag rte lte re].
          destruct Hwf as [Hwf Hrt].
          specialize (IH Hwf).
          assert (Hv : P _ (mk_ltype _ lte Hrt Hwf)).
          { destruct Hrt. exact IH. }
          set (ltypev := mk_enum_ltype_variant
            tag rte (mk_ltype _ lte Hrt Hwf) re).
          specialize (Hen rt en (Some ltypev) Hv).
          subst ltypev.
          unfold EnumLtype in Hen.
          unfold enum_ltype_variant_lty in Hen.
          simpl in Hen.
          eapply P_irrel.
          apply Hen.
        + specialize (Hen rt en None I).
          eapply P_irrel.
          apply Hen.
      - destruct Hwf as (Heq1 & Heq2 & Hwf_cur & Hwf_inner & Hwf_full); subst.
        specialize (Hopened _ _ _ _ _ _ Cpre Cpost (IH_cur Hwf_cur) (IH_inner Hwf_inner) (IH_full Hwf_full)).
        eapply P_irrel. eapply Hopened.
      - specialize (Hcoreable _ κ _ (IH Hwf)).
        eapply P_irrel. eapply Hcoreable.
      - destruct Hwf as (Hwf_cur & Hwf_full & <-).
        specialize (Hshadow _ _ _ r_cur _ (IH_cur Hwf_cur) (IH_full Hwf_full)).
        eapply P_irrel. eapply Hshadow.
      - destruct Hwf as (Heq & Hwf_cur & Hwf_inner); subst.
        specialize (Hopened_na _ _ _ _ Cpre Cpost (IH_cur Hwf_cur) (IH_inner Hwf_inner)).
        eapply P_irrel. eapply Hopened_na.
    Qed.
  End induction.

  (** Unfolding equations for [ltype] *)
  Definition ltype_own_type := ∀ rt, ltype rt → bor_kind → thread_id → place_rfn rt → loc → iProp Σ.

  Definition UninitLtype st := OfTy (uninit st).
  Definition shr_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rt} (lt : ltype rt) κ k π (r : place_rfn (place_rfn rt)) l :=
        (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
         loc_in_bounds l 0 ly.(ly_size) ∗
        match k with
        | Owned =>
            ∃ (r' : place_rfn rt), place_rfn_interp_owned r r' ∗
            |={lftE}=>  ∃ (l' : loc), ptr_loc_own l l' ∗
            rec _ lt (Shared κ) π r' l'
        | Uniq κ' γ' =>
            have_creds ∗
            place_rfn_interp_mut r γ' ∗
            |={lftE}=> &pin{κ'}
              [∃ (r' : place_rfn rt), gvar_auth γ' r' ∗ |={lftE}=>  ∃ (l' : loc), ptr_loc_own l l' ∗ rec_core _ lt (Shared κ) π r' l']
              (∃ (r' : place_rfn rt), gvar_auth γ' r' ∗ |={lftE}=>  ∃ (l' : loc), ptr_loc_own l l' ∗ rec _ lt (Shared κ) π r' l')
        | Shared κ' =>
            ∃ (r' : place_rfn rt),
            place_rfn_interp_shared r r' ∗
            (* the update is also over the fractional borrow to deal with timelessness *)
            □ |={lftE}=> ∃ (vi : val) (li : loc),
            &frac{κ'} (λ q, l ↦{q} vi) ∗
            ⌜val_decodes_to_loc vi li⌝ ∗
            (* no intersection here, as we also don't do that for the type interpretation *)
            ▷ rec _ lt (Shared κ) π r' li
        end)%I.

  Definition mut_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rt} (lt : ltype rt) (κ : lft) (k : bor_kind) (π : thread_id) (r : place_rfn (place_rfn rt * gname)%type) (l : loc) : iProp Σ :=
    (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
       loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned =>
          (* it's fine to existentially quantify here over the gvar_obs, since
            the outer can actually tell us about it. Keep in mind that the gvar here can actually
            change if we write under nested places. *)
          ∃ (γ : gname) (r' : place_rfn rt) ,
          place_rfn_interp_owned r (r', γ) ∗
          (* TODO layout requirements on l' here? *)
          |={lftE}=>  ∃ l' : loc, ptr_loc_own l l' ∗ (rec _ lt (Uniq κ γ) π r' l')
      | Uniq κ' γ' =>
          have_creds ∗
          place_rfn_interp_mut r γ' ∗
          |={lftE}=> &pin{κ'}
            [∃ (r' : (place_rfn rt) * gname),
              gvar_auth γ' r' ∗
              (* update here to be compatible with ofty *)
              |={lftE}=>
              ∃ (l' : loc), ptr_loc_own l l' ∗
              rec_core _ lt (Uniq κ r'.2) π r'.1 l'
            ]
            (∃ (r' : (place_rfn rt) * gname),
              gvar_auth γ' r' ∗
              (* update here to be compatible with ofty *)
              |={lftE}=>
              ∃ (l' : loc), ptr_loc_own l l' ∗
              rec _ lt (Uniq κ r'.2) π r'.1 l')
      | Shared κ' =>
        (∃ r' γ, place_rfn_interp_shared r (r', γ) ∗
        (* the update is also over the fractional borrow to deal with timelessness *)
        □ |={lftE}=> ∃ (vi : val) (li : loc),
          &frac{κ'}(λ q', l ↦{q'} vi) ∗
          ⌜val_decodes_to_loc vi li⌝ ∗
          (* later is for contractiveness, the update for timelessness *)
          ▷ rec _ lt (Shared (κ⊓κ')) π r' li)%I
      end)%I.

  Definition struct_make_uninit_ltype (ly : layout) : sigT (λ rt : RT, (ltype rt * place_rfn rt)%type) :=
    existT (unit : RT) (UninitLtype (LiteralSynType ly), PlaceIn ()).

  Definition struct_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    {rts : list RT}
    (lts : hlist ltype rts) (sls : struct_layout_spec)
    (k : bor_kind) (π : thread_id) (r : place_rfn (plist place_rfnRT rts)) (l : loc) : iProp Σ :=
    ∃ sl : struct_layout,
    ⌜use_struct_layout_alg sls = Some sl⌝ ∗
    ⌜length (sls_fields sls) = length rts⌝ ∗
    ⌜l `has_layout_loc` sl⌝ ∗
    loc_in_bounds l 0 (sl.(ly_size)) ∗
    match k with
    | Owned =>
        ∃ r' : plist place_rfnRT rts, place_rfn_interp_owned r r' ∗ |={lftE}=>
          [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
            ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
            rec _ (projT2 ty).1 Owned π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))
    | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        (* We change the ownership to Owned false, because we can't push the borrow down in this formulation of products.
          The cost of this is that we need an update here (to get congruence rules for ltype_eq),
          which propagates to all the other Uniq cases of other ltypes. *)
        |={lftE}=> &pin{κ}
          [∃ (r' : plist place_rfnRT rts),
            gvar_auth γ r' ∗ |={lftE}=>
            [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
              rec_core _ (projT2 ty).1 Owned π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))
          ]
          (∃ (r' : plist place_rfnRT rts),
            gvar_auth γ r' ∗ |={lftE}=>
            [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
              rec _ (projT2 ty).1 Owned π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))
          )
    | Shared κ =>
        (∃ r', place_rfn_interp_shared r r' ∗
          (* update needed to make the unfolding equation work *)
          □ |={lftE}=>
            [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r') struct_make_uninit_ltype,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
              rec _ (projT2 ty).1 (Shared κ) π (projT2 ty).2 (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))%I
    end.

  Definition array_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    (rt : RT) (def : type rt) (len : nat) (lts : list (nat * ltype rt))
    (k : bor_kind) (π : thread_id) (r : place_rfn (list (place_rfn rt))) (l : loc) : iProp Σ :=
    ∃ ly,
      ⌜syn_type_has_layout (ty_syn_type def MetaNone) ly⌝ ∗
      ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 (ly.(ly_size) * len) ∗
      (*⌜Forall (λ '(i, _), i < len) lts⌝ ∗*)
      match k with
      | Owned =>
          ∃ r' : list (place_rfn rt), place_rfn_interp_owned r r' ∗
          |={lftE}=>
          (⌜length r' = len⌝ ∗
          [∗ list] i ↦ lt; r0 ∈ (interpret_iml (OfTy def) len lts); r',
              ⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ rec _ lt Owned π r0 (offset_loc l ly i))
      | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        |={lftE}=> &pin{κ}
          [∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              [∗ list] i ↦ lt; r0 ∈ interpret_iml (OfTy def) len lts; r',
                ⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ rec_core _ lt Owned π r0 (offset_loc l ly i))]
          (∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              [∗ list] i ↦ lt; r0 ∈ interpret_iml (OfTy def) len lts; r',
                ⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ rec _ lt Owned π r0 (offset_loc l ly i)))
      | Shared κ =>
          ∃ r', place_rfn_interp_shared r r' ∗
            □ |={lftE}=> (⌜length r' = len⌝ ∗ [∗ list] i ↦ lt; r0 ∈ interpret_iml (OfTy def) len lts; r',
                  ⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ rec _ lt (Shared κ) π r0 (offset_loc l ly i))
      end.


  Definition enum_ltype_own
    (rec : ltype_own_type)
    (rec_core : ltype_own_type)
    (rt : RT) (en : enum rt) (variant : option enum_ltype_variant)
    (k : bor_kind) (π : thread_id) (r : place_rfn rt) (l : loc) : iProp Σ :=
      ∃ el,
      ⌜use_enum_layout_alg en.(enum_els) = Some el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(el_size) ∗
      let tag_ly := it_layout el.(el_tag_it) in
      let tag_size := ly_size tag_ly in
      let data_offset := el.(el_data_offset) in
      match k with
      | Owned =>
        ∃ r' : rt, place_rfn_interp_owned r r' ∗
        let v := interp_enum_ltype_variant en variant r' in
        |={lftE}=> ∃ variant_ly,
          ⌜enum_ltype_variant_tag_compat en r' v⌝ ∗
          ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
          ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
          lty_of_ty_own (int el.(el_tag_it)) Owned π
            (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
          lty_of_ty_own (uninit (LiteralSynType (Layout (data_offset - tag_size) 0))) Owned π
            (PlaceIn ()) (l +ₗ tag_size) ∗
          rec _ v.(eltv_ltype) Owned π (PlaceIn v.(eltv_rfn)) (l +ₗ data_offset) ∗
          lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - data_offset - ly_size variant_ly) 0))) Owned π
            (PlaceIn ()) (l +ₗ data_offset +ₗ ly_size variant_ly)
      | Shared κ =>
        ∃ r' : rt, place_rfn_interp_shared r r' ∗
        let v := interp_enum_ltype_variant en variant r' in
        □ |={lftE}=> ∃ variant_ly,
          ⌜enum_ltype_variant_tag_compat en r' v⌝ ∗
          ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
          ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
          lty_of_ty_own (int el.(el_tag_it)) (Shared κ) π
            (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
          lty_of_ty_own (uninit (LiteralSynType (Layout (data_offset - tag_size) 0))) (Shared κ) π
            (PlaceIn ()) (l +ₗ tag_size) ∗
          rec _ v.(eltv_ltype) (Shared κ) π (PlaceIn v.(eltv_rfn)) (l +ₗ data_offset) ∗
          lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - data_offset - ly_size variant_ly) 0))) (Shared κ) π
            (PlaceIn ()) (l +ₗ data_offset +ₗ ly_size variant_ly)
      | Uniq κ γ =>
        let enum_uniq_body (rec' : ltype_own_type) :=
          (∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=> ∃ variant_ly,
          let v := interp_enum_ltype_variant en variant r' in
          ⌜enum_ltype_variant_compat en r' v⌝ ∗
          ⌜enum_variant_lookup el.(el_variants) v.(eltv_tag) = Some variant_ly⌝ ∗
          ⌜syn_type_has_layout (ltype_st v.(eltv_ltype)) variant_ly⌝ ∗
          lty_of_ty_own (int el.(el_tag_it)) Owned π
            (PlaceIn (els_lookup_tag en.(enum_els) v.(eltv_tag))) l ∗
          lty_of_ty_own (uninit (LiteralSynType (Layout (data_offset - tag_size) 0))) Owned π
            (PlaceIn ()) (l +ₗ tag_size) ∗
          rec' _ v.(eltv_ltype) Owned π (PlaceIn v.(eltv_rfn)) (l +ₗ data_offset) ∗
          lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - data_offset - ly_size variant_ly) 0))) Owned π
            (PlaceIn ()) (l +ₗ data_offset +ₗ ly_size variant_ly))%I in
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        |={lftE}=> pinned_bor κ (enum_uniq_body rec_core) (enum_uniq_body rec)
      end.

  Definition opened_ltype_own
      (rec : ltype_own_type) (rec_core : ltype_own_type)
      {rt_cur rt_inner rt_full : RT}
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ)
      (k : bor_kind) (π : thread_id) (r : place_rfn rt_cur) (l : loc) : iProp Σ :=
    ∃ ly, ⌜use_layout_alg (ltype_st lt_cur) = Some ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 (ly_size ly) ∗
      ⌜ltype_st lt_cur = ltype_st lt_inner⌝ ∗
      ⌜ltype_st lt_inner = ltype_st lt_full⌝ ∗

      match k with
      | Owned =>
          ltype_own lt_cur Owned π r l ∗
          (* once we have restored to [lt_inner], we can fold to [lt_full] again *)
          logical_step lftE
          (∀ (r : rt_inner) (r' : rt_full) (κs : list lft),
            (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
            (* directly hand out Cpost. We don't need to wait to get tokens from closing borrows etc. *)
            Cpost r r' ∗
            (lft_dead_list κs -∗
             ltype_own lt_inner Owned π (PlaceIn r) l ={lftE}=∗
             ltype_own_core lt_full Owned π (PlaceIn r') l))
      | Uniq κ γ =>
        ltype_own lt_cur Owned π r l ∗
          (* we will execute this VS when closing the invariant, after having already stratified [lt_cur].
             At that point, we will know [lt_cur] is unblockable to [lt_inner] after the set of lifetimes [κs] is dead *)
        logical_step lftE
          (∀ (own_lt_cur' : thread_id → rt_inner → loc → iProp Σ) (κs : list lft) (r : rt_inner) (r' : rt_full),
            (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
            ([∗ list] κ' ∈ κs, κ' ⊑ κ) -∗
            own_lt_cur' π r l -∗

            (* the ownership of [lt_cur'] needs to be shiftable to the _core_ of [lt_inner];
              this is required for closing the borrow and for proving that it can be unblocked to lt_full
                (which is needed for showing the shift to Coreable) *)
            (□ (lft_dead_list κs -∗ own_lt_cur' π r l ={lftE}=∗
              ltype_own_core lt_inner Owned π (PlaceIn r) l)) ={lftE}=∗

            Cpost r r' ∗
            gvar_obs γ r' ∗
            (lft_dead_list κs -∗ gvar_obs γ r' ={lftE}=∗
              ltype_own_core lt_full (Uniq κ γ) π (PlaceIn r') l))
      | Shared κ =>
          False
      end.

  Definition coreable_ltype_own (rec : ltype_own_type) (rec_core : ltype_own_type)
      {rt_full} (κs : list lft) (lt_full : ltype rt_full)
      (k : bor_kind) (π : thread_id) (r : place_rfn rt_full) (l : loc) : iProp Σ :=
    ∃ ly, ⌜syn_type_has_layout (ltype_st lt_full) ly⌝ ∗
    ⌜l `has_layout_loc` ly⌝ ∗
    loc_in_bounds l 0 (ly_size ly) ∗
    match k with
    | Owned =>
        lft_dead_list κs ={lftE}=∗ rec_core _ lt_full Owned π r l
    | Uniq κ' γ =>
        place_rfn_interp_mut r γ ∗
        (lft_dead_list κs -∗ place_rfn_interp_mut r γ ={lftE}=∗ rec_core _ lt_full (Uniq κ' γ) π r l)
    | Shared κ =>
        rec_core _ lt_full (Shared κ) π r l
    end.

  Definition shadowed_ltype_own (rec : ltype_own_type) (rec_core : ltype_own_type)
    {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full)
    (k : bor_kind) (π : thread_id) (r : place_rfn rt_full) (l : loc) : iProp Σ :=
    rec _ lt_cur k π (r_cur) l ∗
    rec _ lt_full k π r l.

  Definition opened_na_ltype_own
      (rec : ltype_own_type) (rec_core : ltype_own_type)
      {rt_cur rt_inner : RT}
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
      (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ)
      (k : bor_kind) (π : thread_id) (r : place_rfn rt_cur) (l : loc) : iProp Σ :=
    ∃ ly, ⌜use_layout_alg (ltype_st lt_cur) = Some ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 (ly_size ly) ∗
      ⌜ltype_st lt_cur = ltype_st lt_inner⌝ ∗
      match k with
      | Owned =>
            ltype_own lt_cur Owned π r l ∗
            logical_step lftE
            (∀ (r : rt_inner),
              Cpre r -∗
              ltype_own lt_inner Owned π (PlaceIn r) l ={lftE ∪ shrE}=∗ Cpost r)
      | _ => False
    end.

  Lemma ltype_own_pre_ofty_unfold {rt} (ty : type rt) (core : bool) k π r l :
    ltype_own_pre core (OfTy ty) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof.
    rewrite /ltype_own_pre. simp lty_own_pre. rewrite /lty_of_ty_own.
    move: r.
    generalize (ltype_rt_agree (OfTy ty)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.
  Lemma ltype_own_ofty_unfold {rt} (ty : type rt) k π r l :
    ltype_own (OfTy ty) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof. rewrite ltype_own_unseal. apply ltype_own_pre_ofty_unfold. Qed.
  Lemma ltype_own_core_ofty_unfold {rt} (ty : type rt) k π r l :
    ltype_own_core (OfTy ty) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof. rewrite ltype_own_core_unseal. apply ltype_own_pre_ofty_unfold. Qed.

  Lemma ltype_own_pre_alias_unfold (rt : RT) (st : syn_type) (p : loc) (core : bool) k π r l :
    ltype_own_pre core (AliasLtype rt st p) k π r l ≡ alias_lty_own rt st p k π r l.
  Proof.
    rewrite /ltype_own_pre. simp lty_own_pre. rewrite /alias_lty_own.
    destruct k; [ | done..].
    done.
  Qed.
  Lemma ltype_own_alias_unfold (rt : RT) (st : syn_type) (p : loc) k π r l :
    ltype_own (AliasLtype rt st p) k π r l ≡ alias_lty_own rt st p k π r l.
  Proof. rewrite ltype_own_unseal. apply ltype_own_pre_alias_unfold. Qed.
  Lemma ltype_own_core_alias_unfold (rt : RT) (st : syn_type) (p : loc) k π r l :
    ltype_own_core (AliasLtype rt st p) k π r l ≡ alias_lty_own rt st p k π r l.
  Proof. rewrite ltype_own_core_unseal. apply ltype_own_pre_alias_unfold. Qed.

  Lemma ltype_own_blocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own (BlockedLtype ty κ) k π r l ≡ blocked_lty_own ty κ k π r l.
  Proof.
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre. simp lty_own_pre.
    rewrite /blocked_lty_own.
    move: r.
    generalize (ltype_rt_agree (BlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.
  Lemma ltype_own_core_blocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own_core (BlockedLtype ty κ) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof.
    rewrite ltype_own_core_unseal /ltype_own_core_def /ltype_own_pre. simp lty_own_pre.
    rewrite /lty_of_ty_own.
    move: r.
    generalize (ltype_rt_agree (BlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.

  Lemma ltype_own_shrblocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own (ShrBlockedLtype ty κ) k π r l ≡ shr_blocked_lty_own ty κ k π r l.
  Proof.
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre. simp lty_own_pre.
    rewrite /shr_blocked_lty_own.
    move: r.
    generalize (ltype_rt_agree (ShrBlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.
  Lemma ltype_own_core_shrblocked_unfold {rt} (ty : type rt) κ k π r l :
    ltype_own_core (ShrBlockedLtype ty κ) k π r l ≡ lty_of_ty_own ty k π r l.
  Proof.
    rewrite ltype_own_core_unseal /ltype_own_core_def /ltype_own_pre. simp lty_own_pre.
    rewrite /shr_blocked_lty_own.
    move: r.
    generalize (ltype_rt_agree (ShrBlockedLtype ty κ)). simpl.
    intros Heq. rewrite (UIP_refl _ _ Heq).
    intros r. done.
  Qed.

  Lemma ltype_own_pre_shr_ref_unfold {rt} (lt : ltype rt) (core : bool) κ k π r l :
    ltype_own_pre core (ShrLtype lt κ) k π r l ≡ shr_ltype_own (@ltype_own_pre core) (@ltype_own_core) lt κ k π r l.
  Proof.
    (* NOTE: pay attention to unfold also the core, otherwise we get into trouble with generalizing below *)
    rewrite /shr_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    move: r.
    generalize (ltype_rt_agree (ShrLtype lt κ)).
    generalize (ltype_rt_agree lt). simpl.
    intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros r. repeat f_equiv; done.
  Qed.
  Lemma ltype_own_shr_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own (ShrLtype lt κ) k π r l ≡ shr_ltype_own (@ltype_own) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_shr_ref_unfold. Qed.
  Lemma ltype_own_core_shr_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own_core (ShrLtype lt κ) k π r l ≡ shr_ltype_own (@ltype_own_core) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite {1 2}ltype_own_core_unseal. apply ltype_own_pre_shr_ref_unfold. Qed.

  Lemma ltype_own_pre_mut_ref_unfold {rt} (lt : ltype rt) (core : bool) κ k π r l :
    ltype_own_pre core (MutLtype lt κ) k π r l ≡ mut_ltype_own (@ltype_own_pre core) (@ltype_own_core) lt κ k π r l.
  Proof.
    (* NOTE: pay attention to unfold also the core, otherwise we get into trouble with generalizing below *)
    rewrite /mut_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    move: r.
    generalize (ltype_rt_agree (MutLtype lt κ)).
    generalize (ltype_rt_agree lt). simpl.
    intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros r. repeat (first [fast_done | f_equiv]).
  Qed.
  Lemma ltype_own_mut_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own (MutLtype lt κ) k π r l ≡ mut_ltype_own (@ltype_own) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_mut_ref_unfold. Qed.
  Lemma ltype_own_core_mut_ref_unfold {rt} (lt : ltype rt) κ k π r l :
    ltype_own_core (MutLtype lt κ) k π r l ≡ mut_ltype_own (@ltype_own_core) (@ltype_own_core) lt κ k π r l.
  Proof. rewrite {1 2}ltype_own_core_unseal. apply ltype_own_pre_mut_ref_unfold. Qed.

  Lemma StructLtype_StructLty_rfn_eq (rts : list RT) (lts : hlist ltype rts) :
    plist place_rfnRT rts = plist (λ lt : lty, place_rfn (lty_rt lt)) (@ltype_lty +c<$> lts).
  Proof.
    induction rts as [ | ?? IH]; inv_hlist lts; simpl; first done.
    intros x xl'. f_equiv.
    - rewrite (ltype_rt_agree x); done.
    - apply IH.
  Qed.
  Section structlty.
    (** The unfolding for StructLtype requires a bit of work. We first bring the big_sepL into a shape where we can use [big_sepL_fmap]. *)

    Local Definition lty_own_pre_sig (core : bool) (lt : sigT (λ lt : lty, place_rfn (lty_rt lt))) (k : bor_kind) (π : thread_id) (l : loc) : iProp Σ :=
      lty_own_pre core (projT1 lt) k π (projT2 lt) l.

    Local Definition map_fun : sigT (λ rt : RT, (ltype rt * place_rfn rt)%type) → sigT (λ lt : lty, place_rfn (lty_rt lt)) :=
      (λ x, existT (ltype_lty (projT2 x).1) (rew <- [place_rfnRT] ltype_rt_agree (projT2 x).1 in (projT2 x).2)).


    Local Lemma StructLtype_fmap_eq {rts : list RT} (lts : hlist ltype rts) (r : plist place_rfnRT rts) (Heq: plist (λ lt : lty, place_rfn (lty_rt lt)) (@ltype_lty +c<$> lts) = plist place_rfnRT rts):
      (pzipl (hcmap (@ltype_lty) lts) (rew <-[id] Heq in r)) = fmap map_fun (hpzipl rts lts r).
    Proof.
      induction rts as [ | rt rts IH] in lts, r, Heq |-*.
      { inv_hlist lts. done. }
      inv_hlist lts. intros lt lts Heq2.
      simpl.
      f_equiv.
      - simpl. unfold map_fun. f_equiv.
        simpl. generalize (ltype_rt_agree lt) as Heq3.
        clear.
        intros.
        rewrite phd_rew_commute.
        { rewrite Heq3 //. }
        2: { apply StructLtype_StructLty_rfn_eq. }
        intros Heq4.
        clear. move: Heq4 Heq3.
        generalize (ltype_lty lt) as lt' => lt'.
        intros ? <-. rewrite (UIP_refl _ _ Heq4) //.
      - specialize (IH lts (ptl r)). unfold fmap in IH. rewrite -IH.
        { rewrite -StructLtype_StructLty_rfn_eq. done. }
        intros Heq3.
        f_equiv.
        destruct r as [r tl]. simpl.
        rewrite ptl_rew_commute.
        { rewrite -StructLtype_StructLty_rfn_eq. done. }
        2: { rewrite ltype_rt_agree. done. }
        intros Heq4.
        simpl. clear. move: tl Heq4 Heq3.
        generalize (@ltype_lty +c<$> lts) as l => l.
        intros tl. destruct Heq4.
        intros Heq3. rewrite (UIP_refl _ _ Heq3). done.
    Qed.

    Local Lemma StructLtype_big_sepL_fmap' {rts : list RT} (sl : struct_layout) (lts : hlist ltype rts) (r : plist place_rfnRT rts) r'
      (Heq2: plist (λ lt : lty, place_rfn (lty_rt lt)) (@ltype_lty +c<$> lts) = plist place_rfnRT rts)
      (l : loc) (π : thread_id) k core :
      r' = rew <-[id] Heq2 in r →
      ([∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (pzipl (hcmap (@ltype_lty) lts) r')
          (λ ly : layout, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())),
        (∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
        lty_own_pre core (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx sl.(sl_members) i))) ⊣⊢

      ([∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts lts r)
          (λ ly : layout, existT (unit : RT) (UninitLtype (LiteralSynType ly), PlaceIn tt)),
        ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ltype_st (projT2 ty).1) ly⌝ ∗
       lty_own_pre core (ltype_lty (projT2 ty).1) k π (rew <-[place_rfnRT] ltype_rt_agree (projT2 ty).1 in (projT2 ty).2) (l +ₗ offset_of_idx sl.(sl_members) i)).
    Proof.
      intros ->.
      rewrite StructLtype_fmap_eq.
      rewrite (pad_struct_ext _ _ _ (λ ly : layout, map_fun (existT (unit : RT) (UninitLtype (LiteralSynType ly), PlaceIn ())))).
      2: { intros. unfold map_fun. simpl. f_equiv.
        match goal with
        |- PlaceIn _ = rew <- [_] ?Heq in _ => generalize Heq
        end.
        simpl. intros Heq3.
        rewrite (UIP_refl _ _ Heq3). done. }
      rewrite (pad_struct_fmap _ _ _ (λ _, _)).
      simpl. fold map_fun.
      rewrite big_sepL_fmap. done.
    Qed.
  End structlty.

  Lemma ltype_own_pre_struct_unfold {rts : list RT} (lts : hlist ltype rts) (sls : struct_layout_spec) (core : bool) k π r l :
    ltype_own_pre core (StructLtype lts sls) k π r l ≡ struct_ltype_own (@ltype_own_pre core) (@ltype_own_core) lts sls k π r l.
  Proof.
    unfold ltype_own_pre. simpl.
    (*struct_ltype_rt_agree*)
    generalize (ltype_rt_agree (StructLtype lts sls)); intros Heq.
    apply RT_eq_iff in Heq as Heq2.
    destruct Heq2 as (Heq2 & _).
    simpl in *.
    Set Printing Coercions.

    simp lty_own_pre. fold (lty_rt).
    replace (rew <- [λ rt, place_rfn (RT_rt rt)] Heq in r) with ((rew <- [place_rfn] Heq2 in r)); first last.
    { clear.
      apply rew_swap'.
      normalize_dep_rt_goal_prepare.
      specialize (ltype_rt_agree_hlist lts) as Heq3.
      move: Heq3.
      generalize (lty_rt <$> (@ltype_lty +c<$> lts)).
      intros. subst.
      normalize_dep_rt_goal. }
    clear Heq.
    rewrite /struct_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.

    assert (Heq3 : plist (place_rfn ∘ λ lt : lty, lty_rt lt) (@ltype_lty +c<$> lts) = plist (λ rt, place_rfnRT rt) rts).
    { rewrite -Heq2.
      clear. induction lts as [ | rt lt rts lts IH]; simpl; first done.
      rewrite IH. done. }

    repeat f_equiv.
    { rewrite length_hcmap. done. }
    (* TODO deduplicate all this stuff *)
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & Hb)".

        iExists (rew [id]Heq3 in r').
        iSplitL "Hrfn".
        { normalize_dep_rt_goal. }
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew <-[id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
    }
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & #Hb)".
        iExists (rew [id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        iModIntro. iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
      - iIntros "(%r' & Hrfn & #Hb)".
        iExists (rew <-[id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        iModIntro. iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
    }
    { normalize_dep_rt_goal. }
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew [id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew <-[id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
    }
    { setoid_rewrite big_sepL_P_eq.
      iSplit.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew [id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | |]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
      - iIntros "(%r' & Hrfn & Hb)".
        iExists (rew <-[id]Heq3 in r').
        iSplitL "Hrfn". { normalize_dep_rt_goal. }
        iMod "Hb" as "Hb". iModIntro.
        unshelve rewrite StructLtype_big_sepL_fmap'; [ | done | | ]. 2: {
          iApply (big_sepL_mono with "Hb").
          clear. iIntros (? (rt & lt & r'') ?). simpl. done. }
        normalize_dep_rt_goal.
    }
  Qed.

  Lemma ltype_own_struct_unfold {rts : list RT} (lts : hlist ltype rts) (sls : struct_layout_spec) k π r l :
    ltype_own (StructLtype lts sls) k π r l ≡ struct_ltype_own (@ltype_own) (@ltype_own_core) lts sls k π r l.
  Proof.
    rewrite ?ltype_own_unseal.
    rewrite /ltype_own_def ltype_own_pre_struct_unfold. done.
  Qed.
  Lemma ltype_own_core_struct_unfold {rts : list RT} (lts : hlist ltype rts) (sls : struct_layout_spec) k π r l :
    ltype_own_core (StructLtype lts sls) k π r l ≡ struct_ltype_own (@ltype_own_core) (@ltype_own_core) lts sls k π r l.
  Proof.
    rewrite {1 2} ltype_own_core_unseal.
    rewrite /ltype_own_core_def ltype_own_pre_struct_unfold. done.
  Qed.

  Local Lemma ArrayLtype_big_sepL_fmap {rt} (lts : list (ltype rt)) (r : list (place_rfn rt)) core π k ly st l :
    length lts = length r →
    ([∗ list] i↦ ty ∈ zip (map ltype_lty lts) r,
      ∃ Heq : RT_rt (lty_rt ty.1) = RT_rt rt, ⌜lty_st ty.1 = st⌝ ∗
        lty_own_pre core ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)) ⊣⊢
    ([∗ list] i↦ lt;r' ∈ lts;r, ⌜ltype_st lt = st⌝ ∗
        lty_own_pre core (ltype_lty lt) k π (rew <- [place_rfnRT] ltype_rt_agree lt in r') (l offset{ly}ₗ i)).
  Proof.
    intros Hlen.
    assert (⌜length lts = length lts⌝ ⊣⊢ (True : iProp Σ))%I as Heq.
    { iSplit; eauto. }
    rewrite big_sepL2_alt.
    rewrite -Hlen. rewrite Heq. rewrite left_id.
    clear Heq.
    rewrite zip_fmap_l big_sepL_fmap.
    f_equiv; last done. intros ? [lt r']. simpl.
    iSplit.
    { iIntros "(%Heq2 & $ & Hb)".
      Set Printing Coercions.
      iApply (lty_own_pre_rfn_eq with "Hb").
      apply rew_swap'.
      generalize (ltype_rt_agree lt) => Heq3.
      normalize_dep_rt_goal_prepare.
      generalize (lty_rt (ltype_lty lt)).
      normalize_dep_rt_goal. }
    { iIntros "($ & Hb)".
      iExists (ltype_rt_agree' lt).
      iApply (lty_own_pre_rfn_eq with "Hb").
      apply rew_swap.
      generalize (ltype_rt_agree lt) => Heq3.
      normalize_dep_rt_goal_prepare.
      generalize (lty_rt (ltype_lty lt)).
      normalize_dep_rt_goal. }
  Qed.
  Local Lemma OfTy_ltype_lty {rt} (ty : type rt) :
    ltype_lty (OfTy ty) = OfTyLty ty.
  Proof. done. Qed.
  Lemma ltype_own_pre_array_unfold {rt : RT} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) (core : bool) k π r l :
    ltype_own_pre core (ArrayLtype def len lts) k π r l ≡ array_ltype_own (@ltype_own_pre core) (@ltype_own_core) rt def len lts k π r l.
  Proof.
    rewrite /array_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree (ArrayLtype def len lts)).
    fold lty_rt. simpl.
    intros Heq1. rewrite (UIP_refl _ _ Heq1). cbn.
    do 6 f_equiv.
    (*f_equiv.*)
    (*{ rewrite Forall_fmap. iPureIntro. apply Forall_iff. intros []; done. }*)
    f_equiv.
    - do 3 f_equiv.
      { done. }
      f_equiv.
      apply sep_equiv_proper => Hlen.
      rewrite big_sepL_P_eq.
      rewrite -OfTy_ltype_lty.
      Set Printing Coercions.
      rewrite interpret_iml_fmap ArrayLtype_big_sepL_fmap //.
      rewrite length_interpret_iml //.
    - do 3 f_equiv.
      { done. }
      do 2 f_equiv.
      apply sep_equiv_proper => Hlen.
      rewrite big_sepL_P_eq.
      rewrite -OfTy_ltype_lty interpret_iml_fmap ArrayLtype_big_sepL_fmap //.
      rewrite length_interpret_iml//.
    - do 6 f_equiv. all: f_equiv.
      all: f_equiv.
      all: apply sep_equiv_proper => Hlen.
      all: repeat f_equiv; rewrite big_sepL_P_eq.
      all: rewrite -OfTy_ltype_lty interpret_iml_fmap ArrayLtype_big_sepL_fmap//.
      all: rewrite length_interpret_iml//.
  Qed.

  Lemma ltype_own_array_unfold {rt : RT} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) k π r l :
    ltype_own (ArrayLtype def len lts) k π r l ≡ array_ltype_own (@ltype_own) (@ltype_own_core) rt def len lts k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_array_unfold. Qed.
  Lemma ltype_own_core_array_unfold {rt : RT} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) k π r l :
    ltype_own_core (ArrayLtype def len lts) k π r l ≡ array_ltype_own (@ltype_own_core) (@ltype_own_core) rt def len lts k π r l.
  Proof. rewrite {1 2} ltype_own_core_unseal. apply ltype_own_pre_array_unfold. Qed.

  Lemma ltype_own_pre_enum_unfold {rt : RT} (en : enum rt)
      (variant : option enum_ltype_variant) (core : bool) k π r l :
    ltype_own_pre core (EnumLtype en variant) k π r l ≡
      enum_ltype_own (@ltype_own_pre core) (@ltype_own_core) rt en variant k π r l.
  Proof.
    rewrite /enum_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    destruct variant as [[tag rte lte re] | ].
    - destruct lte as [lte <- Hwf]. simpl.
      generalize (ltype_rt_agree (EnumLtype en (Some (mk_enum_ltype_variant tag _ (mk_ltype _ lte eq_refl Hwf) re)))).
      fold lty_rt. simpl.
      intros Heq1. rewrite (UIP_refl _ _ Heq1). cbn.
      rewrite /enum_lty_variant_tag_compat /enum_ltype_variant_tag_compat
        /enum_lty_variant_compat /enum_ltype_variant_compat
        /enum_lty_variant_payload_compat /enum_ltype_variant_payload_compat.
      do 5 f_equiv.
      destruct k; simpl; do 6 f_equiv.
      all: destruct (decide (enum_tag en a0 = Some tag)); simpl.
      all: repeat f_equiv.
      all: try done.
      all: generalize (ltype_rt_agree (OfTy (enum_ty en a0))); simpl; intros Heq2; try rewrite (UIP_refl _ _ Heq2).
      all: (generalize (ltype_rt_agree (mk_ltype _ lte eq_refl Hwf)); simpl; intros Heq3; try rewrite (UIP_refl _ _ Heq3)).
      all: iSplit.
      all: iIntros "H".
      (*all: simpl.*)
      all: first [iDestruct "H" as "(%Heq & H)"; rewrite (UIP_refl _ _ Heq) |
                  iDestruct "H" as "H"; iExists eq_refl].
      all: done.
    - rewrite /interp_enum_ltype_variant /OfTy /=.
      generalize (ltype_rt_agree (EnumLtype en None)).
      fold lty_rt. simpl.
      intros Heq1. rewrite (UIP_refl _ _ Heq1). cbn.
      destruct k; simpl; do 5 f_equiv.
      all: repeat f_equiv.
      all: try done.
      all: try (rewrite /enum_lty_variant_tag_compat /enum_ltype_variant_tag_compat
        /enum_lty_variant_compat /enum_ltype_variant_compat
        /enum_lty_variant_payload_compat /enum_ltype_variant_payload_compat; done).
      all: iSplit.
      all: iIntros "H".
      + iDestruct "H" as "(%Heq & H)". rewrite (UIP_refl _ _ Heq).
        iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iExists eq_refl. iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iDestruct "H" as "(%Heq & H)". rewrite (UIP_refl _ _ Heq).
        iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iExists eq_refl. iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iDestruct "H" as "(%Heq & H)". rewrite (UIP_refl _ _ Heq).
        iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iExists eq_refl. iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iDestruct "H" as "(%Heq & H)". rewrite (UIP_refl _ _ Heq).
        iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
      + iExists eq_refl. iApply (lty_own_pre_rfn_eq with "H"). normalize_dep_rt_goal.
  Qed.

  Lemma ltype_own_enum_unfold {rt : RT} (en : enum rt)
      (variant : option enum_ltype_variant) k π r l :
    ltype_own (EnumLtype en variant) k π r l ≡
      enum_ltype_own (@ltype_own) (@ltype_own_core) rt en variant k π r l.
  Proof. rewrite ?ltype_own_unseal. apply ltype_own_pre_enum_unfold. Qed.
  Lemma ltype_own_core_enum_unfold {rt : RT} (en : enum rt)
      (variant : option enum_ltype_variant) k π r l :
    ltype_own_core (EnumLtype en variant) k π r l ≡
      enum_ltype_own (@ltype_own_core) (@ltype_own_core) rt en variant k π r l.
  Proof. rewrite {1 2} ltype_own_core_unseal. apply ltype_own_pre_enum_unfold. Qed.

  Lemma ltype_own_opened_unfold {rt_cur rt_inner rt_full : RT} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ) k π r l :
    ltype_own (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) k π r l ≡ opened_ltype_own (@ltype_own) (@ltype_own_core) lt_cur lt_inner lt_full Cpre Cpost k π r l.
  Proof.
    rewrite /opened_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_cur).
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree lt_inner).
    generalize (ltype_rt_agree (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost)).
    simpl.
    intros Heq1 Heq2 Heq3 Heq4. move : Cpre Cpost r.
    move: Heq1 Heq2 Heq3 Heq4.
    intros <- <- <-.
    intros Heq Cpre Cpost r. specialize (UIP_refl _ _ Heq) => ->. clear Heq.
    repeat f_equiv.
    - done.
    - done.
    - iSplit.
      + iIntros "(%Heq1 & %Heq2 & Ha)".
        rewrite (UIP_refl _ _ Heq1) (UIP_refl _ _ Heq2). done.
      + iIntros "Ha". iExists eq_refl, eq_refl. done.
    - iSplit.
      + iIntros "(%Heq1 & %Heq2 & Ha)".
        rewrite (UIP_refl _ _ Heq1) (UIP_refl _ _ Heq2). done.
      + iIntros "Ha". iExists eq_refl, eq_refl. done.
  Qed.
  Lemma ltype_own_core_opened_unfold {rt_cur rt_inner rt_full : RT} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ) k π r l :
    ltype_own_core (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) k π r l ≡ opened_ltype_own (@ltype_own) (@ltype_own_core) lt_cur lt_inner lt_full Cpre Cpost k π r l.
  Proof.
    rewrite -ltype_own_opened_unfold.
    rewrite ltype_own_core_unseal ltype_own_unseal /ltype_own_core_def /ltype_own_def /ltype_own_pre.
    simp lty_own_pre. done.
  Qed.

  Lemma ltype_own_coreable_unfold {rt_full} (κs : list lft) (lt_full : ltype rt_full) k π r l :
    ltype_own (CoreableLtype κs lt_full) k π r l ≡ coreable_ltype_own (@ltype_own) (@ltype_own_core) κs lt_full k π r l.
  Proof.
    rewrite /coreable_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (CoreableLtype κs lt_full)).
    simpl. intros Heq1 Heq2. move: Heq1 Heq2 r.
    intros <- Heq r. rewrite (UIP_refl _ _ Heq). clear Heq.
    done.
  Qed.
  Lemma ltype_own_core_coreable_unfold {rt_full} (κs : list lft) (lt_full : ltype rt_full) k π r l :
    ltype_own_core (CoreableLtype κs lt_full) k π r l ≡ ltype_own_core lt_full k π r l.
  Proof.
    rewrite /coreable_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (CoreableLtype κs lt_full)).
    simpl. intros Heq1 Heq2. move : Heq1 Heq2 r. intros <- Heq r.
    rewrite (UIP_refl _ _ Heq). done.
  Qed.

  Lemma ltype_own_shadowed_unfold {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) k π r l :
    ltype_own (ShadowedLtype lt_cur r_cur lt_full) k π r l ≡ shadowed_ltype_own (@ltype_own) (@ltype_own_core) lt_cur r_cur lt_full k π r l.
  Proof.
    rewrite /shadowed_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_cur).
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (ShadowedLtype lt_cur r_cur lt_full)).
    simpl. intros Heq1 Heq2 Heq3. move: Heq1 Heq2 Heq3 r r_cur. intros <- Heq <-.
    rewrite (UIP_refl _ _ Heq). cbn. intros ??.
    iSplit.
    - iIntros "(%Heq' & ?)". rewrite (UIP_refl _ _ Heq'). iFrame.
    - iIntros "?". iExists eq_refl. done.
  Qed.
  Lemma ltype_own_core_shadowed_unfold {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) k π r l :
    ltype_own_core (ShadowedLtype lt_cur r_cur lt_full) k π r l ≡ ltype_own_core lt_full k π r l.
  Proof.
    rewrite /shadowed_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_full).
    generalize (ltype_rt_agree (ShadowedLtype lt_cur r_cur lt_full)).
    intros Heq1 Heq2. move: Heq1 Heq2 r. intros <- Heq. rewrite (UIP_refl _ _ Heq).
    intros ?. done.
  Qed.

  Lemma ltype_own_opened_na_unfold {rt_cur rt_inner : RT} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
      (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ) k π r l :
    ltype_own (OpenedNaLtype lt_cur lt_inner Cpre Cpost) k π r l ≡ opened_na_ltype_own (@ltype_own) (@ltype_own_core) lt_cur lt_inner Cpre Cpost k π r l.
  Proof.
    rewrite /opened_na_ltype_own ?ltype_own_core_unseal /ltype_own_core_def ?ltype_own_unseal /ltype_own_def /ltype_own_pre.
    simp lty_own_pre.
    generalize (ltype_rt_agree lt_cur).
    generalize (ltype_rt_agree lt_inner).
    generalize (ltype_rt_agree (OpenedNaLtype lt_cur lt_inner Cpre Cpost)).
    simpl.
    intros Heq1 Heq2 Heq3. move : Cpre Cpost r.
    move: Heq1 Heq2 Heq3.
    intros <- <-.
    intros Heq Cpre Cpost r.
    specialize (UIP_refl _ _ Heq) => ->. clear Heq.
    repeat f_equiv.
    - done.
    - iSplit.
      + iIntros "(%Heq & Ha)".
        rewrite (UIP_refl _ _ Heq). done.
      + iIntros "Ha". iExists eq_refl. done.
  Qed.
  Lemma ltype_own_core_opened_na_unfold {rt_cur rt_inner : RT} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
      (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ) k π r l :
    ltype_own_core (OpenedNaLtype lt_cur lt_inner Cpre Cpost) k π r l ≡ opened_na_ltype_own (@ltype_own) (@ltype_own_core) lt_cur lt_inner Cpre Cpost k π r l.
  Proof.
    rewrite -ltype_own_opened_na_unfold.
    rewrite ltype_own_core_unseal ltype_own_unseal /ltype_own_core_def /ltype_own_def /ltype_own_pre.
    simp lty_own_pre. done.
  Qed.

  (** Lifting basic lemmas to [ltype] *)

  (* NOTE: This does not hold true for [OpenedLtype]! *)
  Lemma ltype_own_pre_shr_pers core {rt} (lt : ltype rt) κ π r l :
    (*match lt.(ltype_lty) with OpenedLty _ _ _ _ _ => False | _ => True end →*)
    Persistent (ltype_own_pre core lt (Shared κ) π r l).
  Proof. rewrite /ltype_own_pre. apply lty_own_pre_shr_pers. Qed.
  Global Instance ltype_own_shr_pers {rt} (lt : ltype rt) κ π r l :
    (*TCDone (match lt.(ltype_lty) with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (ltype_own lt (Shared κ) π r l).
  Proof. rewrite ltype_own_unseal. apply ltype_own_pre_shr_pers. Qed.
  Global Instance ltype_own_core_shr_pers {rt} (lt : ltype rt) κ π r l :
    (*TCDone (match lt.(ltype_lty) with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (ltype_own_core lt (Shared κ) π r l).
  Proof. rewrite ltype_own_core_unseal. apply ltype_own_pre_shr_pers. Qed.

  Lemma ltype_core_idemp {rt} (lt : ltype rt) :
    ltype_core (ltype_core lt) = ltype_core lt.
  Proof.
    destruct lt as [lt Heq Hwf].
    rewrite /ltype_core /=.
    specialize (lty_core_idemp lt) as Heq2.
    match goal with
    | |- context[ltype_core_obligation_1 ?H1 ?H2] => generalize (ltype_core_obligation_1 H1 H2) as Heq3
    end.
    simpl. intros Heq3.
    match goal with
    | |- context[ltype_core_obligation_1 ?H1 ?H2] => generalize (ltype_core_obligation_1 H1 H2) as Heq4
    end. intros Heq4.
    match goal with
    | |- context[ltype_core_obligation_2 ?H1 ?H2] => generalize (ltype_core_obligation_2 H1 H2) as Hwf1
    end; simpl.
    intros Hwf1.
    match goal with
    | |- context[ltype_core_obligation_2 ?H1 ?H2] => generalize (ltype_core_obligation_2 H1 H2) as Hwf2
    end; simpl.
    intros Hwf2.
    move: Hwf Heq2 Heq3 Heq4 Hwf1 Hwf2.
    subst. simpl.
    generalize (lty_core lt) as l => lt'.
    intros _ -> Heq3 Heq4 Hwf1 Hwf2.
    rewrite (UIP_t _ _ _ Heq3 Heq4).
    (* TODO uses proof irrelevance, can we avoid that? *)
    rewrite (proof_irrelevance _ Hwf1 Hwf2). done.
  Qed.

  Lemma ltype_own_has_layout {rt} (lt : ltype rt) k π r l :
    ltype_own lt k π r l -∗ ∃ ly : layout, ⌜syn_type_has_layout (ltype_st lt) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝.
  Proof.
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre.
    iIntros "Hown". iPoseProof lty_own_has_layout as "Ha".
    by iApply "Ha".
  Qed.
  Lemma ltype_own_has_layout' {rt} (lt : ltype rt) k π r l ly :
    syn_type_has_layout (ltype_st lt) ly →
    ltype_own lt k π r l -∗ ⌜l `has_layout_loc` ly⌝.
  Proof.
    iIntros (Hst) "Hown". iPoseProof (ltype_own_has_layout with "Hown") as "(%ly' & % & %)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj. done.
  Qed.

  Lemma ltype_own_loc_in_bounds {rt} (lt : ltype rt) k π r l ly :
    syn_type_has_layout (ltype_st lt) ly →
    ltype_own lt k π r l -∗ loc_in_bounds l 0 ly.(ly_size).
  Proof.
    iIntros (?) "Hown".
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre.
    iPoseProof lty_own_loc_in_bounds as "Ha"; first done.
    by iApply "Ha".
  Qed.

  Lemma ltype_own_addr_in_usize {rt} (lt : ltype rt) k π r l :
    ltype_own lt k π r l -∗ ⌜l.(loc_a) ∈ USize⌝.
  Proof.
    iIntros "Hown".
    iPoseProof (ltype_own_has_layout with "Hown") as "(%ly & % & %)".
    iPoseProof (ltype_own_loc_in_bounds with "Hown") as "Hlb"; first done.
    iApply (loc_in_bounds_in_range_usize with "Hlb").
  Qed.

  Lemma ltype_core_syn_type_eq {rt} (lt : ltype rt) :
    ltype_st (ltype_core lt) = ltype_st lt.
  Proof.
    rewrite /ltype_st /ltype_core /= lty_core_syn_type_eq //.
  Qed.

  Lemma ltype_own_shared_to_core {rt} (lt : ltype rt) κ0 π r l :
    ltype_own lt (Shared κ0) π r l -∗ ltype_own (ltype_core lt) (Shared κ0) π (r) l.
  Proof.
    iIntros "Ha".
    rewrite ltype_own_unseal /ltype_own_def /ltype_own_pre.
    assert (Heq2 : RT_rt (lty_rt (ltype_lty lt)) = RT_rt (lty_rt (lty_core (ltype_lty lt)))).
    { (rewrite lty_core_rt_eq//). }
    unshelve iPoseProof (lty_own_shared_to_core _ _ _ _ _  with "Ha") as "Ha"; first done.
    revert r Heq2.
    (*generalize (lty_core_rt_eq (ltype_lty lt)).*)
    generalize (ltype_rt_agree (ltype_core lt)).
    generalize (ltype_rt_agree lt).
    destruct lt; simpl.
    intros Heq0. subst.
    normalize_dep_rt_goal.
  Qed.


  (** Rules for ltype_core *)
  (** Since [ltype]s bundle equality proofs, [ltype_core] does not compute well, and we need equational lemmas instead. *)
  Lemma ltype_core_ofty {rt} (ty : type rt) :
    ltype_core (OfTy ty) = OfTy ty.
  Proof.
    rewrite /ltype_core /OfTy. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.

  Lemma canonical_enum_ltype_variant_core {rt : RT} (en : enum rt) r :
    enum_ltype_variant_core (canonical_enum_ltype_variant en r) =
      canonical_enum_ltype_variant en r.
  Proof.
    rewrite /enum_ltype_variant_core /canonical_enum_ltype_variant /= ltype_core_ofty //.
  Qed.

  Lemma interp_enum_ltype_variant_core {rt : RT} (en : enum rt) variant r :
    interp_enum_ltype_variant en (enum_ltype_variant_core <$> variant) r =
      enum_ltype_variant_core (interp_enum_ltype_variant en variant r).
  Proof.
    destruct variant as [v | ]; simpl.
    - destruct (decide (enum_tag en r = Some v.(eltv_tag))); simpl;
        rewrite ?canonical_enum_ltype_variant_core //.
    - symmetry. apply canonical_enum_ltype_variant_core.
  Qed.

  Lemma ltype_core_alias (rt : RT) (st : syn_type) (p : loc) :
    ltype_core (AliasLtype rt st p) = AliasLtype rt st p.
  Proof.
    rewrite /ltype_core /AliasLtype. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_blocked {rt} (ty : type rt) (κ : lft) :
    ltype_core (BlockedLtype ty κ) = OfTy ty.
  Proof.
    rewrite /ltype_core /BlockedLtype /OfTy. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_shrblocked {rt} (ty : type rt) (κ : lft) :
    ltype_core (ShrBlockedLtype ty κ) = OfTy ty.
  Proof.
    rewrite /ltype_core /ShrBlockedLtype /OfTy. simpl.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_mut_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_core (MutLtype lt κ) = MutLtype (ltype_core lt) κ.
  Proof.
    rewrite /ltype_core /MutLtype /=. f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_shr_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_core (ShrLtype lt κ) = ShrLtype (ltype_core lt) κ.
  Proof.
    rewrite /ltype_core /ShrLtype /=. f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_struct {rts} (lts : hlist ltype rts) (sls : struct_layout_spec) :
    ltype_core (StructLtype lts sls) = StructLtype (hmap (@ltype_core) lts) sls.
  Proof.
    rewrite /ltype_core /StructLtype /=.
    match goal with
    | |- mk_ltype _ ?lt1 ?H1 ?H3 = mk_ltype _ ?lt2 ?H2 ?H4 =>
        generalize H1 as Heq1; generalize H2 as Heq2;
        generalize H3 as Hwf1; generalize H4 as Hwf2
    end; simpl.
    intros Hwf1 Hwf2 <-. simpl.
    move: Hwf1 Hwf2.
    rewrite hcmap_hmap fmap_hcmap. simpl.
    intros Hwf1 Hwf2 Heq. rewrite (UIP_refl _ _ Heq).
    f_equiv. apply proof_irrelevance.
  Qed.

  Lemma ltype_lty_core {rt} (lt : ltype rt) :
    ltype_lty (ltype_core lt) = lty_core (ltype_lty lt).
  Proof. done. Qed.

  Lemma ltype_core_array {rt} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) :
    ltype_core (ArrayLtype def len lts) = ArrayLtype def len ((λ '(i, lt), (i, ltype_core lt)) <$> lts).
  Proof.
    rewrite /ltype_core /ArrayLtype /=.
    match goal with
    | |- mk_ltype _ ?lt1 ?H1 ?H3 = mk_ltype _ ?lt2 ?H2 ?H4 =>
        generalize H1 as Heq1; generalize H2 as Heq2;
        generalize H3 as Hwf1; generalize H4 as Hwf2
    end; simpl.
    intros Hwf1 Hwf2 <-. simpl.
    move: Hwf1 Hwf2.
    rewrite !map_fmap !map_map.

    rewrite (map_ext _  ((λ x : nat * ltype rt, let '(i, lt) := let '(i, lt) := x in (i, ltype_lty lt) in (i, lty_core lt)))); first last.
    { intros []. done. }
    intros Hwf1 Hwf2 Heq1.
    rewrite (UIP_refl _ _ Heq1).
    specialize (proof_irrelevance _  Hwf1 Hwf2) as ?. subst.
    done.
  Qed.
  Lemma ltype_core_enum {rt} (en : enum rt) (variant : option enum_ltype_variant) :
    ltype_core (EnumLtype en variant) =
      EnumLtype en (enum_ltype_variant_core <$> variant).
  Proof.
    destruct variant as [[tag rte lte re] | ].
    all: rewrite /ltype_core /EnumLtype /=.
    all: match goal with
      | |- mk_ltype _ ?lt1 ?H1 ?H3 = mk_ltype _ ?lt2 ?H2 ?H4 =>
          generalize H1 as Heq1; generalize H2 as Heq2;
          generalize H3 as Hwf1; generalize H4 as Hwf2
      end; simpl.
    all: intros Hwf1 Hwf2 Heq1 Heq2.
    all: rewrite (UIP_refl _ _ Heq1).
    all: rewrite (UIP_refl _ _ Heq2).
    all: f_equiv; apply proof_irrelevance.
  Qed.
  Lemma ltype_core_opened {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost :
    ltype_core (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) = OpenedLtype lt_cur lt_inner lt_full Cpre Cpost.
  Proof.
    rewrite /ltype_core /OpenedLtype /=.
    f_equiv; simpl.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_coreable {rt_full} (κs : list lft) (lt_full : ltype rt_full) :
    ltype_core (CoreableLtype κs lt_full) = ltype_core lt_full.
  Proof.
    rewrite /ltype_core /CoreableLtype /=.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_shadowed {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) :
    ltype_core (ShadowedLtype lt_cur r_cur lt_full) = ltype_core lt_full.
  Proof.
    rewrite /ltype_core /ShadowedLtype /=.
    f_equiv.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_opened_na {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost :
    ltype_core (OpenedNaLtype lt_cur lt_inner Cpre Cpost) = OpenedNaLtype lt_cur lt_inner Cpre Cpost.
  Proof.
    rewrite /ltype_core /OpenedNaLtype /=.
    f_equiv; simpl.
    - apply UIP_t.
    - apply proof_irrelevance.
  Qed.
  Lemma ltype_core_uninit st :
    ltype_core (UninitLtype st) = UninitLtype st.
  Proof.
    rewrite /ltype_core. simpl. apply mk_ltype_irrel.
  Qed.

  (** Rules for ltype_st *)
  Lemma ltype_st_ofty {rt} (ty : type rt) :
    ltype_st (OfTy ty) = ty.(ty_syn_type) MetaNone.
  Proof. done. Qed.
  Lemma ltype_st_alias rt st p :
    ltype_st (AliasLtype rt st p) = st.
  Proof. done. Qed.
  Lemma ltype_st_blocked {rt} (ty : type rt) (κ : lft) :
    ltype_st (BlockedLtype ty κ) = ty.(ty_syn_type) MetaNone.
  Proof. done. Qed.
  Lemma ltype_st_shrblocked {rt} (ty : type rt) (κ : lft) :
    ltype_st (ShrBlockedLtype ty κ) = ty.(ty_syn_type) MetaNone.
  Proof. done. Qed.
  Lemma ltype_st_mut_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_st (MutLtype lt κ) = PtrSynType.
  Proof. done. Qed.
  Lemma ltype_st_shr_ref {rt} (lt : ltype rt) (κ : lft) :
    ltype_st (ShrLtype lt κ) = PtrSynType.
  Proof. done. Qed.
  Lemma ltype_st_struct {rts} (lts : hlist ltype rts) (sls : struct_layout_spec) :
    ltype_st (StructLtype lts sls) = sls.
  Proof. done. Qed.
  Lemma ltype_st_array {rt} (def : type rt) (len : nat) (lts : list (nat * ltype rt)) :
    ltype_st (ArrayLtype def len lts) = ArraySynType (ty_syn_type def MetaNone) len.
  Proof. rewrite /ltype_st /= //. Qed.
  Lemma ltype_st_enum {rt} (en : enum rt) (variant : option enum_ltype_variant) :
    ltype_st (EnumLtype en variant) = en.(enum_els).
  Proof. rewrite /ltype_st /= //. Qed.
  Lemma ltype_st_opened {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost :
    ltype_st (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) = ltype_st lt_cur.
  Proof. done. Qed.
  Lemma ltype_st_coreable {rt_full} κs (lt_full : ltype rt_full) :
    ltype_st (CoreableLtype κs lt_full) = ltype_st lt_full.
  Proof. done. Qed.
  Lemma ltype_st_shadowed {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) :
    ltype_st (ShadowedLtype lt_cur r_cur lt_full) = ltype_st lt_full.
  Proof. done. Qed.
  Lemma ltype_st_opened_na {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost :
    ltype_st (OpenedNaLtype lt_cur lt_inner Cpre Cpost) = ltype_st lt_cur.
  Proof. done. Qed.

  (** Lifting the core equations to ltypes *)
  Lemma ltype_own_core_equiv {rt} (lt : ltype rt) k π r l :
    ltype_own_core lt k π r l ≡ ltype_own (ltype_core lt) k π r l.
  Proof.
    rewrite ltype_own_unseal ltype_own_core_unseal /ltype_own_core_def /ltype_own_def.
    assert (Heq : RT_rt (lty_rt (ltype_lty lt)) = RT_rt (lty_rt (lty_core (ltype_lty lt)))).
    { rewrite lty_core_rt_eq. done. }
    unshelve rewrite /ltype_own_pre (lty_own_core_equiv _ false); first apply Heq.
    simpl. iApply lty_own_pre_rfn_eq'.
    move: Heq.
    generalize (ltype_rt_agree lt) as Heq2.
    generalize (ltype_rt_agree (ltype_core lt)) as Heq2.
    simpl. rewrite lty_core_rt_eq.
    intros Heq1 Heq2 Heq3. rewrite (UIP_t _ _ _  Heq1 Heq2).
    rewrite (UIP_refl _ _ Heq3). done.
  Qed.
  Lemma ltype_own_core_core {rt} (lt : ltype rt) k π r l :
    ltype_own_core (ltype_core lt) k π r l ≡ ltype_own_core lt k π r l.
  Proof.
    rewrite ltype_own_core_unseal /ltype_own_core_def.
    assert (Heq : RT_rt (lty_rt (lty_core (ltype_lty lt))) = RT_rt (lty_rt (ltype_lty lt))).
    { rewrite lty_core_rt_eq. done. }
    unshelve rewrite /ltype_own_pre lty_own_core_core'; first apply Heq.
    simpl. iApply lty_own_pre_rfn_eq'.
    move: Heq.
    generalize (ltype_rt_agree lt) as Heq2.
    generalize (ltype_rt_agree (ltype_core lt)) as Heq2.
    simpl. rewrite lty_core_rt_eq.
    intros Heq1 Heq2 Heq3. rewrite (UIP_t _ _ _  Heq1 Heq2).
    rewrite (UIP_refl _ _ Heq3). done.
  Qed.


  (** Compute the lifetimes at which there are blocked components of an lty. *)
  Fixpoint lty_blocked_lfts (lt : lty) : list lft :=
    match lt with
    | OfTyLty ty => []
    | AliasLty _ _ _ => []
    | BlockedLty ty κ => [κ]
    | ShrBlockedLty ty κ => [κ]
    | MutLty lt κ => lty_blocked_lfts lt
    | ShrLty lt κ => lty_blocked_lfts lt
    | StructLty lts sls => concat (map lty_blocked_lfts lts)
    | ArrayLty def len lts => concat (map (λ '(_, lt), lty_blocked_lfts lt) lts)
    | EnumLty en variant =>
      match variant with Some v => lty_blocked_lfts v.(elv_lty) | None => [] end
    | OpenedLty _ _ _ _ _  => []
    | CoreableLty κs _ => κs
    | ShadowedLty lt_cur r_cur lt_full => lty_blocked_lfts lt_full
    | OpenedNaLty _ _ _ _ => []
    end.

  Definition ltype_blocked_lfts {rt} (lt : ltype rt) : list lft :=
    lty_blocked_lfts (lt.(ltype_lty)).

  (** ** Deinitialization of ltypes *)
  Definition lty_uniq_deinitializable (lt : lty) : Prop :=
    match lt with
    | BlockedLty _ _  => False
    | ShrBlockedLty _ _ => False
    | OfTyLty _ => True
    | AliasLty _ _ _ => False
    | MutLty _ _ => True
    | ShrLty _ _ => True
    | StructLty lts sls =>
        True
    | ArrayLty def len lts =>
        True
    | EnumLty en variant =>
        True
    | OpenedLty _ _ _ _ _ => False
    | CoreableLty _ _ => True
    | ShadowedLty lt _ _ =>
        False
    | OpenedNaLty _ _ _ _ => False
    end.
  Definition ltype_uniq_deinitializable {rt} (lt : ltype rt) :=
    lty_uniq_deinitializable lt.(ltype_lty).

  Lemma lty_own_deinit_ghost_drop_uniq π F (lt : lty) κ γ r l :
    lftE ⊆ F →
    lty_uniq_deinitializable lt →
    lty_own lt (Uniq κ γ) π r l ={F}=∗
    place_rfn_interp_mut r γ.
  Proof.
    intros ? Hdeinit.
    induction lt using lty_induction; simpl; try done.
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & ? & Hcred & $ & Hl)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & Hlb & Hcred & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%el & ? & ? & ? & Hcred & $ & Hb)".
    - rewrite /lty_own. simp lty_own_pre.
      by iIntros "(%ly & %Halg & ? & ? & $ & _)".
  Qed.
  Lemma ltype_own_deinit_ghost_drop_uniq π F {rt} (lt : ltype rt) κ γ r l :
    lftE ⊆ F →
    ltype_uniq_deinitializable lt →
    ltype_own lt (Uniq κ γ) π r l ={F}=∗
    place_rfn_interp_mut r γ.
  Proof.
    iIntros (??) "Hown".
    iPoseProof (lty_own_deinit_ghost_drop_uniq _ _ (lt.(ltype_lty)) with "[Hown]") as "Ha";
      [done | done | ..].
    { rewrite ltype_own_unseal. done. }
    destruct lt; subst; eauto.
  Qed.

  Definition lty_uniq_extractable (lt : lty) : option (option (list lft)) :=
    match lt with
    | BlockedLty _ κ  => Some (Some [κ])
    | ShrBlockedLty _ _ => Some None
    | OfTyLty _ => Some (None)
    | AliasLty _ _ _ => None
    | MutLty _ _ => Some None
    | ShrLty _ _ => Some None
    | StructLty lts sls =>
        Some None
    | ArrayLty def len lts =>
        Some None
    | EnumLty en variant =>
        Some None
    | OpenedLty _ _ _ _ _ => None
    | CoreableLty _ _ => Some None
    | ShadowedLty lt _ _ =>
        None
    | OpenedNaLty _ _ _ _ => None
    end.
  Definition ltype_uniq_extractable {rt} (lt : ltype rt) : option (option (list lft)) :=
    lty_uniq_extractable lt.(ltype_lty).


  Lemma lty_own_extract_ghost_drop_uniq π F (lt : lty) κ κm γ r l :
    lftE ⊆ F →
    lty_uniq_extractable lt = Some κm →
    lty_own lt (Uniq κ γ) π r l ={F}=∗
    (MaybeInherit κm (place_rfn_interp_mut r γ)).
  Proof.
    intros ? Hdeinit.
    rewrite /MaybeInherit/Inherit.
    induction lt using lty_induction; simpl; simpl in Hdeinit; try done.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-. simpl.
      iIntros "(%ly & %Halg & %Hly & ? & ? & Hinh & Hcred & Hl)".
      iModIntro. iIntros (??) "Ha".
      rewrite right_id.
      iMod (fupd_mask_mono with "(Hinh Ha)") as "($ & _)"; first done.
      done.
    - rewrite /lty_own. simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & ? & Hlb & (%r' & Hrfn & Hobs & Hb))". injection Hdeinit as <-.
      iModIntro. iIntros (??). simpl.
      done.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hr & Hb)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hb)". injection Hdeinit as <-.
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & ? & Hcred & ? & Hb)". injection Hdeinit as <-.
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%el & ? & ? & ? & Hcred & Hr & Hb)".
      iModIntro. iIntros (??). by iFrame.
    - rewrite /lty_own. simp lty_own_pre. injection Hdeinit as <-.
      iIntros "(%ly & %Halg & ? & ? & ? & _)".
      iModIntro. iIntros (??). by iFrame.
  Qed.
  Lemma ltype_own_extract_ghost_drop_uniq π F {rt} (lt : ltype rt) κ κm γ r l :
    lftE ⊆ F →
    ltype_uniq_extractable lt = Some κm →
    ltype_own lt (Uniq κ γ) π r l ={F}=∗
    MaybeInherit κm (place_rfn_interp_mut r γ).
  Proof.
    iIntros (??) "Hown".
    iPoseProof (lty_own_extract_ghost_drop_uniq _ _ (lt.(ltype_lty)) with "[Hown]") as "Ha";
      [done | done | ..].
    { rewrite ltype_own_unseal. done. }
    destruct lt; subst; eauto.
  Qed.
End ltype_def.

Notation "◁ ty" := (OfTy ty) (at level 15) : bi_scope.

Notation "l ◁ₗ[ π , k ]  r  @  ty" := (ltype_own ty k π r l) (at level 15) : bi_scope.
Notation "l ◁ₗ[ π , k ]  .@  ty" := (ltype_own ty k π (PlaceIn ()) l) (at level 15) : bi_scope.

(** Ltac for simplifying some of the Ltac functions that don't compute *)
Ltac simp_ltype_core Heq :=
  cbn in Heq;
  repeat lazymatch type of Heq with
  | _ = ltype_core (ltype_core _) =>
      rewrite ltype_core_idemp in Heq
  | _ = ltype_core (OfTy _) =>
      rewrite ltype_core_ofty in Heq
  | _ = ltype_core (AliasLtype _ _ _) =>
      rewrite ltype_core_alias in Heq
  | _ = ltype_core (BlockedLtype _ _) =>
      rewrite ltype_core_blocked in Heq
  | _ = ltype_core (ShrBlockedLtype _ _) =>
      rewrite (ltype_core_shrblocked) in Heq
  | _ = ltype_core (MutLtype _ _) =>
      rewrite (ltype_core_mut_ref) in Heq
  | _ = ltype_core (ShrLtype _ _) =>
      rewrite (ltype_core_shr_ref) in Heq
  | _ = ltype_core (StructLtype _ _) =>
      rewrite (ltype_core_struct) in Heq
  | _ = ltype_core (ArrayLtype _ _ _) =>
      rewrite (ltype_core_array) in Heq
  | _ = ltype_core (EnumLtype _ _) =>
      rewrite ltype_core_enum in Heq
  | _ = ltype_core (OpenedLtype _ _ _ _ _) =>
      rewrite (ltype_core_opened) in Heq
  | _ = ltype_core (CoreableLtype _ _) =>
      rewrite (ltype_core_coreable) in Heq
  | _ = ltype_core (ShadowedLtype _ _ _) =>
      rewrite (ltype_core_shadowed _ _ _) in Heq
  | _ = ltype_core (OpenedNaLtype _ _ _ _) =>
      rewrite (ltype_core_opened_na) in Heq
  end.
Ltac simp_ltype_st Heq :=
  cbn in Heq;
  repeat lazymatch type of Heq with
  | _ = ltype_st (ltype_core _) =>
      rewrite ltype_core_syn_type_eq in Heq
  | _ = ltype_st (OfTy _) =>
      rewrite ltype_st_ofty in Heq
  | _ = ltype_st (AliasLtype _ _ _) =>
      rewrite ltype_st_alias in Heq
  | _ = ltype_st (BlockedLtype _ _) =>
      rewrite ltype_st_blocked in Heq
  | _ = ltype_st (ShrBlockedLtype _ _) =>
      rewrite (ltype_st_shrblocked) in Heq
  | _ = ltype_st (MutLtype _ _) =>
      rewrite (ltype_st_mut_ref) in Heq
  | _ = ltype_st (ShrLtype _ _) =>
      rewrite (ltype_st_shr_ref) in Heq
  | _ = ltype_st (StructLtype _ _) =>
      rewrite (ltype_st_struct) in Heq; simpl in Heq
  | _ = ltype_st (ArrayLtype _ _ _) =>
      rewrite (ltype_st_array) in Heq; simpl in Heq
  | _ = ltype_st (EnumLtype _ _) =>
      rewrite (ltype_st_enum) in Heq; simpl in Heq
  | _ = ltype_st (OpenedLtype _ _ _ _ _) =>
      rewrite (ltype_st_opened) in Heq
  | _ = ltype_st (CoreableLtype _ _) =>
      rewrite (ltype_st_coreable) in Heq
  | _ = ltype_st (ShadowedLtype _ _ _) =>
      rewrite (ltype_st_shadowed _ _ _) in Heq
  | _ = ltype_st (OpenedNaLtype _ _ _ _) =>
      rewrite (ltype_st_opened_na) in Heq
  end.

Ltac simp_ltype :=
  match goal with
  | |- context[@ltype_core _ _ ?rt ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_core (rt:=rt) lt) as ltc eqn:Heq;
      simp_ltype_core Heq;
      subst ltc
  | |- context[@ltype_st _ _ ?rt ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_st (rt:=rt) lt) as ltc eqn:Heq;
      simp_ltype_st Heq;
      subst ltc
  end.
Ltac simp_ltypes := repeat simp_ltype.

Tactic Notation "simp_ltype" "in" hyp(H) :=
  match type of H with
  | context[@ltype_core _ _ ?rt ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_core (rt:=rt) lt) as ltc eqn:Heq in H;
      simp_ltype_core Heq;
      subst ltc
  | context[@ltype_st _ _ ?rt ?lt] =>
      assert_fails (is_var lt);
      let ltc := fresh "ltc" in
      let Heq := fresh "Heq_lt" in
      remember (ltype_st (rt:=rt) lt) as ltc eqn:Heq in H;
      simp_ltype_st Heq;
      subst ltc
  end.
Tactic Notation "simp_ltypes" "in" hyp(H) := repeat simp_ltype in H.

(** ** Ltype subtyping *)
Definition ltype_incl' `{!typeGS Σ} {rt1 rt2 : RT} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : iProp Σ :=
  (□
    match b with
    | Owned =>
      ∀ π l, ltype_own lt1 Owned π r1 l ={lftE}=∗ ltype_own lt2 Owned π r2 l
    | Uniq κ γ =>
      ∀ π l, ltype_own lt1 (Uniq κ γ) π r1 l -∗ ltype_own lt2 (Uniq κ γ) π r2 l
    | Shared κ =>
      ∀ π l, ltype_own lt1 (Shared κ) π r1 l -∗ ltype_own lt2 (Shared κ) π r2 l
    end).

Definition ltype_incl `{!typeGS Σ} {rt1 rt2 : RT} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : iProp Σ :=
  (□
  (
   ltype_incl' b r1 r2 lt1 lt2 ∗
   ltype_incl' b r1 r2 (ltype_core lt1) (ltype_core lt2)
  )).
Global Instance ltype_incl_persistent `{!typeGS Σ} {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Persistent (ltype_incl b r1 r2 lt1 lt2) := _.

Definition ltype_eq `{!typeGS Σ} {rt1 rt2 : RT} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : iProp Σ :=
  ltype_incl b r1 r2 lt1 lt2 ∗ ltype_incl b r2 r1 lt2 lt1.
Global Instance ltype_eq_persistent `{!typeGS Σ} {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Persistent (ltype_eq b r1 r2 lt1 lt2) := _.

(** Heterogeneous ltype equality *)
Definition eqltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ (rrust_ctx -∗ elctx_interp E -∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ltype_eq b r1 r2 lt1 lt2).
#[export]
Instance: Params (@eqltype) 6 := {}.

(** Homogeneous ltype equality, disregarding the refinement and borkind *)
Definition full_eqltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ∀ b r, ltype_eq b r r lt1 lt2.
#[export]
Instance: Params (@full_eqltype) 5 := {}.

(** Heterogeneous ltype subtyping *)
Definition subltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ (elctx_interp E -∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ltype_incl b r1 r2 lt1 lt2).
#[export]
Instance: Params (@subltype) 6 := {}.

(** Homogeneous ltype subtyping, disregarding the refinement and borkind *)
Definition full_subltype `{!typeGS Σ} (E : elctx) (L : llctx) {rt} (lt1 : ltype rt) (lt2 : ltype rt) : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ∀ b r, ltype_incl b r r lt1 lt2.
#[export]
Instance: Params (@full_subltype) 5 := {}.

Lemma ltype_incl'_use `{!typeGS Σ} {rt1 rt2} F (lt1 : ltype rt1) (lt2 : ltype rt2) l π b r1 r2 :
  lftE ⊆ F →
  ltype_incl' b r1 r2 lt1 lt2 -∗
  l ◁ₗ[π, b] r1 @ lt1 ={F}=∗
  l ◁ₗ[π, b] r2 @ lt2.
Proof.
  iIntros (?) "#Hincl Hl".
  iMod (fupd_mask_subseteq lftE) as "Hcl"; first done.
  destruct b.
  - iMod ("Hincl" with "Hl") as "$". by iMod "Hcl".
  - iMod "Hcl". iModIntro. by iApply "Hincl".
  - iMod "Hcl". iModIntro. by iApply "Hincl".
Qed.
Lemma ltype_incl_use `{!typeGS Σ} {rt1 rt2} π F b r1 r2 l (lt1 : ltype rt1) (lt2 : ltype rt2) :
  lftE ⊆ F →
  ltype_incl b r1 r2 lt1 lt2 -∗
  l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2.
Proof.
  iIntros (?) "Hincl Ha".
  iDestruct "Hincl" as "(#Hincl & _)".
  destruct b.
  - iApply (fupd_mask_mono with "(Hincl Ha)"); done.
  - by iApply "Hincl".
  - by iApply "Hincl".
Qed.
Lemma ltype_incl_use_core `{!typeGS Σ} {rt1 rt2} π F b r1 r2 l (lt1 : ltype rt1) (lt2 : ltype rt2) :
  lftE ⊆ F →
  ltype_incl b r1 r2 lt1 lt2 -∗
  l ◁ₗ[π, b] r1 @ ltype_core lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ ltype_core lt2.
Proof.
  iIntros (?) "Hincl Ha".
  iDestruct "Hincl" as "( _ & #Hincl)".
  destruct b.
  - iApply (fupd_mask_mono with "(Hincl Ha)"); done.
  - by iApply "Hincl".
  - by iApply "Hincl".
Qed.

Lemma ltype_incl_core `{!typeGS Σ}  {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
  ltype_incl b r1 r2 lt1 lt2 -∗ ltype_incl b r1 r2 (ltype_core lt1) (ltype_core lt2).
Proof.
  iIntros "(_ & #Hi)".
  iSplitR; iModIntro.
  - done.
  - rewrite !ltype_core_idemp. done.
Qed.

Section accessors.
  Context `{!typeGS Σ}.
  Lemma subltype_use {rt1 rt2} F E L b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    lftE ⊆ F →
    subltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    □ ∀ π l, l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2.
  Proof.
    iIntros (? Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "(_ & #Hincl)".
    iModIntro. iIntros (π l). iApply ltype_incl_use; done.
  Qed.
  Lemma subltype_use_core {rt1 rt2} F E L b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    lftE ⊆ F →
    subltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    □ ∀ π l, l ◁ₗ[π, b] r1 @ ltype_core lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ ltype_core lt2.
  Proof.
    iIntros (? Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "(_ & #Hincl)".
    iModIntro. iIntros (π l). iApply ltype_incl_use_core; done.
  Qed.

  Lemma subltype_acc {rt1 rt2} E L b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    subltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ltype_incl b r1 r2 lt1 lt2.
  Proof.
    iIntros (Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "#Hincl". done.
  Qed.
  Lemma full_subltype_acc E L {rt} (lt1 lt2 : ltype rt) :
    full_subltype E L lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ∀ b r, ltype_incl b r r lt1 lt2.
  Proof.
    iIntros (Hsubt) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & _)".
    iPoseProof (Hsubt with "HL CTX HE") as "(% & #Hincl)".
    iR. iIntros (b r). iApply "Hincl".
  Qed.

  Lemma eqltype_use_noend F E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) qL l π :
    lftE ⊆ F →
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    (l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2) ∗
    llctx_interp_noend L qL.
  Proof.
    iIntros (? Hunfold) "#CTX #HE HL".
    iPoseProof (Hunfold with "HL CTX HE") as "(% & #Hll)". iFrame.
    iIntros "Hl".
    iDestruct "Hll" as "((#Ha & _) & _)".
    destruct b.
    - iMod (fupd_mask_subseteq lftE) as "Hcl"; first solve_ndisj.
      iMod ("Ha" with "Hl") as "$". by iMod "Hcl" as "_".
    - by iApply "Ha".
    - by iApply "Ha".
  Qed.
  Lemma eqltype_use F E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) l π :
    lftE ⊆ F →
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    (l ◁ₗ[π, b] r1 @ lt1 ={F}=∗ l ◁ₗ[π, b] r2 @ lt2) ∗
    llctx_interp L.
  Proof.
    iIntros (? Hunfold) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (eqltype_use_noend with "CTX HE HL") as "($ & HL)"; [done.. | ].
    by iApply "HL_cl".
  Qed.
  Lemma eqltype_acc E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ltype_eq b r1 r2 lt1 lt2.
  Proof.
    iIntros (Heq) "CTX HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iApply (Heq with "HL CTX HE").
  Qed.
  Lemma full_eqltype_acc E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ∀ b r, ltype_eq b r r lt1 lt2.
  Proof.
    iIntros (Heq) "CTX HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iApply (Heq with "HL CTX HE").
  Qed.

  Lemma all_ltype_eq_alt {rt} b (lt1 lt2 : ltype rt) :
    (∀ r, ltype_eq b r r lt1 lt2) ⊣⊢ (∀ r, ltype_incl b r r lt1 lt2) ∧ (∀ r, ltype_incl b r r lt2 lt1).
  Proof.
    iSplit.
    - iIntros "#Ha". iSplit; iIntros (r); iSpecialize ("Ha" $! r); iDestruct "Ha" as "[Ha Hb]"; done.
    - iIntros "#[Ha Hb]". iIntros (r). iSplit; done.
  Qed.
  Lemma full_eqltype_use F π E L {rt} b r (lt1 lt2 : ltype rt) l :
    lftE ⊆ F →
    full_eqltype E L lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    (l ◁ₗ[ π, b] r @ lt1 ={F}=∗ l ◁ₗ[ π, b] r @ lt2) ∗
    llctx_interp L.
  Proof.
    iIntros (? Heq) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "(% & #Heq)"; [done | ].
    iFrame. iIntros "Hl". iDestruct ("Heq" $! _ _) as "[Hincl _]".
    by iApply (ltype_incl_use with "Hincl Hl").
  Qed.

  Lemma eqltype_syn_type_eq_noend E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) qL :
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros (Hunfold) "#CTX #HE HL".
    iPoseProof (Hunfold with "HL CTX HE") as "(% & #Hll)".
    done.
  Qed.
  Lemma eqltype_syn_type_eq E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    eqltype E L b r1 r2 lt1 lt2 →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ⌜ltype_st lt1 = ltype_st lt2⌝.
  Proof.
    iIntros (Hunfold) "#CTX #HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (eqltype_syn_type_eq_noend with "CTX HE HL") as "#$".
    done.
  Qed.
End accessors.

Section eqltype.
  Context `{!typeGS Σ}.

  (** *** [ltype_incl]/[ltype_eq] *)
  Lemma ltype_incl_eq {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_incl b r1 r2 lt1 lt2 -∗ ltype_incl b r2 r1 lt2 lt1 -∗ ltype_eq b r1 r2 lt1 lt2.
  Proof.
    iIntros "H1 H2". iSplit; done.
  Qed.

  Lemma ltype_incl'_refl {rt} b r (lt : ltype rt) : ⊢ ltype_incl' b r r lt lt.
  Proof.
    iModIntro. destruct b; iIntros; try destruct wl; eauto.
  Qed.
  Lemma ltype_incl_refl {rt} b r (lt : ltype rt) : ⊢ ltype_incl b r r lt lt.
  Proof.
    iIntros "!>". iSplit; iApply ltype_incl'_refl.
  Qed.
  Lemma ltype_incl_trans {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    ltype_incl b r1 r2 lt1 lt2 -∗ ltype_incl b r2 r3 lt2 lt3 -∗ ltype_incl b r1 r3 lt1 lt3.
  Proof.
    iIntros "(#Hi1 & #Hc1) (#Hi2 & #Hc2)".
    iModIntro.
    iSplit.
    - iModIntro. destruct b.
      + iIntros (??) "Ha". iMod ("Hi1" with "Ha") as "Ha". by iApply "Hi2".
      + iIntros (??) "Ha". iPoseProof ("Hi1" with "Ha") as "Ha". by iApply "Hi2".
      + iIntros (??) "Ha". iApply "Hi2". iApply "Hi1". done.
    - iModIntro. destruct b.
      + iIntros (??) "Ha". iMod ("Hc1" with "Ha") as "Ha". iApply ("Hc2" with "Ha").
      + iIntros (??) "Ha". iApply "Hc2". iApply "Hc1". done.
      + iIntros (??) "Ha". iApply "Hc2". iApply "Hc1". done.
  Qed.

  Lemma ltype_eq_ltype_incl_l {rt1 rt2} k r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq k r1 r2 lt1 lt2 -∗ ltype_incl k r1 r2 lt1 lt2.
  Proof. iIntros "($ & _)". Qed.
  Lemma ltype_eq_ltype_incl_r {rt1 rt2} k r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq k r1 r2 lt1 lt2 -∗ ltype_incl k r2 r1 lt2 lt1.
  Proof. iIntros "(_ & $)". Qed.

  Lemma ltype_eq_refl {rt} b r (lt : ltype rt) : ⊢ ltype_eq b r r lt lt.
  Proof.
    iSplit; iApply ltype_incl_refl.
  Qed.
  Lemma ltype_eq_sym {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : ltype_eq b r1 r2 lt1 lt2 -∗ ltype_eq b r2 r1 lt2 lt1.
  Proof.
    iIntros "[H1 H2]". iSplit; done.
  Qed.
  Lemma ltype_eq_trans {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    ltype_eq b r1 r2 lt1 lt2 -∗ ltype_eq b r2 r3 lt2 lt3 -∗ ltype_eq b r1 r3 lt1 lt3.
  Proof.
    iIntros "(Hi1 & Hi2) (Hj1 & Hj2)". iSplit.
    - iApply (ltype_incl_trans with "Hi1 Hj1").
    - iApply (ltype_incl_trans with "Hj2 Hi2").
  Qed.

  Lemma ltype_eq_core {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    ltype_eq b r1 r2 lt1 lt2 -∗ ltype_eq b r1 r2 (ltype_core lt1) (ltype_core lt2).
  Proof.
    iIntros "((#Hi & #Hc) & (#Hi2 & #Hc2))".
    iSplit; iModIntro.
    - rewrite !ltype_core_idemp. iSplit; done.
    - rewrite !ltype_core_idemp. iSplit; done.
  Qed.

  (** *** [eqltype] / [subltype] / [full_eqltype] / [full_subltype] *)
  Lemma full_eqltype_alt E L {rt} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 ↔ (∀ b r, eqltype E L b r r lt1 lt2).
  Proof.
    split.
    - iIntros (Heq b r qL) "HL CTX HE". iPoseProof (Heq with "HL CTX HE") as "(%Hst & ?)".
      iR. done.
    - iIntros (Heq qL) "HL CTX HE".
      iPoseProof (Heq inhabitant inhabitant with "HL CTX HE") as "(%Hst & #?)".
      iR. iIntros (b r).
      iPoseProof (Heq with "HL CTX HE") as "(_ & #?)".
      done.
  Qed.
  Lemma full_subltype_alt E L {rt} (lt1 lt2 : ltype rt) :
    full_subltype E L lt1 lt2 ↔ (∀ b r, subltype E L b r r lt1 lt2).
  Proof.
    split.
    - iIntros (Hsub b r qL) "HL CTX HE".
      iPoseProof (Hsub with "HL CTX HE") as "(%Hst & ?)".
      iR. done.
    - iIntros (Hsub qL) "HL CTX HE".
      iPoseProof (Hsub inhabitant inhabitant with "HL CTX HE") as "(%Hst & #?)".
      iR. iIntros (b r).
      iPoseProof (Hsub with "HL CTX HE") as "(_ & #?)".
      done.
  Qed.

  Global Instance eqltype_refl E L {rt} b r : Reflexive (eqltype E L b (rt1:=rt) (rt2:=rt) r r).
  Proof. iIntros (??) "? ? ?". iR. iApply ltype_eq_refl. Qed.
  Lemma eqltype_symm E L {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) :
    eqltype E L b r1 r2 lt1 lt2 → eqltype E L b r2 r1 lt2 lt1.
  Proof.
    intros Heq.
    iIntros (?) "HL CTX HE". iDestruct (Heq with "HL CTX HE") as "(% & #Heq)".
    iR. by iApply ltype_eq_sym.
  Qed.
  Lemma eqltype_trans E L {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    eqltype E L b r1 r2 lt1 lt2 → eqltype E L b r2 r3 lt2 lt3 → eqltype E L b r1 r3 lt1 lt3.
  Proof.
    intros H1 H2.
    iIntros (?) "HL #CTX #HE". iDestruct (H1 with "HL CTX HE") as "(%Hst1 & #Heq1)".
    iDestruct (H2 with "HL CTX HE") as "(%Hst2 & #Heq2)".
    rewrite Hst1 Hst2. iR.
    iApply ltype_eq_trans; done.
  Qed.

  Global Instance full_eqltype_equivalence E L {rt}:
    Equivalence (full_eqltype E L (rt:=rt)).
  Proof.
    split.
    - intros ?. apply full_eqltype_alt => ??. apply eqltype_refl.
    - intros ??. rewrite !full_eqltype_alt => ? ??. by apply eqltype_symm.
    - intros ???. rewrite !full_eqltype_alt => H1 H2 ??. eapply eqltype_trans; [apply H1 | apply H2].
  Qed.

  Global Instance subltype_refl E L {rt} b r : Reflexive (subltype E L (rt1:=rt) (rt2:=rt) b r r).
  Proof.
    iIntros (lt ?) "HL CTX HE".
    iR. iModIntro.
    iSplit; iApply ltype_incl'_refl.
  Qed.
  Lemma subltype_trans E L {rt1 rt2 rt3} b r1 r2 r3 (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) :
    subltype E L b r1 r2 lt1 lt2 → subltype E L b r2 r3 lt2 lt3 → subltype E L b r1 r3 lt1 lt3.
  Proof.
    iIntros (Hsub12 Hsub23). iIntros (?) "HL #CTX #HE".
    iPoseProof (Hsub12 with "HL CTX HE") as "(%Hst1 & #Hsub12)".
    iPoseProof (Hsub23 with "HL CTX HE") as "(%Hst2 & #Hsub23)".
    rewrite Hst1 Hst2. iR.
    iApply (ltype_incl_trans with "Hsub12 Hsub23").
  Qed.
  Global Instance full_subltype_preorder E L {rt} : PreOrder (full_subltype E L (rt := rt)).
  Proof.
    split.
    - intros ?. apply full_subltype_alt. intros ??. apply subltype_refl.
    - intros ???. rewrite !full_subltype_alt. intros H1 H2 ??. eapply subltype_trans; [apply H1 | apply H2].
  Qed.

  Lemma all_subltype_alt E L {rt} b (lt1 lt2 : ltype rt) :
    (∀ r, subltype E L b r r lt1 lt2) ↔
    (∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ∀ r, ltype_incl b r r lt1 lt2).
  Proof.
    split.
    - intros Ha qL. iIntros "HL CTX HE".
      iPoseProof (Ha inhabitant with "HL CTX HE") as "(% & #?)".
      iR.
      iIntros (r). by iPoseProof (Ha r with "HL CTX HE") as "(_ & Ha)".
    - intros Ha r. iIntros (qL) "HL CTX HE".
      iPoseProof (Ha with "HL CTX HE") as "(% & Ha)".
      iR. done.
  Qed.
  Lemma all_eqltype_alt E L {rt} b (lt1 lt2 : ltype rt) :
    (∀ r, eqltype E L b r r lt1 lt2) ↔
    (∀ qL, llctx_interp_noend L qL -∗ rrust_ctx -∗ elctx_interp E -∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ ∀ r, ltype_eq b r r lt1 lt2).
  Proof.
    split.
    - intros Ha qL. iIntros "HL CTX HE".
      iPoseProof (Ha inhabitant with "HL CTX HE") as "(% & #?)".
      iR. iIntros (r).
      by iPoseProof (Ha r with "HL CTX HE") as "(_ & Ha)".
    - intros Ha r. iIntros (qL) "HL CTX HE".
      iPoseProof (Ha with "HL CTX HE") as "(% & Ha)".
      iR. done.
  Qed.

  Lemma subltype_eqltype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b r1 r2 :
    subltype E L b r1 r2 lt1 lt2 → subltype E L b r2 r1 lt2 lt1 → eqltype E L b r1 r2 lt1 lt2.
  Proof.
    intros Ha Hb. iIntros (?) "HL #CTX #HE".
    iPoseProof (Ha with "HL CTX HE") as "(%Hst1 & #Ha)". iPoseProof (Hb with "HL CTX HE") as "(%Hst2 & #Hb)".
    iR. iSplit; done.
  Qed.
  Lemma full_subltype_eqltype E L {rt} (lt1 lt2 : ltype rt) :
    full_subltype E L lt1 lt2 → full_subltype E L lt2 lt1 → full_eqltype E L lt1 lt2.
  Proof.
    rewrite !full_subltype_alt !full_eqltype_alt.
    intros Ha Hb b r. eapply subltype_eqltype; done.
  Qed.

  (** ** Compatibilty of [OfTy] with subtyping *)
  Lemma type_incl_ltype_owned_wand {rt} (ty1 ty2 : type rt) π l :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    ∀ r, l ◁ₗ[π, Owned] r @ (◁ ty1) -∗ l ◁ₗ[π, Owned] r @ (◁ ty2).
  Proof.
    iIntros "%Hcomp #Hincl" (r) "Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & ? & Hsc & ? & %r' & Hrfn & Hb)".
    iExists ly.
    iPoseProof ("Hincl" $! inhabitant) as "(Hsceq & _)".
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsceq Hsc". { by iApply "Hsceq". }
    iMod "Hb" as "(% & ? & Hv)". iExists _. iFrame.
    iModIntro.
    iDestruct ("Hincl" $! r') as "(_ & #Hincl' & _)".
    by iApply "Hincl'".
  Qed.
  Lemma type_incl_ltype_shared_wand {rt} (ty1 ty2 : type rt) π l κ :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    ∀ r, l ◁ₗ[π, Shared κ] r @ (◁ ty1) -∗ l ◁ₗ[π, Shared κ] r @ (◁ ty2).
  Proof.
    iIntros "%Hcomp #Hincl" (r) "Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & ? & Hsc & ? & %r' & Hrfn & #Hb)".
    iExists ly.
    iPoseProof ("Hincl" $! inhabitant) as "(Hsceq & _)".
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsceq Hsc". { by iApply "Hsceq". }
    iModIntro. iMod "Hb" as "Hshr".
    iDestruct ("Hincl" $! r') as "(_ & _ & #Hincl')".
    by iApply "Hincl'".
  Qed.

  Lemma type_ltype_incl_shared_in {rt1 rt2} r1 r2 κ (ty1 : type rt1) (ty2 : type rt2) :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    type_incl r1 r2 ty1 ty2 -∗
    ltype_incl (Shared κ) #r1 #r2 (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "%Hcomp Hsub".
    iDestruct ("Hsub") as "(#Hsceq & #Hown & #Hshr)".
    (*iSplitR; iModIntro; simpl.*)
    rewrite /ltype_incl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iModIntro. iIntros (π l) "Hb". rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Hst & ? & Hsc & ? & %r' & -> & #Hb)".
    iExists ly.
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".
    iExists r2. iSplitR; first done. iModIntro. iMod "Hb". iModIntro. by iApply "Hshr".
  Qed.
  Lemma subtype_subltype_shared_in E L {rt1 rt2} r1 r2 κ (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 →
    subltype E L (Shared κ) (PlaceIn r1) (PlaceIn r2) (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub qL) "HL #CTX #HE". iPoseProof (Hsub with "HL HE") as "(%Hst & #Hsub)".
    simp_ltypes.
    iR. iApply (type_ltype_incl_shared_in); last done.
    rewrite Hst//.
  Qed.

  Lemma type_ltype_incl_shared {rt : RT} κ (ty1 : type rt) (ty2 : type rt) :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    (∀ r, type_incl r r ty1 ty2) -∗
    ∀ r, ltype_incl (Shared κ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "%Hcomp #Hsub". iIntros (r).
    iPoseProof ("Hsub" $! inhabitant) as "(#Hsceq & _)".
    iModIntro.
    simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb". rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Hst & ? & Hsc & ? & %r' & Hrfn & #Hb)".
    iExists ly.
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".
    iFrame. iModIntro. iMod "Hb". iModIntro.
    iDestruct ("Hsub" $! r') as "(_ & _ & Hshr)".
    by iApply "Hshr".
  Qed.
  Lemma subtype_subltype_shared E L {rt : RT} κ (ty1 : type rt) (ty2 : type rt) :
    (∀ r, subtype E L r r ty1 ty2) →
    ∀ r, subltype E L (Shared κ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub r qL) "HL #CTX #HE".
    rewrite all_subtype_alt in Hsub.
    iPoseProof (Hsub with "HL HE") as "(%Hcomp & #Hsub)".
    simp_ltypes. iR.
    iApply (type_ltype_incl_shared with "[] Hsub").
    rewrite Hcomp//.
  Qed.

  Lemma type_ltype_incl_owned_in_strong {rt1 rt2} π r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone) →
    (∀ v, v ◁ᵥ{π, MetaNone} r1 @ ty1 -∗ v ◁ᵥ{π, MetaNone} r2 @ ty2) -∗
    (ty1.(ty_sidecond) -∗ ty2.(ty_sidecond)) -∗
    ∀ l, l ◁ₗ[π, Owned] #r1 @ (◁ ty1) -∗ l ◁ₗ[π, Owned] #r2 @ (◁ ty2)%I.
  Proof.
    iIntros (Hcomp) "Hsub Hsceq".
    iIntros (l) "Hb".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Hst & ? & Hsc & ? & %r' & Hrfn & Hb)".
    iExists ly.
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsceq Hsc". { by iApply "Hsceq". }
    iExists r2. iSplitR; first done. iMod "Hb" as "(% & ? & Hv)". iExists _. iFrame.
    iModIntro. iDestruct "Hrfn" as "->". by iApply "Hsub".
  Qed.

  Lemma type_ltype_incl_owned_in {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    type_incl r1 r2 ty1 ty2 -∗ ltype_incl Owned #r1 #r2 (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "%Hcomp Hsub".
    iDestruct ("Hsub") as "(#Hsceq & #Hown & #Hshr)".
    iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb".
    iApply (type_ltype_incl_owned_in_strong with "Hown"); [done.. | ].
    done.
  Qed.
  Lemma subtype_subltype_owned_in E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 → subltype E L Owned #r1 #r2 (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub qL) "HL #CTX #HE". iPoseProof (Hsub with "HL HE") as "(%Hst & #Hsub)".
    simp_ltypes. iR.
    iApply (type_ltype_incl_owned_in); last done.
    rewrite Hst//.
  Qed.

  Lemma type_ltype_incl_owned {rt : RT} (ty1 : type rt) (ty2 : type rt) :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    (∀ r, type_incl r r ty1 ty2) -∗ ∀ r, ltype_incl Owned r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "%Hcomp #Hsub" (r).
    iPoseProof ("Hsub" $! inhabitant) as "(#Hsceq & _)".
    iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb".
    iModIntro.
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Hst & ? & Hsc & ? & %r' & Hrfn & Hb)".
    iDestruct ("Hsub" $! r') as "(_ & #Hown & #Hshr)".
    iExists ly.
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".
    iFrame. iMod "Hb" as "(% & ? & Hv)". iExists _. iFrame.
    iModIntro. by iApply "Hown".
  Qed.
  Lemma subtype_subltype_owned E L {rt : RT} (ty1 : type rt) (ty2 : type rt) :
    (∀ r, subtype E L r r ty1 ty2) → ∀ r, subltype E L Owned r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub r qL) "HL #CTX #HE". rewrite all_subtype_alt in Hsub.
    iPoseProof (Hsub with "HL HE") as "(%Hst & #Hsub)".
    simp_ltypes. iR.
    iApply (type_ltype_incl_owned with "[] Hsub").
    rewrite Hst//.
  Qed.

  (* NOTE: We do not get a direct heterogeneous subtyping lemma in the Uniq, because we cannot update the ghost variables in general.
     (I think we could get a lemma looking roughly like what we want, but it would work by reborrowing and  thus require later credits, and might also need a proof of liveness depending on how the atomic accessor works.) *)
  Lemma eqtype_subltype_homo_uniq_strong E L {rt} κ γ r1 r2 (ty1 : type rt) (ty2 : type rt) :
    eqtype E L r1 r2 ty1 ty2 → subltype E L (Uniq κ γ) (PlaceIn r1) (PlaceIn r2) (◁ ty1)%I (◁ ty2)%I.
  Proof.
    (* even this does not work, because we'd either:
       - need to update the ghost variable (TODO maybe this works with an atomic accessor)
       - or need to reborrow the whole thing, which would need a credit, see the comment above
     *)
  Abort.

  Lemma type_eq_ltype_incl_uniq {rt : RT} κ γ (ty1 : type rt) (ty2 : type rt) :
    ⌜syn_type_compat (ty1.(ty_syn_type) MetaNone) (ty2.(ty_syn_type) MetaNone)⌝ -∗
    (∀ r, type_incl r r ty1 ty2) -∗ (∀ r, type_incl r r ty2 ty1) -∗ ∀ r, ltype_incl (Uniq κ γ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros "%Hcomp #Hsub1 #Hsub2" (r).
    iPoseProof ("Hsub1" $! inhabitant) as "(#Hsceq & _)".
    iModIntro; simpl.
    simpl. simp_ltypes. rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hb".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Hst & ? & Hsc & Hlb & ? & Hrfn & Hb)".
    iExists ly. iFrame.
    apply Hcomp in Hst. iR.
    iFrame.
    iSplitL "Hsc"; first by iApply "Hsceq".

    iMod "Hb". iModIntro.
    iApply (pinned_bor_iff' with "[] Hb").
    iNext. iModIntro. iSplit.
    * iIntros "(%r' & Hrfn & Hb)". iExists _. iFrame.
      iMod "Hb". iModIntro.
      iDestruct "Hb" as "(%v & Hl & Hv)". iExists _. iFrame.
      iDestruct ("Hsub1" $! r') as "(_ & Hown & _)".
      by iApply "Hown".
    * iIntros "(%r' & Hrfn & Hb)". iExists _. iFrame.
      iMod "Hb". iModIntro.
      iDestruct "Hb" as "(%v & Hl & Hv)". iExists _. iFrame.
      iDestruct ("Hsub2" $! r') as "(_ & Hown & _)".
      by iApply "Hown".
  Qed.
  Lemma eqtype_subltype_uniq E L {rt : RT} κ γ (ty1 : type rt) (ty2 : type rt) :
    (∀ r, eqtype E L r r ty1 ty2) → ∀ r, subltype E L (Uniq κ γ) r r (◁ ty1)%I (◁ ty2)%I.
  Proof.
    iIntros (Hsub r qL) "HL #CTX #HE". apply all_eqtype_alt in Hsub as [Hsub1 Hsub2].
    iPoseProof (Hsub1 with "HL HE") as "(%Hst1 & #Hsub1)".
    iPoseProof (Hsub2 with "HL HE") as "(%Hst2 & #Hsub2)".

    simp_ltypes. iR.
    iApply (type_eq_ltype_incl_uniq with "[] Hsub1 Hsub2").
    rewrite Hst1//.
  Qed.

  Lemma full_eqtype_subltype E L {rt : RT} (ty1 : type rt) (ty2 : type rt) :
    (full_eqtype E L ty1 ty2) → full_subltype E L (◁ ty1)%I (◁ ty2)%I.
  Proof.
    intros Heq. apply full_subltype_alt => b r.
    destruct b.
    - eapply subtype_subltype_owned.
      intros. eapply Heq.
    - eapply subtype_subltype_shared.
      intros. eapply Heq.
    - eapply eqtype_subltype_uniq. done.
  Qed.

  Lemma full_eqtype_eqltype E L {rt : RT} (ty1 ty2 : type rt):
    (full_eqtype E L ty1 ty2) → full_eqltype E L (◁ ty1)%I (◁ ty2)%I.
  Proof.
    intros Ha. apply full_subltype_eqltype; apply full_eqtype_subltype; last symmetry; done.
  Qed.

  Lemma full_eqltype_subltype_l E L {rt : RT} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 → full_subltype E L lt1 lt2.
  Proof.
    iIntros (Heq ?) "HL #CTX #HE".
    iPoseProof (Heq with "HL CTX HE") as "(%Hst & Hincl)".
    iR.
    iIntros (??).
    iDestruct ("Hincl" $! _ _) as "($ & _)".
  Qed.
  Lemma full_eqltype_subltype_r E L {rt : RT} (lt1 lt2 : ltype rt) :
    full_eqltype E L lt1 lt2 → full_subltype E L lt2 lt1.
  Proof.
    iIntros (Heq ?) "HL #CTX #HE".
    iPoseProof (Heq with "HL CTX HE") as "(%Hst & Hincl)".
    iR.
    iIntros (??).
    iDestruct ("Hincl" $! _ _) as "(_ & $)".
  Qed.
End eqltype.

Section blocked.
  Context `{typeGS Σ}.

  Section unblockable.
    Context {rt rti : RT}.

    (** Implicit unblocking by the lifetime logic, saying that we can go back to the core of an ltype [lt] after [κs] has ended.
      Crucially, these shifts need to work without assuming anything about liveness of lifetimes and
      without updating any refinements.
      Moreover, we rely on later credits here in order to do this without laters by prepaying inheritance viewshifts (in particular to get the congruence lemma for products).
     *)
    Definition imp_unblockable (κs : list lft) (lt : ltype rt) : iProp Σ :=
      □
      (** Uniq *)
      ((∀ κ' γ' π r l,
        lft_dead_list κs -∗
        (ltype_own lt (Uniq κ' γ') π r l ={lftE}=∗ ltype_own_core lt (Uniq κ' γ') π r l)) ∗
      (** Owned. *)
      (∀ π r l,
        lft_dead_list κs -∗ ltype_own lt Owned π r l ={lftE}=∗ ltype_own_core lt Owned π r l)
      (** We don't have a requirement on Shared, as we should not have blocked things below shared ownership anyways. *)
      ).

    Global Instance imp_unblockable_persistent κ lt : Persistent (imp_unblockable κ lt).
    Proof. apply _. Qed.

    Lemma imp_unblockable_shorten κs κs' lt :
      □ (lft_dead_list κs ={lftE}=∗ lft_dead_list κs') -∗
      imp_unblockable κs' lt -∗ imp_unblockable κs lt.
    Proof.
      iIntros "#Hincl #(Ha1 & Ha2) !>".
      iSplitL.
      - iIntros (?????) "#Hdead Hb".
        iMod ("Hincl" with "Hdead") as "Hdead'".
        iApply ("Ha1" with "Hdead' Hb").
      - iIntros (???) "Hdead Hb".
        iMod ("Hincl" with "Hdead") as "Hdead'".
        iApply ("Ha2" with "Hdead' Hb").
    Qed.

    Lemma imp_unblockable_shorten' κ κ' lt :
      κ' ⊑ κ -∗ imp_unblockable [κ'] lt -∗ imp_unblockable [κ] lt.
    Proof.
      iIntros "#Hincl". iApply imp_unblockable_shorten.
      iIntros "!> (Hdead & _)".
      iMod (lft_incl_dead with "Hincl Hdead") as "Hdead'"; first done.
      iApply big_sepL_singleton. done.
    Qed.
  End unblockable.

  (** Ofty is trivially unblockable *)
  Lemma ofty_imp_unblockable {rt} (ty : type rt) κs :
    ⊢ imp_unblockable κs (◁ ty).
  Proof.
    iModIntro. iSplitR.
    - iIntros "*". rewrite ltype_own_core_equiv. simp_ltypes. eauto.
    - iIntros "*". rewrite ltype_own_core_equiv. simp_ltypes. eauto.
  Qed.

  (** The core is trivially unblockable *)
  Lemma core_imp_unblockable {rt} (lt : ltype rt) κs :
    ⊢ imp_unblockable κs (ltype_core lt).
  Proof.
    iModIntro. iSplitR.
    - iIntros "*". rewrite ltype_own_core_equiv. simp_ltypes. eauto.
    - iIntros "*". rewrite ltype_own_core_equiv. simp_ltypes. eauto.
  Qed.

  (** Blocked is unblockable *)
  Lemma blocked_imp_unblockable {rt} (ty : type rt) κ :
    ⊢ imp_unblockable [κ] (BlockedLtype ty κ).
  Proof.
    iModIntro. iSplitR.
    - iIntros (κ' γ' π r l) "(#Hdead & _) Hb/=".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_blocked_unfold ltype_own_ofty_unfold.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & Hsc & Hlb & Hb & Hcred & Hat)".
      iExists ly. iSplitR; first done. iSplitR; first done. iFrame "Hsc Hlb Hcred Hat".
      iMod ("Hb" with "Hdead") as "($ & Hb)". iApply "Hb".
    - iIntros (π r l) "(#Hdead & _)".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_blocked_unfold ltype_own_ofty_unfold.
      iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & Hinh)".
      iMod ("Hinh" with "Hdead") as "Hv".
      iDestruct "Hv" as "(%r' & Hrfn & >(%v & Hl & Hv))".
      iModIntro. iExists ly. iSplitR; first done. iSplitR; first done. iFrame "Hsc Hlb".
      iExists r'. iFrame "Hrfn". iModIntro. iExists v. iFrame.
  Qed.

  (** Shr Blocked is unblockable *)
  Lemma shr_blocked_imp_unblockable {rt} (ty : type rt) κ :
    ⊢ imp_unblockable [κ] (ShrBlockedLtype ty κ).
  Proof.
    iModIntro. iSplitR.
    - iIntros (κ' γ' π r l) "(#Hdead & _) Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_shrblocked_unfold ltype_own_ofty_unfold.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hobs & Hshr & Hinh & Hcred & Hat)".
      iExists ly. iFrame.
      iMod ("Hinh" with "Hdead") as "$". done.
    - iIntros (π r l) "(#Hdead & _) Hblocked".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite ltype_own_shrblocked_unfold ltype_own_ofty_unfold.
      iDestruct "Hblocked" as "(%ly & ? & ? & ? & ? & %r' & Hrfn & Hshr & Hunblock)".
      iMod ("Hunblock" with "Hdead") as "Hl".
      iDestruct "Hl" as "(%v & Hl & Hv)".
      iModIntro. iExists ly. iFrame.
      done.
  Qed.

  Lemma mut_ltype_imp_unblockable {rt} κs κ' (lt : ltype rt) :
    imp_unblockable κs lt -∗
    imp_unblockable κs (MutLtype lt κ').
  Proof.
    iIntros "#(Hub_mut & Hub_own)". iModIntro. iSplitL.
    - iIntros (κ0 γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & ? & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro. iModIntro.
      (*rewrite ltype_core_syn_type_eq.*)
      setoid_rewrite ltype_own_core_core.
      iApply (pinned_bor_impl with "[] Hb").
      iNext. iModIntro. iSplit; first last.
      { setoid_rewrite ltype_own_core_equiv. eauto. }
      iIntros "(%r' & Hauth & Hb)". iExists _. iFrame "Hauth".
      iMod "Hb". iDestruct "Hb" as "(%l' & Hl & Hb)".
      iMod ("Hub_mut" with "Hdead Hb") as "Hb"; first last.
      { iModIntro. rewrite ltype_own_core_equiv. eauto with iFrame. }
    - iIntros (π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? &  %γ & %r' & Hrfn & Hb)".
      iExists ly. iFrame.
      iModIntro.
      iMod "Hb" as "(%l' & Hl & Hb)".
      iExists _. iFrame. rewrite -ltype_own_core_equiv.
      iApply ("Hub_mut" with "Hdead Hb").
  Qed.

  Lemma shr_ltype_imp_unblockable {rt} κs κ' (lt : ltype rt) :
    imp_unblockable κs lt -∗
    imp_unblockable κs (ShrLtype lt κ').
  Proof.
    iIntros "#(Hub_mut & Hub_own)". iModIntro. iSplitL.
    - iIntros (κ0 γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & ? & ? & Hb)".
      iExists ly. iFrame.
      iMod "Hb". iModIntro. iModIntro.
      setoid_rewrite ltype_own_core_core.
      iApply (pinned_bor_impl with "[] Hb").
      iNext. iModIntro. iSplit; first last.
      { setoid_rewrite ltype_own_core_equiv. eauto. }
      iIntros "(%r' & Hauth & Hb)". iExists _. iFrame "Hauth".
      iMod "Hb". iDestruct "Hb" as "(%l' & Hl & Hb)".
      iExists _. iFrame.
      iApply (ltype_own_shared_to_core with "Hb").
    - iIntros (π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
      iDestruct "Hb" as "(%ly & ? & ? & ? & %r' & Hrfn & Hb)".
      iExists ly. iFrame.
      iModIntro.
      iMod "Hb" as "(%l' & Hl & Hb)".
      iExists _. iFrame.
      by iApply ltype_own_shared_to_core.
  Qed.

  Lemma struct_ltype_imp_unblockable {rts} κ (lts : hlist ltype rts) sls :
    ([∗ list] lt ∈ hzipl rts lts, imp_unblockable κ (projT2 lt)) ⊢
    imp_unblockable κ (StructLtype lts sls).
  Proof.
    set (map_core := (λ '(existT x (a, b)), existT x (ltype_core a, b) : sigT (λ rt, ltype rt * place_rfn rt)%type)).
    iIntros "#Hub". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hb" as "(%sl & %Halg & %Hlen & ? & ? & ? & ? & Hb)".
      iExists sl. iFrame. iR. iR.
      iMod "Hb". iModIntro.
      iApply (pinned_bor_impl' with "[] [] Hb").
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          iMod ("Ha").
          iApply big_sepL_fupd.
          iApply (big_sepL_impl with "Ha").
          iModIntro. iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          apply pad_struct_lookup_Some in Hlook; first last.
          { rewrite length_hpzipl -Hlen. erewrite struct_layout_spec_has_layout_fields_length;done. }
          destruct Hlook as (n & ly' & Hlook & [(? & Hlook1) | (-> & Hlook1)]).
          { simpl in *.
            apply (hpzipl_lookup_inv_hzipl_pzipl _ _ r') in Hlook1 as (Hlook1 & _).
            iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
            iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
            rewrite ltype_own_core_equiv. rewrite ltype_core_syn_type_eq. eauto 8 with iFrame.
          }
          { (* uninit *)
            injection Hlook1 => _ _ ?. subst.
            apply existT_inj in Hlook1. injection Hlook1 as -> ->.
            rewrite ltype_core_uninit. eauto 8. }
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          setoid_rewrite ltype_own_core_equiv.
          iMod ("Ha").
          iApply (big_sepL_impl with "Ha").
          iModIntro. iModIntro.
          iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          simp_ltypes. eauto 8 with iFrame.
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          setoid_rewrite ltype_own_core_equiv.
          iMod ("Ha").
          iApply (big_sepL_impl with "Ha").
          iModIntro. iModIntro.
          iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          simp_ltypes. eauto 8 with iFrame.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          rewrite hpzipl_hmap.
          rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
          { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
          rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
          setoid_rewrite ltype_own_core_equiv.
          iMod ("Ha").
          iApply (big_sepL_impl with "Ha").
          iModIntro. iModIntro.
          iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
          simp_ltypes. eauto 8 with iFrame.
    - iIntros (π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_struct_unfold /struct_ltype_own.
      iDestruct "Hb" as "(%sl & %Halg & %Hlen & ? &  ? & %r' & ? & Hb)".
      iExists sl. iFrame. iR. iR.
      iModIntro. iMod "Hb".
      rewrite hpzipl_hmap.
      rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, map_core (struct_make_uninit_ltype ly))); first last.
      { intros ?. rewrite /map_core /struct_make_uninit_ltype. rewrite ltype_core_uninit//. }
      rewrite (pad_struct_fmap _ _ _ map_core) big_sepL_fmap.
      iApply big_sepL_fupd.
      iApply (big_sepL_impl with "Hb").
      iModIntro. iIntros (k [rt [lt r'']] Hlook) "(%ly & ? & ? & Hl)". simpl.
      apply pad_struct_lookup_Some in Hlook; first last.
      { rewrite length_hpzipl -Hlen. erewrite struct_layout_spec_has_layout_fields_length;done. }
      destruct Hlook as (n & ly' & Hlook & [(? & Hlook1) | (-> & Hlook1)]).
      {
        apply (hpzipl_lookup_inv_hzipl_pzipl _ _ r') in Hlook1 as (Hlook1 & _).
        iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
        iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
        rewrite ltype_own_core_equiv. rewrite ltype_core_syn_type_eq. eauto 8 with iFrame.
      }
      { (* uninit *)
        injection Hlook1 => _ _ ?. subst.
        apply existT_inj in Hlook1. injection Hlook1 as -> ->.
        rewrite ltype_core_uninit. eauto 8. }
  Qed.

  Lemma array_ltype_imp_unblockable {rt} κs (def : type rt) len (lts : list (nat * ltype rt)) :
    ([∗ list] lt ∈ (interpret_iml (◁ def) len lts), imp_unblockable κs lt) -∗
    imp_unblockable κs (ArrayLtype def len lts).
  Proof.
    iIntros "#Hub". iModIntro. iSplitL.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_array_unfold /array_ltype_own.
      iDestruct "Hb" as "(%sl & %Halg & % & % & ? & ? & ? & Hb)".
      iExists sl. iFrame. iR. iR. iR.
      iMod "Hb". iModIntro.
      iApply (pinned_bor_impl' with "[] [] Hb").
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)).
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          iMod ("Ha") as "(%Hlen & Ha)". iR.
          iApply big_sepL2_fupd.
          iApply (big_sepL2_impl with "Ha").
          iModIntro. iIntros (k lt r'' Hlook1 Hlook2) "(%Hst & Hl)".
          simp_ltypes. iR.
          iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
          iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
          rewrite ltype_own_core_equiv. done.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)) in "Ha".
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          setoid_rewrite ltype_core_syn_type_eq.
          setoid_rewrite ltype_own_core_equiv. done.
      + iNext. iModIntro. iSplit.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)).
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          setoid_rewrite ltype_core_syn_type_eq.
          setoid_rewrite ltype_own_core_equiv.
          setoid_rewrite ltype_core_idemp. done.
        * iIntros "(%r' & ? & Ha)". iExists r'. iFrame.
          iEval (rewrite -(ltype_core_ofty def)) in "Ha".
          rewrite interpret_iml_fmap big_sepL2_fmap_l.
          setoid_rewrite ltype_core_syn_type_eq.
          setoid_rewrite ltype_own_core_equiv.
          setoid_rewrite ltype_core_idemp. done.
    - iIntros (π r l) "#Hdead Hb".
      rewrite ltype_own_core_equiv /=. simp_ltypes.
      rewrite !ltype_own_array_unfold /array_ltype_own.
      iDestruct "Hb" as "(%ly & %Halg & % & % & ? & %r' & ? & Hb)".
      iExists ly. iFrame. iR. iR. iR. iModIntro.
      iEval (rewrite -(ltype_core_ofty def)).
      rewrite interpret_iml_fmap big_sepL2_fmap_l.
      iMod ("Hb") as "(%Hlen & Ha)". iR.
      iApply big_sepL2_fupd.
      iApply (big_sepL2_impl with "Ha").
      iModIntro. iIntros (k lt r'' Hlook1 Hlook2) "(%Hst & Hl)".
      simp_ltypes. iR.
      iPoseProof (big_sepL_lookup with "Hub") as "Hub'"; first done. simpl.
      iDestruct "Hub'" as "(_ & #Hub_own)". iMod ("Hub_own" with "Hdead Hl") as "Hl".
      rewrite ltype_own_core_equiv. done.
  Qed.

  Lemma enum_ltype_imp_unblockable {rt} κs (en : enum rt) (variant : option enum_ltype_variant) :
    (match variant with
    | Some v => imp_unblockable κs v.(eltv_ltype)
    | None => True%I
    end) -∗
    imp_unblockable κs (EnumLtype en variant).
  Proof.
    destruct variant as [variant | ].
    - destruct variant as [tag rte lte re].
      iIntros "#Hub". iModIntro. iSplitL.
      + iIntros (κ' γ' π r l) "#Hdead Hb".
        rewrite ltype_own_core_equiv /=. simp_ltypes.
        rewrite !ltype_own_enum_unfold /enum_ltype_own.
        iDestruct "Hb" as "(%el & %Halg & %Hly & Hlb & Hcred & Hrfn & Hb)".
        iExists el. iFrame. iR. iR.
        iMod "Hb". iModIntro.
        iApply (pinned_bor_impl' with "[] [] Hb").
        * iNext. iModIntro. iSplit.
          -- iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
             iMod "Hb" as "(%variant_ly & %Hcompat & %Hlookup & %Hst & Htag & Hpad & Hpayload & Htail)".
             iDestruct "Hub" as "(_ & Hub)".
             unfold interp_enum_ltype_variant. simpl.
             simpl in *.
             destruct (decide (enum_tag en r' = Some tag)); simpl; last by iFrame.
             iMod ("Hub" with "Hdead Hpayload") as "Hpayload".
             iModIntro. iExists variant_ly. iR.
             iSplitR; first done.
             iEval (rewrite ltype_own_core_equiv) in "Hpayload".
             iFrame "Htag Hpad Htail Hpayload". simpl in *.
             rewrite ltype_core_syn_type_eq//.
          -- iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
             iMod "Hb" as "(%variant_ly & %Hcompat & %Hlookup & %Hst & Htag & Hpad & Hpayload & Htail)".
             setoid_rewrite ltype_own_core_equiv.
             simpl in *.
             destruct (decide (enum_tag en r' = Some tag)); simpl in *.
             2: { iFrame. iR. iR. iR. simp_ltypes. done. }
             iModIntro. iExists variant_ly. iR.
             iSplitR; first done. simpl in *.
             iFrame. rewrite ltype_core_syn_type_eq in Hst. done.
        * iNext. iModIntro. iSplit.
          -- iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
             iMod "Hb" as "(%variant_ly & %Hcompat & %Hlookup & %Hst & Htag & Hpad & Hpayload & Htail)".
             setoid_rewrite ltype_own_core_equiv.
             simpl in *.
             destruct (decide (enum_tag en r' = Some tag)); simpl in *; last by iFrame.
             iModIntro. iExists variant_ly. iR.
             iSplitR; first done.
             rewrite ltype_core_idemp.
             simpl in *.
             iFrame. rewrite ltype_core_syn_type_eq//.
          -- iIntros "(%r' & Hauth & Hb)". iExists r'. iFrame "Hauth".
             iMod "Hb" as "(%variant_ly & %Hcompat & %Hlookup & %Hst & Htag & Hpad & Hpayload & Htail)".
             setoid_rewrite ltype_own_core_equiv.
             simpl in *.
             destruct (decide (enum_tag en r' = Some tag)); simpl in *.
             2: { iFrame. simp_ltypes. iR. iR. done. }
             iModIntro. iExists variant_ly. iR.
             iSplitR; first done.
             rewrite ltype_core_idemp.
             simpl in *.
             iFrame. rewrite ltype_core_syn_type_eq in Hst. done.
      + iIntros (π r l) "#Hdead Hb".
        rewrite ltype_own_core_equiv /=. simp_ltypes.
        rewrite !ltype_own_enum_unfold /enum_ltype_own.
        iDestruct "Hb" as "(%el & %Halg & %Hly & Hlb & %r' & Hr & Hb)".
        iMod "Hb" as "(%variant_ly & %Hcompat & %Hlookup & %Hst & Htag & Hpad & Hpayload & Htail)".
        iDestruct "Hub" as "(_ & #Hub_own)".
        iModIntro. iExists el. iR. iR. iFrame "Hlb". iExists r'. iFrame "Hr".
        simpl in *.
        destruct (decide (enum_tag en r' = Some tag)); simpl in *.
        2: { iFrame. simp_ltypes. iR. iR. done. }
        iMod ("Hub_own" with "Hdead Hpayload") as "Hpayload".
        iEval (rewrite ltype_own_core_equiv) in "Hpayload".
        iModIntro. iExists variant_ly. iR.
        simpl in *. iFrame.
        iR.
        iPureIntro. rewrite ltype_core_syn_type_eq. done.
    - iIntros "_". rewrite -(ltype_core_enum en None). iApply core_imp_unblockable.
  Qed.


  (* Unblocking is trivial for OpenedLtype, since the core is trivial.
     However, that also doesn't buy us much, since we will anyways never have OpenedLtype below an intact mutable reference.
  *)
  Lemma opened_ltype_imp_unblockable {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost κs :
    ⊢ imp_unblockable κs (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost).
  Proof.
    iModIntro. iSplitL.
    - iIntros (κ' ????). rewrite ltype_own_core_equiv ltype_core_opened. eauto.
    - iIntros (???). rewrite ltype_own_core_equiv ltype_core_opened. eauto.
  Qed.

  Lemma coreable_ltype_imp_unblockable {rt_full} (lt_full : ltype rt_full) κs :
    ⊢ imp_unblockable κs (CoreableLtype κs lt_full).
  Proof.
    iModIntro. iSplitL.
    - iIntros (κ' γ π r l) "#Hdead Hb".
      rewrite ltype_own_core_coreable_unfold ltype_own_coreable_unfold /coreable_ltype_own.
      iDestruct "Hb" as "(%ly & _ & _ & _ & Hrfn & Hvs)".
      iApply ("Hvs" with "Hdead Hrfn").
    - iIntros (π r l) "Hdead Ha".
      rewrite ltype_own_core_coreable_unfold ltype_own_coreable_unfold /coreable_ltype_own.
      iDestruct "Ha" as "(%ly & _ & _ & _ & Ha)".
      iApply ("Ha" with "Hdead").
  Qed.

  Lemma alias_ltype_imp_unblockable rt st l κs :
    ⊢ imp_unblockable κs (AliasLtype rt st l).
  Proof.
    iModIntro. iSplitL.
    - iIntros (?????). rewrite ltype_own_core_equiv ltype_core_alias. eauto.
    - iIntros (???). rewrite ltype_own_core_equiv ltype_core_alias. eauto.
  Qed.

  Lemma shadowed_ltype_imp_unblockable {rt_cur rt_full} (lt_cur : ltype rt_cur) (r_cur : place_rfn rt_cur) (lt_full : ltype rt_full) κs :
    imp_unblockable κs lt_full -∗ imp_unblockable κs (ShadowedLtype lt_cur r_cur lt_full).
  Proof.
    iIntros "#(Ha1 & Ha2)".
    iModIntro. iSplitL.
    - iIntros (?????). rewrite ltype_own_core_equiv ltype_own_shadowed_unfold. simp_ltypes.
      iIntros "Hdead (_ & Hb)".
      rewrite -ltype_own_core_equiv. iApply ("Ha1" with "Hdead Hb").
    - iIntros (???). rewrite ltype_own_core_equiv ltype_own_shadowed_unfold. simp_ltypes.
      iIntros "Hdead (_ & Hb)".
      rewrite -ltype_own_core_equiv. iApply ("Ha2" with "Hdead Hb").
  Qed.

  Lemma opened_na_ltype_imp_unblockable {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost κs :
    ⊢ imp_unblockable κs (OpenedNaLtype lt_cur lt_inner Cpre Cpost).
  Proof.
    iModIntro. iSplitL.
    - iIntros (κ' ????). rewrite ltype_own_core_equiv ltype_core_opened_na. eauto.
    - iIntros (???). rewrite ltype_own_core_equiv ltype_core_opened_na. eauto.
  Qed.

  (** Once all the blocked lifetimes are dead, every ltype is unblockable to its core. *)
  Lemma imp_unblockable_blocked_dead {rt} (lt : ltype rt) :
    ⊢ imp_unblockable (ltype_blocked_lfts lt) lt.
  Proof.
    (* TODO is there a way to use this dependent induction principle directly with iInduction or induction? *)
    move: rt lt. eapply ltype_induction.
    - iIntros (rt ty κ). cbn. iApply blocked_imp_unblockable.
    - iIntros (rt ty κ). iApply shr_blocked_imp_unblockable.
    - iIntros (rt ty). iApply ofty_imp_unblockable.
    - iIntros (rt st l). iApply alias_ltype_imp_unblockable.
    - iIntros (rt lt IH κ). iApply mut_ltype_imp_unblockable. by iApply IH.
    - iIntros (rt lt IH κ). iApply shr_ltype_imp_unblockable. by iApply IH.
    - iIntros (rts lts IH sls).
      iApply (struct_ltype_imp_unblockable _ lts sls).
      iApply big_sepL_intro. iModIntro. iIntros (k [rt lt] Hlook).
      iApply imp_unblockable_shorten; first last.
      { iApply IH. by eapply list_elem_of_lookup_2. }
      simpl. clear -Hlook.
      unfold ltype_blocked_lfts. simpl.
      iModIntro. rewrite /lft_dead_list.
      iInduction lts as [ | X Xl lt' lts ] "IH" forall (k Hlook); simpl; first done.
      destruct k as [ | k]; simpl in Hlook.
      + injection Hlook as Heq Heq2; subst. apply existT_inj in Heq2 as ->.
        rewrite big_sepL_app. by iIntros "($ & _)".
      + iIntros "Ha". iApply "IH"; first done.
        rewrite big_sepL_app. iDestruct "Ha" as "(_ & $)".
    - iIntros (rt def len lts IH ).
      iApply array_ltype_imp_unblockable.
      iApply big_sepL_intro. iModIntro. iIntros (k lt Hlook).
      apply lookup_interpret_iml_Some_inv in Hlook as (? & [-> | Hel]).
      + iApply ofty_imp_unblockable.
      + iApply imp_unblockable_shorten; first last.
        { iApply IH. done. }
        simpl. rewrite /ltype_blocked_lfts /=. iModIntro.
        iIntros "Hdead". clear -Hel.
        iInduction lts as [ | lt' lts ] "IH" forall (k Hel).
        { by apply elem_of_nil in Hel. }
        apply elem_of_cons in Hel as [<- | Hel].
        * simpl. rewrite lft_dead_list_app. by iDestruct "Hdead" as "($ & _)".
        * simpl. rewrite lft_dead_list_app. iDestruct "Hdead" as "(_ & Hdead)".
          by iApply "IH".
    - iIntros (rt en variant Hub).
      iApply enum_ltype_imp_unblockable.
      simpl.
      rewrite /ltype_blocked_lfts/=.
      destruct variant; simpl; done.
    - iIntros (rt_cur rt_inner rt_full lt_cur lt_inner ty_full Cpre R Cpost IH1 IH2).
      iApply opened_ltype_imp_unblockable.
    - iIntros (rt_full κ' lt_full Hdead). iApply coreable_ltype_imp_unblockable.
    - iIntros (rt_cur rt_full lt_cur r_cur lt_full _ Hub).
      iApply shadowed_ltype_imp_unblockable. done.
    - iIntros (rt_cur rt_inner lt_cur lt_inner Cpre R Cpost IH).
      iApply opened_na_ltype_imp_unblockable.
  Qed.

  (** We can essentiallly rewrite with [ltype_eq] when proving [imp_unblockable]. *)
  Lemma ltype_eq_imp_unblockable {rt} κs (lt1 lt2 : ltype rt) :
    (∀ b r, ltype_eq b r r lt1 lt2) -∗
    imp_unblockable κs lt1 -∗
    imp_unblockable κs lt2.
  Proof.
    (*iIntros "((% & #Hi1 & #Hc1) & (_ & #Hi2 & #Hc2)) (#Hub1 & #Hub2)". *)
    iIntros "#Heq (#Hub1 & #Hub2)".
    iSplitL; iModIntro.
    - iIntros (κ' γ' π r l) "#Hdead Hb".
      iDestruct ("Heq" $! (Uniq κ' γ') r) as "((#Hi1 & #Hc1) & (#Hi2 & #Hc2))".
      iDestruct ("Hub1" with "Hdead") as "#Hub1'".
      iApply ltype_own_core_equiv. iApply "Hc1". iApply ltype_own_core_equiv.
      iApply "Hub1'". by iApply "Hi2".
    - iIntros (π r l) "#Hdead Hb".
      iDestruct ("Heq" $! (Owned) r) as "((#Hi1 & #Hc1) & (#Hi2 & #Hc2))".
      iMod ("Hi2" with "Hb") as "Hb".
      iMod ("Hub2" with "Hdead Hb") as "Hb".
      rewrite !ltype_own_core_equiv. by iApply "Hc1".
  Qed.
  (** A particular instance: when we unfold a type to an ltype, this should always be unblockable. *)
  Lemma ltype_eq_imp_unblockable_ofty {rt} κs ty (lt : ltype rt) :
    (∀ b r, ltype_eq b r r (◁ ty)%I lt) -∗
    imp_unblockable κs lt.
  Proof.
    iIntros "Heq". iApply (ltype_eq_imp_unblockable with "Heq").
    iApply ofty_imp_unblockable.
  Qed.

  Lemma imp_unblockable_use π F κs {rt} (lt : ltype rt) (r : place_rfn rt) l bk :
    lftE ⊆ F →
    imp_unblockable κs lt -∗
    lft_dead_list κs -∗
    l ◁ₗ[π, bk] r @ lt ={F}=∗ l ◁ₗ[π, bk] r @ ltype_core lt.
  Proof.
    iIntros (?) "(#Hub_uniq & #Hub_owned) Hdead Hl".
    destruct bk.
    - iMod (fupd_mask_mono with "(Hub_owned Hdead Hl)") as "Hl"; first done.
      rewrite ltype_own_core_equiv. done.
    - iApply (ltype_own_shared_to_core with "Hl").
    - iMod (fupd_mask_mono with "(Hub_uniq Hdead Hl)") as "Hl"; first done.
      rewrite ltype_own_core_equiv. done.
  Qed.

  Lemma unblock_blocked {rt} E κ π l b (ty : type rt) r :
    lftE ⊆ E →
    [† κ] -∗
    l ◁ₗ[π, b] r @ (BlockedLtype ty κ) ={E}=∗ l ◁ₗ[π, b] r @ (◁ ty)%I.
  Proof.
    iIntros (?) "Hdead Hl".
    iPoseProof (blocked_imp_unblockable ty κ) as "Ha".
    iMod (imp_unblockable_use with "Ha [$Hdead//] Hl") as "Hb"; first done.
    simp_ltypes. done.
  Qed.
  Lemma unblock_shrblocked {rt} E κ π l b (ty : type rt) r :
    lftE ⊆ E →
    [† κ] -∗
    l ◁ₗ[π, b] r @ (ShrBlockedLtype ty κ) ={E}=∗ l ◁ₗ[π, b] r @ (◁ ty)%I.
  Proof.
    iIntros (?) "Hdead Hl".
    iPoseProof (shr_blocked_imp_unblockable ty κ) as "Ha".
    iMod (imp_unblockable_use with "Ha [$Hdead//] Hl") as "Hb"; first done.
    simp_ltypes. done.
  Qed.
  Lemma unblock_coreable {rt} F π (lt_full : ltype rt) r κs l b :
    lftE ⊆ F →
    lft_dead_list κs -∗
    l ◁ₗ[π, b] r @ CoreableLtype κs lt_full ={F}=∗
    l ◁ₗ[π, b] r @ ltype_core lt_full.
  Proof.
    iIntros (?) "Hdead Hl".
    iPoseProof (coreable_ltype_imp_unblockable lt_full κs) as "Ha".
    iMod (imp_unblockable_use with "Ha [$Hdead//] Hl") as "Hb"; first done.
    simp_ltypes. done.
  Qed.
End blocked.
