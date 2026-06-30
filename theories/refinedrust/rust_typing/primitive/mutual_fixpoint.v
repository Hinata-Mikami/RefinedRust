From refinedrust Require Import type programs.
From refinedrust Require Import options.
Require Import Stdlib.Program.Equality.

Import EqNotations.

Set Universe Polymorphism.

(** Guarded mutual recursive types.

    This file intentionally mirrors the front matter of [fixpoint.v], but keeps
    the development isolated while the mutually-recursive construction is being
    connected to the generator.

    The unary [type_fixpoint] in [fixpoint.v] cannot be generalized by taking a
    completion of [hlist type rts] directly: [type] is an OFE, but the existing
    construction only completes the guarded ownership/sharing predicates.  The
    mutual construction therefore has to do the same thing componentwise for an
    SCC, while copying metadata, syntactic types, sideconditions, lifetimes, and
    well-formedness environments from suitable finite approximants.
*)

Section mutual_fixpoint_defs.
  Context `{!typeGS Σ}.

  Definition mut_types (rts : list RT) : Type := hlist type rts.

  Definition mut_typeO (rts : list RT) : ofe :=
    hlistO (λ rt : RT, typeO (rt:=rt)) rts.

  Definition mut_ty_own_shrO (rts : list RT) : ofe :=
    hlistO (λ rt : RT,
      prodO (thread_id -d> rt -d> metadataO -d> val -d> iPropO Σ)
            (lft -d> thread_id -d> rt -d> metadataO -d> loc -d> iPropO Σ)) rts.

  Definition mut_type_fun (rts : list RT) : Type :=
    mut_types rts → mut_types rts.

  (** Finite approximants for one mutually-recursive SCC.

      As in [fixpoint.v], [0] already means one application of the functor.
      This makes all non-guarded fields come from functor-produced types rather
      than from the initial hlist.
   *)
  Fixpoint mut_type_base {rts : list RT}
      (Hrts : TCTForall (λ rt, Inhabited (RT_xt rt)) rts) : mut_types rts :=
    match Hrts with
    | TCTForall_nil _ => +[]
    | TCTForall_cons _ rt rts _ Hrts' => type_inhabitant +:: mut_type_base Hrts'
    end.

  Definition mut_type_approximant {rts : list RT} (F : mut_type_fun rts)
      (base : mut_types rts) (n : nat) : mut_types rts :=
    Nat.iter (S n) F base.

  Definition mut_Fn {rts : list RT} (F : mut_type_fun rts)
      (base : mut_types rts) (n : nat) : mut_types rts :=
    mut_type_approximant F base n.

  Definition mut_Fn_canon {rts : list RT} (F : mut_type_fun rts)
      (Hrts : TCTForall (λ rt, Inhabited (RT_xt rt)) rts) (n : nat) : mut_types rts :=
    mut_Fn F (mut_type_base Hrts) n.

  Lemma mut_Fn_0 {rts : list RT} (F : mut_type_fun rts)
      (base : mut_types rts) :
    mut_Fn F base 0 = F base.
  Proof. done. Qed.

  Lemma mut_Fn_succ {rts : list RT} (F : mut_type_fun rts)
      (base : mut_types rts) n :
    mut_Fn F base (S n) = F (mut_Fn F base n).
  Proof. done. Qed.

  Definition mut_component {rts : list RT} (default_rt : RT)
      (default : type default_rt) (tys : mut_types rts) (i : nat) :
      type (lnth default_rt rts i) :=
    hnth default tys i.

  Definition mut_type_project_def {rts : list RT} (tys : mut_types rts)
      {rt : RT} `{!Inhabited (RT_xt rt)} (i : nat)
      (Hlook : rts !! i = Some rt) : type rt :=
    rew [type] (lookup_lnth rts rt i rt Hlook) in
      mut_component rt type_inhabitant tys i.
  Definition mut_type_project_aux : seal (@mut_type_project_def). Proof. by eexists. Qed.
  Definition mut_type_project := mut_type_project_aux.(unseal).
  Definition mut_type_project_unfold : @mut_type_project = @mut_type_project_def :=
    mut_type_project_aux.(seal_eq).
  Global Arguments mut_type_project {_} _ {_} {_} _ _.

  Definition mut_own_shr_of_type {rt : RT} (ty : type rt) :
      prodO (thread_id -d> rt -d> metadataO -d> val -d> iPropO Σ)
            (lft -d> thread_id -d> rt -d> metadataO -d> loc -d> iPropO Σ) :=
    (ty.(ty_own_val), ty.(ty_shr)).

  Definition mut_own_shr_of_types {rts : list RT} (tys : mut_types rts) :
      mut_ty_own_shrO rts :=
    hmap (λ _ ty, mut_own_shr_of_type ty) tys.

  Definition HTypeDist {rts : list RT} n : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ rt, TypeDist (rt:=rt) n).

  Definition HTypeDist2 {rts : list RT} n : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ rt, TypeDist2 (rt:=rt) n).

  Definition HTypeDistLater {rts : list RT} n : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ rt, TypeDistLater (rt:=rt) n).

  Definition HTypeDistLater2 {rts : list RT} n : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ rt, TypeDistLater2 (rt:=rt) n).

  Definition HTypeSynTypeEq {rts : list RT} : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ _ ty ty', ∀ m, ty_syn_type ty m = ty_syn_type ty' m).

  Definition HTypeSidecondEq {rts : list RT} : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ _ ty ty', ty_sidecond ty ≡ ty_sidecond ty').

  Definition HTypeLftsEquiv {rts : list RT} : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ _ ty ty',
      ⊢ lft_equiv (lft_intersect_list (ty_lfts ty))
          (lft_intersect_list (ty_lfts ty'))).

  Definition HTypeWfEEquiv {rts : list RT} : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ _ ty ty', elctx_interp (ty_wf_E ty) ≡ elctx_interp (ty_wf_E ty')).

  Definition HTypeHasOpTypeEq {rts : list RT} : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ _ ty ty', ∀ ot, ty_has_op_type ty ot ↔ ty_has_op_type ty' ot).

  Lemma HTypeSynTypeEq_tail {rt rts} (tys tys' : mut_types (rt :: rts)) :
    HTypeSynTypeEq tys tys' → HTypeSynTypeEq (hlist_tail tys) (hlist_tail tys').
  Proof. intros H; dependent destruction H; done. Qed.

  Lemma HTypeSidecondEq_tail {rt rts} (tys tys' : mut_types (rt :: rts)) :
    HTypeSidecondEq tys tys' → HTypeSidecondEq (hlist_tail tys) (hlist_tail tys').
  Proof. intros H; dependent destruction H; done. Qed.

  Lemma HTypeLftsEquiv_tail {rt rts} (tys tys' : mut_types (rt :: rts)) :
    HTypeLftsEquiv tys tys' → HTypeLftsEquiv (hlist_tail tys) (hlist_tail tys').
  Proof. intros H; dependent destruction H; done. Qed.

  Lemma HTypeWfEEquiv_tail {rt rts} (tys tys' : mut_types (rt :: rts)) :
    HTypeWfEEquiv tys tys' → HTypeWfEEquiv (hlist_tail tys) (hlist_tail tys').
  Proof. intros H; dependent destruction H; done. Qed.

  Lemma HTypeHasOpTypeEq_tail {rt rts} (tys tys' : mut_types (rt :: rts)) :
    HTypeHasOpTypeEq tys tys' → HTypeHasOpTypeEq (hlist_tail tys) (hlist_tail tys').
  Proof. intros H; dependent destruction H; done. Qed.

  Lemma HForallTwo_combine {A} {F G : A → Type} {Xl}
      (P Q R : ∀ X, F X → G X → Prop) (xs : hlist F Xl) (ys : hlist G Xl) :
    (∀ X x y, P X x y → Q X x y → R X x y) →
    HForallTwo P xs ys → HForallTwo Q xs ys → HForallTwo R xs ys.
  Proof.
    intros HR HP. revert Q R HR.
    induction HP; intros Q R HR HQ; dependent destruction HQ; constructor.
    - eapply HR; done.
    - eapply IHHP; done.
  Qed.

  Class MutTypeNonExpansive {rts : list RT} (F : mut_type_fun rts) : Type := {
    mut_type_ne : ∀ n tys tys',
      HTypeDist n tys tys' → HTypeDist n (F tys) (F tys');
    mut_type_ne2 : ∀ n tys tys',
      HTypeDist2 n tys tys' → HTypeDist2 n (F tys) (F tys');
  }.

  Class MutTypeContractive {rts : list RT} (F : mut_type_fun rts) : Type := {
    mut_type_ctr_syn_type : ∀ tys tys',
      HTypeSynTypeEq (F tys) (F tys');
    mut_type_ctr_sidecond : ∀ tys tys',
      HTypeSynTypeEq tys tys' → HTypeSidecondEq (F tys) (F tys');
    mut_type_ctr_lfts_idempotent : ∀ tys,
      HTypeLftsEquiv (F (F tys)) (F tys);
    mut_type_ctr_wf_E_idempotent : ∀ tys,
      HTypeWfEEquiv (F (F tys)) (F tys);
    mut_type_ctr_has_op_type : ∀ tys tys',
      HTypeHasOpTypeEq (F tys) (F tys');
    mut_type_ctr_dist : ∀ n tys tys',
      HTypeDist2 n tys tys' → HTypeDist n (F tys) (F tys');
    mut_type_ctr_dist2 : ∀ n tys tys',
      HTypeDistLater2 n tys tys' → HTypeDist2 n (F tys) (F tys');
  }.

  Global Instance mut_type_contractive_ne {rts : list RT} (F : mut_type_fun rts) :
    MutTypeContractive F → MutTypeNonExpansive F.
  Proof.
    intros Hctr. constructor.
    - intros n tys tys' Hdist.
      eapply mut_type_ctr_dist. eapply HForallTwo_impl; last done.
      intros rt ty ty' ?. apply type_dist_dist2. done.
    - intros n tys tys' Hdist.
      eapply mut_type_ctr_dist2. eapply HForallTwo_impl; last done.
      intros rt ty ty' Hty. apply type_dist2_later.
      destruct Hty as [Hst Hsc Hown Hshr]. constructor; [done.. | | ].
      + intros. eapply dist_later_mono; first apply Hown. lia.
      + intros. eapply dist_le; first apply Hshr. lia.
  Qed.

  Lemma mut_Fn_syn_type_const {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n m :
    HTypeSynTypeEq (mut_Fn F base n) (mut_Fn F base m).
  Proof.
    destruct n; destruct m; rewrite /mut_Fn /mut_type_approximant /=;
      apply mut_type_ctr_syn_type.
  Qed.

  Lemma mut_Fn_sidecond_const {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n :
    n ≥ 1 → HTypeSidecondEq (mut_Fn F base n) (mut_Fn F base 1).
  Proof.
    intros Hn.
    destruct n as [|n]; first lia.
    destruct n as [|n].
    { unfold HTypeSidecondEq. apply HForallTwo_reflexive.
      intros X ty. reflexivity. }
    rewrite !mut_Fn_succ.
    eapply (@mut_type_ctr_sidecond rts F MutTypeContractive0).
    apply (@mut_Fn_syn_type_const rts F MutTypeContractive0 base).
  Qed.

  Lemma mut_Fn_lfts_const_0 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n :
    HTypeLftsEquiv (mut_Fn F base n) (mut_Fn F base 0).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    destruct n as [|[|n]].
    - unfold HTypeLftsEquiv. apply HForallTwo_reflexive.
      intros X ty. iApply lft_equiv_refl.
    - rewrite mut_Fn_succ mut_Fn_0. apply mut_type_ctr_lfts_idempotent.
    - rewrite !mut_Fn_succ.
      eapply HForallTwo_transitive.
      { intros rt ty1 ty2 ty3 H12 H23.
        iApply lft_equiv_trans; first iApply H12. iApply H23. }
      { eapply (@mut_type_ctr_lfts_idempotent rts F MutTypeContractive0). }
      apply (IH (S n)). lia.
  Qed.

  Lemma mut_Fn_wf_E_const_1 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n :
    n ≥ 1 → HTypeWfEEquiv (mut_Fn F base n) (mut_Fn F base 1).
  Proof.
    intros Hn.
    induction n as [n IH] using lt_wf_ind.
    destruct n as [|[|n]].
    - lia.
    - unfold HTypeWfEEquiv. apply HForallTwo_reflexive.
      intros X ty. reflexivity.
    - rewrite !mut_Fn_succ.
      eapply HForallTwo_transitive.
      { intros rt ty1 ty2 ty3 H12 H23. etrans; done. }
      { eapply (@mut_type_ctr_wf_E_idempotent rts F MutTypeContractive0). }
      apply (IH (S n)); lia.
  Qed.

  Lemma mut_Fn_has_op_type_const {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n m :
    HTypeHasOpTypeEq (mut_Fn F base n) (mut_Fn F base m).
  Proof.
    destruct n; destruct m; rewrite /mut_Fn /mut_type_approximant /=;
      apply mut_type_ctr_has_op_type.
  Qed.

  Definition HTypeOwnShrCauchy {rts : list RT} n : mut_types rts → mut_types rts → Prop :=
    HForallTwo (λ rt ty ty',
      (∀ π r m v, dist_later n (v ◁ᵥ{π, m} r @ ty)%I (v ◁ᵥ{π, m} r @ ty')%I) ∧
      (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ ty)%I ≡{n}≡ (l ◁ₗ{π, m, κ} r @ ty')%I)).

  Lemma mut_Fn_dist_later2_0 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n m :
    n ≥ 1 → m ≥ 1 →
    HTypeDistLater2 0 (mut_Fn F base n) (mut_Fn F base m).
  Proof.
    intros Hn Hm.
    eapply HForallTwo_combine.
    { intros rt ty ty' Hst Hsc. constructor.
      - apply Hst.
      - apply Hsc.
      - intros. dist_later_2_intro. lia.
      - intros. dist_later_intro. unfold_sidx. lia. }
    - eapply (@mut_Fn_syn_type_const rts F MutTypeContractive0 base).
    - eapply (@HForallTwo_transitive RT (λ rt, type rt) rts
        (λ rt ty ty', ty_sidecond ty ≡ ty_sidecond ty')).
      { intros rt ty1 ty2 ty3 H12 H23. etrans; done. }
      + eapply (@mut_Fn_sidecond_const rts F MutTypeContractive0 base); lia.
      + eapply (@HForallTwo_symmetric RT (λ rt, type rt) rts
          (λ rt ty ty', ty_sidecond ty ≡ ty_sidecond ty')).
        { intros rt ty1 ty2 H. symmetry. done. }
        eapply (@mut_Fn_sidecond_const rts F MutTypeContractive0 base); lia.
  Qed.

  Lemma mut_ty_own_shr_cauchy_dist2 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) (i n : nat) :
    n ≤ i →
    HTypeDist2 n (mut_Fn F base (2 + i)) (mut_Fn F base (2 + n)).
  Proof.
    induction n as [|n IH] in i |-*; intros Hle.
    - eapply (@mut_type_ctr_dist2 rts F MutTypeContractive0).
      change (HTypeDistLater2 0 (mut_Fn F base (1 + i)) (mut_Fn F base 1)).
      eapply (@mut_Fn_dist_later2_0 rts F MutTypeContractive0 base); lia.
    - destruct i; first lia.
      eapply (@mut_type_ctr_dist2 rts F MutTypeContractive0).
      eapply HForallTwo_impl; last first.
      { eapply IH. lia. }
      intros rt ty ty' Hdist. apply type_dist2_later.
      destruct Hdist as [Hst Hsc Hown Hshr]. constructor; [done.. | | ].
      + intros. eapply dist_later_mono; first apply Hown. lia.
      + intros. eapply dist_le; first apply Hshr. lia.
  Qed.

  (* We have the [2+] in order to fix up the [0] base case, exactly as in
     the unary construction in [fixpoint.v]. *)
  Lemma mut_ty_own_shr_cauchy {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) (i n : nat) :
    n ≤ i →
    HTypeOwnShrCauchy n (mut_Fn F base (2 + i)) (mut_Fn F base (2 + n)).
  Proof.
    intros Hle.
    unfold HTypeOwnShrCauchy.
    eapply (@HForallTwo_impl RT (λ rt, type rt) (λ rt, type rt) rts
      (λ rt, TypeDist2 (rt:=rt) n)
      (λ rt ty ty',
        (∀ π r m v, dist_later n (v ◁ᵥ{π, m} r @ ty)%I (v ◁ᵥ{π, m} r @ ty')%I) ∧
        (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ ty)%I ≡{n}≡ (l ◁ₗ{π, m, κ} r @ ty')%I))).
    { intros rt ty ty' Hdist.
      destruct Hdist as [_ _ Hown Hshr]. split; [exact Hown | exact Hshr]. }
    eapply (@mut_ty_own_shr_cauchy_dist2 rts F MutTypeContractive0 base). done.
  Qed.

  Lemma mut_own_shr_of_types_dist {rts : list RT} n (tys tys' : mut_types rts) :
    HTypeOwnShrCauchy (S n) tys tys' →
    mut_own_shr_of_types tys ≡{n}≡ mut_own_shr_of_types tys'.
  Proof.
    unfold HTypeOwnShrCauchy, mut_own_shr_of_types.
    induction 1; constructor; simpl; [|done].
    destruct H as [Hown Hshr]. constructor; simpl.
    - intros ????. eapply dist_later_lt; first eapply Hown. unfold_sidx. lia.
    - intros ?????. eapply dist_le; first eapply Hshr. lia.
  Qed.

  (* [3+] because that is what we need to apply [mut_ty_own_shr_cauchy]
     when proving that the chain is Cauchy, exactly as in [fixpoint.v]. *)
  Program Definition mut_ty_own_shr_chain {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) : chain (mut_ty_own_shrO rts) := {|
    chain_car n := mut_own_shr_of_types (mut_Fn F base (3 + n));
  |}.
  Next Obligation.
    intros rts F Hctr base n i Hle.
    eapply mut_own_shr_of_types_dist.
    change (HTypeOwnShrCauchy (S n) (mut_Fn F base (2 + S i)) (mut_Fn F base (2 + S n))).
    eapply (@mut_ty_own_shr_cauchy rts F Hctr base). exact (le_n_S _ _ Hle).
  Qed.

  Definition mut_ty_own_shr_fixpoint {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) : mut_ty_own_shrO rts :=
    compl (mut_ty_own_shr_chain F base).

  Lemma mut_ty_own_shr_chain_tail_eq {rt rts}
      (tys : nat → mut_types (rt :: rts))
      (own_chain : chain (mut_ty_own_shrO (rt :: rts))) :
    (∀ n, own_chain n = mut_own_shr_of_types (tys n)) →
    ∀ n, hlist_chain_tail own_chain n = mut_own_shr_of_types (hlist_tail (tys n)).
  Proof.
    intros Hchain n. change (hlist_tail (own_chain n) = mut_own_shr_of_types (hlist_tail (tys n))).
    rewrite Hchain. generalize (tys n). intros tysn.
    refine (hlist_cons_inv (λ tysn,
      hlist_tail (mut_own_shr_of_types tysn) = mut_own_shr_of_types (hlist_tail tysn)) _ tysn).
    intros ty tys'. done.
  Qed.

  Local Program Fixpoint mut_type_fixpoint_from_chain {rts : list RT}
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, HTypeLftsEquiv (tys n) tys0)
      (Hwf : ∀ n, HTypeWfEEquiv (tys n) tys1)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n)) {struct rts} :
      mut_types rts :=
    match rts as rts return
        ∀ (tys0 tys1 : mut_types rts)
          (tys : nat → mut_types rts)
          (own_chain : chain (mut_ty_own_shrO rts)),
        (∀ n, own_chain n = mut_own_shr_of_types (tys n)) →
        (∀ n, HTypeSynTypeEq (tys n) tys0) →
        (∀ n, HTypeSidecondEq (tys n) tys1) →
        (∀ n, HTypeLftsEquiv (tys n) tys0) →
        (∀ n, HTypeWfEEquiv (tys n) tys1) →
        (∀ n, HTypeHasOpTypeEq tys0 (tys n)) → mut_types rts with
    | [] => λ _ _ _ _ _ _ _ _ _ _, +[]
    | rt :: rts => λ tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop,
      let ty0 := hlist_head tys0 in
      let ty1 := hlist_head tys1 in
      let own_shr := compl (hlist_chain_head own_chain) in
      {| ty_xt_inhabited := ty0.(ty_xt_inhabited);
         ty_metadata_kind := ty0.(ty_metadata_kind);
         ty_trivial_drop := ty0.(ty_trivial_drop);
         ty_syn_type := ty0.(ty_syn_type);
         _ty_has_op_type := ty0.(_ty_has_op_type _);
         ty_own_val := own_shr.1;
         ty_shr := own_shr.2;
         _ty_ghost_drop _ _ := True%I;
         ty_sidecond := ty1.(ty_sidecond);
         _ty_lfts := ty_lfts ty0;
         _ty_wf_E := ty_wf_E ty1 |} +::
      mut_type_fixpoint_from_chain (hlist_tail tys0) (hlist_tail tys1)
        (λ n, hlist_tail (tys n)) (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        (λ n, HTypeLftsEquiv_tail _ _ (Hlfts n))
        (λ n, HTypeWfEEquiv_tail _ _ (Hwf n))
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))
    end tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop.
  Next Obligation.
    intros.
    unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros n. simpl.
      rewrite Hchain.
      simpl.
      pose proof (Hsyn n) as Hsynn.
      dependent destruction Hsynn.
      rewrite -x. simpl. rewrite -(H m). eapply ty_has_layout.
  Qed.
  Next Obligation.
    intros.
    eapply _ty_op_type_stable. exact H.
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      pose proof (Hside n) as Hsiden.
      dependent destruction Hsiden.
      rewrite -x. simpl. rewrite -H. eapply ty_own_val_sidecond.
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      pose proof (Hside n) as Hsiden.
      dependent destruction Hsiden.
      rewrite -x. simpl. rewrite -H. eapply ty_shr_sidecond.
  Qed.
  Next Obligation.
    unfold TCNoResolve.
    intros.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_Persistent.
      intros ? [] [] Heq. eapply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      remember (tys n) as tyn.
      dependent destruction tyn.
      simpl.
      eapply ty_shr_persistent.
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      pose proof (Hsyn n) as Hsynn.
      dependent destruction Hsynn.
      rewrite -x. simpl. rewrite -(H m). eapply ty_shr_aligned.
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. do 9 f_equiv.
      { do 2 f_equiv. apply Heq. }
      apply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      pose proof (Hsyn n) as Hsynn.
      dependent destruction Hsynn.
      pose proof (Hlfts n) as Hlftsn.
      rewrite -x in Hlftsn.
      dependent destruction Hlftsn.
      rewrite -x. simpl.
      iIntros "#RUST Hna Htok %% Hlb Hb".
      iApply fupd_logical_step.
      iPoseProof H1 as "[_ Hincl]".
      iMod (lft_incl_acc with "[] Htok") as "(%q' & Htok & Hcl_tok)"; first done.
      { iApply lft_intersect_mono; first iApply lft_incl_refl. iApply "Hincl". }
      rewrite ty_lfts_unfold.
      iPoseProof (ty_share with "RUST Hna Htok [] [//] Hlb Hb") as "Hlb"; first done.
      { rewrite (H0 m). done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hlb").
      iApply logical_step_intro.
      iModIntro. iIntros "($ & Htok)".
      iApply ("Hcl_tok" with "Htok").
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. do 2 f_equiv; eapply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      remember (tys n) as tyn.
      dependent destruction tyn.
      simpl. eapply ty_shr_mono.
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    iIntros "_". iApply logical_step_intro. done.
  Qed.
  Next Obligation.
    intros. unfold own_shr.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv; first eapply Heq.
      eapply Heq.
    - intros n. simpl.
      rewrite Hchain. simpl.
      pose proof (Hop n) as Hopn.
      dependent destruction Hopn.
      rewrite -x. simpl.
      eapply _ty_memcast_compat.
      rewrite -ty_has_op_type_unfold.
      rewrite -ty_has_op_type_unfold in H.
      eapply H0. exact H.
  Qed.
  Next Obligation.
    intros.
    by eapply _ty_has_op_type_untyped.
  Qed.

  Definition mut_type_fixpoint {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} : mut_types rts :=
    let base := mut_type_base TCTForall0 in
    mut_type_fixpoint_from_chain (mut_Fn F base 0) (mut_Fn F base 1)
      (λ n, mut_Fn F base (3 + n)) (mut_ty_own_shr_chain F base)
      (λ _, eq_refl)
      (λ n, mut_Fn_syn_type_const F base (3 + n) 0)
      (λ n, mut_Fn_sidecond_const F base (3 + n) ltac:(lia))
      (λ n, mut_Fn_lfts_const_0 F base (3 + n))
      (λ n, mut_Fn_wf_E_const_1 F base (3 + n) ltac:(lia))
      (λ n, mut_Fn_has_op_type_const F base 0 (3 + n)).

  Definition mut_type_fixpoint_project {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      {rt : RT} `{!Inhabited (RT_xt rt)} (i : nat)
      (Hlook : rts !! i = Some rt) : type rt :=
    mut_type_project (mut_type_fixpoint F) i Hlook.
  Global Arguments mut_type_fixpoint_project {_} _ {_} _ {_} {_} _ _.

  Local Lemma mut_type_fixpoint_from_chain_own_val_unfold_n {rts : list RT}
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, HTypeLftsEquiv (tys n) tys0)
      (Hwf : ∀ n, HTypeWfEEquiv (tys n) tys1)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i n v π
      (r : lnth default_rt rts i) m :
    (v ◁ᵥ{π, m} r @ mut_component default_rt default
      (mut_type_fixpoint_from_chain tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop) i)%I
    ≡{n}≡
    (v ◁ᵥ{π, m} r @ mut_component default_rt default (tys n) i)%I.
  Proof.
    revert tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i r.
    induction rts as [|rt rts IH]; intros tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i r.
    - simpl. generalize (tys n). intros tyn.
      refine (hlist_nil_inv (λ tyn,
        (v ◁ᵥ{π, m} r @ default)%I ≡{n}≡
        (v ◁ᵥ{π, m} r @ mut_component default_rt default tyn i)%I) _ tyn).
      done.
    - destruct i as [|i].
      + simpl.
        rewrite /mut_component /=.
        etrans; first apply (conv_compl n (chain_map fst (hlist_chain_head own_chain))).
        change ((hlist_head (own_chain n)).1 π r m v ≡{n}≡
          (v ◁ᵥ{π, m} r @ hnth default (tys n) 0)%I).
        rewrite Hchain.
        generalize (tys n). intros tyn.
        refine (hlist_cons_inv (λ tyn,
          (hlist_head (mut_own_shr_of_types tyn)).1 π r m v ≡{n}≡
          (v ◁ᵥ{π, m} r @ hnth default tyn 0)%I) _ tyn).
        intros ty tys'. done.
      + simpl.
        rewrite /mut_component /=.
        etrans.
        { eapply IH. }
        remember (tys n) as tyn eqn:Htyn.
        change ((v ◁ᵥ{π, m} r @ hnth default (hlist_tail (tys n)) i)%I ≡{n}≡
          (v ◁ᵥ{π, m} r @ hnth default tyn (S i))%I).
        rewrite -Htyn.
        change ((v ◁ᵥ{π, m} r @ hnth default (hlist_tail tyn) i)%I ≡{n}≡
          (v ◁ᵥ{π, m} r @ hnth default tyn (S i))%I).
        refine (hlist_cons_inv (λ tyn,
          (v ◁ᵥ{π, m} r @ hnth default (hlist_tail tyn) i)%I ≡{n}≡
          (v ◁ᵥ{π, m} r @ hnth default tyn (S i))%I) _ tyn).
        intros ty tys'. done.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_shr_unfold_n {rts : list RT}
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, HTypeLftsEquiv (tys n) tys0)
      (Hwf : ∀ n, HTypeWfEEquiv (tys n) tys1)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i n l κ π
      (r : lnth default_rt rts i) m :
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default
      (mut_type_fixpoint_from_chain tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop) i)%I
    ≡{n}≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (tys n) i)%I.
  Proof.
    revert tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i r.
    induction rts as [|rt rts IH]; intros tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i r.
    - simpl. generalize (tys n). intros tyn.
      refine (hlist_nil_inv (λ tyn,
        (l ◁ₗ{π,m,κ} r@default)%I ≡{n}≡
        (l ◁ₗ{π,m,κ} r@mut_component default_rt default tyn i)%I) _ tyn).
      done.
    - destruct i as [|i].
      + simpl.
        rewrite /mut_component /=.
        etrans; first apply (conv_compl n (chain_map snd (hlist_chain_head own_chain))).
        change ((hlist_head (own_chain n)).2 κ π r m l ≡{n}≡
          (l ◁ₗ{π, m, κ} r @ hnth default (tys n) 0)%I).
        rewrite Hchain.
        generalize (tys n). intros tyn.
        refine (hlist_cons_inv (λ tyn,
          (hlist_head (mut_own_shr_of_types tyn)).2 κ π r m l ≡{n}≡
          (l ◁ₗ{π, m, κ} r @ hnth default tyn 0)%I) _ tyn).
        intros ty tys'. done.
      + simpl.
        rewrite /mut_component /=.
        etrans.
        { eapply IH. }
        remember (tys n) as tyn eqn:Htyn.
        change ((l ◁ₗ{π, m, κ} r @ hnth default (hlist_tail (tys n)) i)%I ≡{n}≡
          (l ◁ₗ{π, m, κ} r @ hnth default tyn (S i))%I).
        rewrite -Htyn.
        change ((l ◁ₗ{π, m, κ} r @ hnth default (hlist_tail tyn) i)%I ≡{n}≡
          (l ◁ₗ{π, m, κ} r @ hnth default tyn (S i))%I).
        refine (hlist_cons_inv (λ tyn,
          (l ◁ₗ{π, m, κ} r @ hnth default (hlist_tail tyn) i)%I ≡{n}≡
          (l ◁ₗ{π, m, κ} r @ hnth default tyn (S i))%I) _ tyn).
        intros ty tys'. done.
  Qed.

  Lemma mut_type_fixpoint_own_val_unfold_n {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i n v π
      (r : lnth default_rt rts i) m :
    (v ◁ᵥ{π, m} r @ mut_component default_rt default (mut_type_fixpoint F) i)%I
    ≡{n}≡
    (v ◁ᵥ{π, m} r @ mut_component default_rt default (mut_Fn_canon F TCTForall0 (3 + n)) i)%I.
  Proof.
    set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint.
    exact (mut_type_fixpoint_from_chain_own_val_unfold_n
      (mut_Fn F base 0) (mut_Fn F base 1)
      (λ n0, mut_Fn F base (3 + n0)) (mut_ty_own_shr_chain F base)
      (λ _, eq_refl)
      (λ n0, mut_Fn_syn_type_const F base (3 + n0) 0)
      (λ n0, mut_Fn_sidecond_const F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_lfts_const_0 F base (3 + n0))
      (λ n0, mut_Fn_wf_E_const_1 F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_has_op_type_const F base 0 (3 + n0))
      default_rt default i n v π r m).
  Qed.

  Lemma mut_type_fixpoint_shr_unfold_n {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i n l κ π
      (r : lnth default_rt rts i) m :
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_type_fixpoint F) i)%I
    ≡{n}≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_Fn_canon F TCTForall0 (3 + n)) i)%I.
  Proof.
    set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint.
    exact (mut_type_fixpoint_from_chain_shr_unfold_n
      (mut_Fn F base 0) (mut_Fn F base 1)
      (λ n0, mut_Fn F base (3 + n0)) (mut_ty_own_shr_chain F base)
      (λ _, eq_refl)
      (λ n0, mut_Fn_syn_type_const F base (3 + n0) 0)
      (λ n0, mut_Fn_sidecond_const F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_lfts_const_0 F base (3 + n0))
      (λ n0, mut_Fn_wf_E_const_1 F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_has_op_type_const F base 0 (3 + n0))
      default_rt default i n l κ π r m).
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_syn_type {rts : list RT}
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, HTypeLftsEquiv (tys n) tys0)
      (Hwf : ∀ n, HTypeWfEEquiv (tys n) tys1)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i m :
    ty_syn_type (mut_component default_rt default
      (mut_type_fixpoint_from_chain tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop) i) m =
    ty_syn_type (mut_component default_rt default tys0 i) m.
  Proof.
    revert tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i.
    induction rts as [|rt rts IH]; intros tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i.
    - dependent destruction tys0. done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i]; first done.
      simpl. rewrite /mut_component /=.
      eapply (IH tys0 tys1 (λ n, hlist_tail (tys n))
        (hlist_chain_tail own_chain)).
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_sidecond {rts : list RT}
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, HTypeLftsEquiv (tys n) tys0)
      (Hwf : ∀ n, HTypeWfEEquiv (tys n) tys1)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i :
    ty_sidecond (mut_component default_rt default
      (mut_type_fixpoint_from_chain tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop) i) ≡
    ty_sidecond (mut_component default_rt default tys1 i).
  Proof.
    revert tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i.
    induction rts as [|rt rts IH]; intros tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop i.
    - dependent destruction tys1. done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i]; first done.
      simpl. rewrite /mut_component /=.
      eapply (IH tys0 tys1 (λ n, hlist_tail (tys n))
        (hlist_chain_tail own_chain)).
  Qed.

  Lemma mut_type_fixpoint_syn_type {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i m :
    ty_syn_type (mut_component default_rt default (mut_type_fixpoint F) i) m =
    ty_syn_type (mut_component default_rt default (mut_Fn_canon F TCTForall0 0) i) m.
  Proof.
    set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint.
    eapply mut_type_fixpoint_from_chain_syn_type.
  Qed.

  Lemma mut_type_fixpoint_sidecond {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i :
    ty_sidecond (mut_component default_rt default (mut_type_fixpoint F) i) ≡
    ty_sidecond (mut_component default_rt default (mut_Fn_canon F TCTForall0 1) i).
  Proof.
    set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint.
    eapply mut_type_fixpoint_from_chain_sidecond.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_HTypeSynTypeEq {rts : list RT}
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, HTypeLftsEquiv (tys n) tys0)
      (Hwf : ∀ n, HTypeWfEEquiv (tys n) tys1)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n)) :
    HTypeSynTypeEq
      (mut_type_fixpoint_from_chain tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop)
      tys0.
  Proof.
    revert tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop.
    induction rts as [|rt rts IH]; intros tys0 tys1 tys own_chain Hchain Hsyn Hside Hlfts Hwf Hop.
    - dependent destruction tys0. constructor.
    - dependent destruction tys0. dependent destruction tys1. constructor.
      + done.
      + eapply IH.
  Qed.

  Local Lemma mut_type_fixpoint_HTypeSynTypeEq {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} :
    HTypeSynTypeEq (mut_type_fixpoint F) (mut_Fn_canon F TCTForall0 0).
  Proof.
    set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint.
    eapply mut_type_fixpoint_from_chain_HTypeSynTypeEq.
  Qed.

  Local Lemma HTypeSynTypeEq_component {rts : list RT} (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i m :
    HTypeSynTypeEq tys tys' →
    ty_syn_type (mut_component default_rt default tys i) m =
    ty_syn_type (mut_component default_rt default tys' i) m.
  Proof.
    revert tys tys' i.
    induction rts as [|rt rts IH]; intros tys tys' i Hsyn.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hsyn. destruct i as [|i]; simpl; first apply H.
      eapply IH. done.
  Qed.

  Local Lemma HTypeSidecondEq_component {rts : list RT} (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i :
    HTypeSidecondEq tys tys' →
    ty_sidecond (mut_component default_rt default tys i) ≡
    ty_sidecond (mut_component default_rt default tys' i).
  Proof.
    revert tys tys' i.
    induction rts as [|rt rts IH]; intros tys tys' i Hside.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hside. destruct i as [|i]; simpl; first done.
      eapply IH. done.
  Qed.

  Local Lemma HTypeDist_component_own_val {rts : list RT} n (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i v π
      (r : lnth default_rt rts i) m :
    HTypeDist n tys tys' →
    (v ◁ᵥ{π, m} r @ mut_component default_rt default tys i)%I ≡{n}≡
    (v ◁ᵥ{π, m} r @ mut_component default_rt default tys' i)%I.
  Proof.
    revert tys tys' i r.
    induction rts as [|rt rts IH]; intros tys tys' i r Hdist.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hdist. destruct i as [|i]; simpl; first apply type_dist_own_val.
      eapply IH. done.
  Qed.

  Local Lemma HTypeDist_component_shr {rts : list RT} n (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i l κ π
      (r : lnth default_rt rts i) m :
    HTypeDist n tys tys' →
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys i)%I ≡{n}≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys' i)%I.
  Proof.
    revert tys tys' i r.
    induction rts as [|rt rts IH]; intros tys tys' i r Hdist.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hdist. destruct i as [|i]; simpl; first apply type_dist_shr.
      eapply IH. done.
  Qed.

  Local Lemma HTypeOwnShrCauchy_component_own_val {rts : list RT} n
      (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i v π
      (r : lnth default_rt rts i) m :
    HTypeOwnShrCauchy n tys tys' →
    dist_later n
      (v ◁ᵥ{π, m} r @ mut_component default_rt default tys i)%I
      (v ◁ᵥ{π, m} r @ mut_component default_rt default tys' i)%I.
  Proof.
    revert tys tys' i r.
    induction rts as [|rt rts IH]; intros tys tys' i r Hdist.
    - dependent destruction tys. dependent destruction tys'. dist_later_intro. done.
    - dependent destruction Hdist. destruct i as [|i]; simpl; first apply H.
      eapply IH. done.
  Qed.

  Local Lemma HTypeOwnShrCauchy_component_shr {rts : list RT} n
      (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i l κ π
      (r : lnth default_rt rts i) m :
    HTypeOwnShrCauchy n tys tys' →
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys i)%I ≡{n}≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys' i)%I.
  Proof.
    revert tys tys' i r.
    induction rts as [|rt rts IH]; intros tys tys' i r Hdist.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hdist. destruct i as [|i]; simpl; first apply H.
      eapply IH. done.
  Qed.

  Local Lemma HTypeDist2_of_components {rts : list RT} n (tys tys' : mut_types rts) :
    (∀ default_rt (default : type default_rt) i,
      TypeDist2 n (mut_component default_rt default tys i)
        (mut_component default_rt default tys' i)) →
    HTypeDist2 n tys tys'.
  Proof.
    revert tys tys'. induction rts as [|rt rts IH]; intros tys tys' Hcomp.
    - dependent destruction tys. dependent destruction tys'. constructor.
    - dependent destruction tys. dependent destruction tys'. constructor.
      + exact (Hcomp rt t 0).
      + eapply IH. intros default_rt default i.
        exact (Hcomp default_rt default (S i)).
  Qed.

  Local Lemma mut_Fn_fixpoint_component_dist2 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} n
      (default_rt : RT) (default : type default_rt) i :
    TypeDist2 n
      (mut_component default_rt default (mut_Fn_canon F TCTForall0 (2 + n)) i)
      (mut_component default_rt default (mut_type_fixpoint F) i).
  Proof.
    set (base := mut_type_base TCTForall0).
    constructor.
    - intros m. etrans.
      { eapply HTypeSynTypeEq_component.
        eapply (@mut_Fn_syn_type_const rts F MutTypeContractive0 base (2 + n) 0). }
      symmetry. eapply mut_type_fixpoint_syn_type.
    - etrans.
      { eapply HTypeSidecondEq_component.
        eapply (@mut_Fn_sidecond_const rts F MutTypeContractive0 base (2 + n)); lia. }
      symmetry. eapply mut_type_fixpoint_sidecond.
    - intros π r m v. dist_later_intro.
      rewrite mut_type_fixpoint_own_val_unfold_n.
      eapply dist_later_lt.
      { eapply HTypeOwnShrCauchy_component_own_val.
        eapply (@mut_ty_own_shr_cauchy rts F MutTypeContractive0 base n (S m0)); unfold_sidx; lia. }
      unfold_sidx. lia.
    - intros κ π r m l.
      rewrite mut_type_fixpoint_shr_unfold_n.
      symmetry.
      eapply HTypeOwnShrCauchy_component_shr.
      eapply (@mut_ty_own_shr_cauchy rts F MutTypeContractive0 base (S n) n); lia.
  Qed.

  Local Lemma mut_Fn_fixpoint_dist2 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} n :
    HTypeDist2 n (mut_Fn_canon F TCTForall0 (2 + n)) (mut_type_fixpoint F).
  Proof.
    eapply HTypeDist2_of_components.
    intros default_rt default i.
    eapply mut_Fn_fixpoint_component_dist2.
  Qed.

  Lemma mut_type_fixpoint_own_val_unfold {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i v π
      (r : lnth default_rt rts i) m :
    (v ◁ᵥ{π, m} r @ mut_component default_rt default (mut_type_fixpoint F) i)%I ≡
    (v ◁ᵥ{π, m} r @ mut_component default_rt default (F (mut_type_fixpoint F)) i)%I.
  Proof.
    apply equiv_dist => n.
    rewrite mut_type_fixpoint_own_val_unfold_n.
    rewrite /mut_Fn_canon mut_Fn_succ.
    eapply HTypeDist_component_own_val.
    eapply (@mut_type_ctr_dist rts F MutTypeContractive0).
    eapply mut_Fn_fixpoint_dist2.
  Qed.

  Lemma mut_type_fixpoint_shr_unfold {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i l κ π
      (r : lnth default_rt rts i) m :
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_type_fixpoint F) i)%I ≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (F (mut_type_fixpoint F)) i)%I.
  Proof.
    apply equiv_dist => n.
    rewrite mut_type_fixpoint_shr_unfold_n.
    rewrite /mut_Fn_canon mut_Fn_succ.
    eapply HTypeDist_component_shr.
    eapply (@mut_type_ctr_dist rts F MutTypeContractive0).
    eapply mut_Fn_fixpoint_dist2.
  Qed.

  Lemma mut_type_fixpoint_incl_1 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i
      (r : lnth default_rt rts i) :
    ⊢ type_incl r r
      (mut_component default_rt default (mut_type_fixpoint F) i)
      (mut_component default_rt default (F (mut_type_fixpoint F)) i).
  Proof.
    iSplit; last iSplit.
    - iModIntro. iIntros "Hsc".
      rewrite (mut_type_fixpoint_sidecond F default_rt default i).
      rewrite (HTypeSidecondEq_component (F (mut_type_fixpoint F)) (mut_Fn_canon F TCTForall0 1)
        default_rt default i).
      { iExact "Hsc". }
      eapply (@mut_type_ctr_sidecond rts F MutTypeContractive0).
      eapply mut_type_fixpoint_HTypeSynTypeEq.
    - iModIntro. iIntros (π m v). rewrite mut_type_fixpoint_own_val_unfold. eauto.
    - iModIntro. iIntros (κ π m l). rewrite mut_type_fixpoint_shr_unfold. eauto.
  Qed.

  Lemma mut_type_fixpoint_incl_2 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i
      (r : lnth default_rt rts i) :
    ⊢ type_incl r r
      (mut_component default_rt default (F (mut_type_fixpoint F)) i)
      (mut_component default_rt default (mut_type_fixpoint F) i).
  Proof.
    iSplit; last iSplit.
    - iModIntro.
      rewrite (mut_type_fixpoint_sidecond F default_rt default i).
      rewrite (HTypeSidecondEq_component (F (mut_type_fixpoint F)) (mut_Fn_canon F TCTForall0 1)
        default_rt default i).
      { iIntros "$". }
      eapply (@mut_type_ctr_sidecond rts F MutTypeContractive0).
      eapply mut_type_fixpoint_HTypeSynTypeEq.
    - iModIntro. iIntros (π m v). rewrite mut_type_fixpoint_own_val_unfold. eauto.
    - iModIntro. iIntros (κ π m l). rewrite mut_type_fixpoint_shr_unfold. eauto.
  Qed.

  Lemma mut_type_fixpoint_subtype_1 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) E L i
      (r : lnth default_rt rts i) :
    subtype E L r r
      (mut_component default_rt default (mut_type_fixpoint F) i)
      (mut_component default_rt default (F (mut_type_fixpoint F)) i).
  Proof.
    iIntros (?) "HL HE".
    iSplitR; last iApply mut_type_fixpoint_incl_1.
    iPureIntro. intros m.
    rewrite (mut_type_fixpoint_syn_type F default_rt default i m).
    symmetry. eapply HTypeSynTypeEq_component.
    change (HTypeSynTypeEq (F (mut_type_fixpoint F)) (F (mut_type_base TCTForall0))).
    eapply mut_type_ctr_syn_type.
  Qed.

  Lemma mut_type_fixpoint_subtype_2 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) E L i
      (r : lnth default_rt rts i) :
    subtype E L r r
      (mut_component default_rt default (F (mut_type_fixpoint F)) i)
      (mut_component default_rt default (mut_type_fixpoint F) i).
  Proof.
    iIntros (?) "HL HE".
    iSplitR; last iApply mut_type_fixpoint_incl_2.
    iPureIntro. intros m.
    rewrite (mut_type_fixpoint_syn_type F default_rt default i m).
    eapply HTypeSynTypeEq_component.
    change (HTypeSynTypeEq (F (mut_type_fixpoint F)) (F (mut_type_base TCTForall0))).
    eapply mut_type_ctr_syn_type.
  Qed.

  Lemma mut_type_fixpoint_unfold_eqtype {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) E L i
      (r : lnth default_rt rts i) :
    eqtype E L r r
      (mut_component default_rt default (mut_type_fixpoint F) i)
      (mut_component default_rt default (F (mut_type_fixpoint F)) i).
  Proof.
    split.
    - apply mut_type_fixpoint_subtype_1.
    - apply mut_type_fixpoint_subtype_2.
  Qed.

  (** The actual guarded fixpoint should have the following shape once the
      componentwise Cauchy proof from [fixpoint.v] has been lifted to [hlist].

      The intended implementation mirrors [type_fixpoint]:

      - define [Fn] by iterating the SCC functor from a base hlist;
      - prove componentwise constancy of syntactic metadata and sideconditions;
      - build a Cauchy chain in [mut_ty_own_shrO rts] from [Fn (3 + n)];
      - assemble each component type from the completed ownership/sharing pair
        and the finite approximants for the remaining fields;
      - expose projection-specific unfolding and subtype lemmas.
  *)
  Definition mut_type_fixpoint_ty : Type :=
    ∀ rts : list RT,
      TCTForall (λ rt, Inhabited (RT_xt rt)) rts → mut_type_fun rts → mut_types rts.

End mutual_fixpoint_defs.

Arguments mut_component {_ _} _ _ _ _.

Section rules.
  Context `{!typeGS Σ}.
  Context {rts : list RT}.
  Context (F : mut_type_fun rts) `{!MutTypeContractive F}.
  Context `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}.
  Context {rt : RT} `{!Inhabited (RT_xt rt)}.
  Context (i : nat) (Hlook : rts !! i = Some rt).

  Local Definition mut_fixpoint_project : type rt :=
    mut_type_project (mut_type_fixpoint F) i Hlook.

  Local Definition mut_fixpoint_project_unfolded : type rt :=
    mut_type_project (F (mut_type_fixpoint F)) i Hlook.

  Local Lemma subtype_rew_r {rt1 rt2 : RT} (Heq : rt1 = rt2) E L
      (r : rt2) (ty1 ty2 : type rt1) :
    subtype E L (rew <-[RT_rt] Heq in r) (rew <-[RT_rt] Heq in r) ty1 ty2 →
    subtype E L r r (rew [type] Heq in ty1) (rew [type] Heq in ty2).
  Proof. destruct Heq. done. Qed.

  Lemma mut_type_project_fixpoint_subtype_1 E L r :
    subtype E L r r mut_fixpoint_project mut_fixpoint_project_unfolded.
  Proof.
    rewrite /mut_fixpoint_project /mut_fixpoint_project_unfolded.
    rewrite !mut_type_project_unfold /mut_type_project_def.
    simpl.
    eapply subtype_rew_r.
    apply mut_type_fixpoint_subtype_1.
  Qed.

  Lemma mut_type_project_fixpoint_subtype_2 E L r :
    subtype E L r r mut_fixpoint_project_unfolded mut_fixpoint_project.
  Proof.
    rewrite /mut_fixpoint_project /mut_fixpoint_project_unfolded.
    rewrite !mut_type_project_unfold /mut_type_project_def.
    simpl.
    eapply subtype_rew_r.
    apply mut_type_fixpoint_subtype_2.
  Qed.

  Lemma mut_type_project_fixpoint_unfold_eqtype E L r :
    eqtype E L r r mut_fixpoint_project mut_fixpoint_project_unfolded.
  Proof.
    split.
    - apply mut_type_project_fixpoint_subtype_1.
    - apply mut_type_project_fixpoint_subtype_2.
  Qed.

  (* on place access, unfold *)
  Lemma typed_place_mut_fixpoint_unfold π E L l r k1 bmin P (T : place_cont_t rt bmin) :
    typed_place π E L l (◁ mut_fixpoint_project) r bmin k1 P T :-
    return (typed_place π E L l (◁ mut_fixpoint_project_unfolded) r bmin k1 P T).
  Proof.
    iApply typed_place_eqltype.
    apply full_eqtype_eqltype.
    intros ?.
    apply mut_type_project_fixpoint_unfold_eqtype.
  Qed.
  Definition typed_place_mut_fixpoint_unfold_inst := [instance typed_place_mut_fixpoint_unfold].
  Global Existing Instance typed_place_mut_fixpoint_unfold_inst.

  Lemma owned_subtype_mut_fixpoint_id π E L b r1 r2 T :
    owned_subtype π E L b r1 r2 mut_fixpoint_project mut_fixpoint_project T :-
    exhale (⌜r1 = r2⌝);
    return T L.
  Proof.
    iIntros "Ha". by iApply owned_subtype_id.
  Qed.
  Definition owned_subtype_mut_fixpoint_id_inst := [instance @owned_subtype_mut_fixpoint_id].
  Global Existing Instance owned_subtype_mut_fixpoint_id_inst | 5.

  Lemma owned_subtype_mut_fixpoint_r {rt1} (ty1 : type rt1) π E L b r1 r2 T :
    owned_subtype π E L b r1 r2 ty1 mut_fixpoint_project T :-
    return (owned_subtype π E L b r1 r2 ty1 mut_fixpoint_project_unfolded T).
  Proof.
    iIntros "HT".
    iApply owned_subtype_subtype_r; last iApply "HT".
    apply mut_type_project_fixpoint_subtype_2.
  Qed.
  Definition owned_subtype_mut_fixpoint_r_inst := [instance @owned_subtype_mut_fixpoint_r].
  Global Existing Instance owned_subtype_mut_fixpoint_r_inst | 6.

  Lemma weak_subtype_mut_fixpoint_id E L r1 r2 T :
    weak_subtype E L r1 r2 mut_fixpoint_project mut_fixpoint_project T :-
    exhale (⌜r1 = r2⌝); return T.
  Proof.
    iIntros "(-> & HT)". by iApply weak_subtype_id.
  Qed.
  Definition weak_subtype_mut_fixpoint_id_inst := [instance @weak_subtype_mut_fixpoint_id].
  Global Existing Instance weak_subtype_mut_fixpoint_id_inst | 5.

  Lemma weak_subtype_mut_fixpoint_r {rt1} (ty1 : type rt1) E L r1 r2 T :
    weak_subtype E L r1 r2 ty1 mut_fixpoint_project T :-
    return (weak_subtype E L r1 r2 ty1 mut_fixpoint_project_unfolded T).
  Proof.
    iIntros "HT".
    iApply weak_subtype_subtype_r; last done.
    apply mut_type_project_fixpoint_subtype_2.
  Qed.
  Definition weak_subtype_mut_fixpoint_r_inst := [instance @weak_subtype_mut_fixpoint_r].
  Global Existing Instance weak_subtype_mut_fixpoint_r_inst | 6.

  Lemma mut_subtype_mut_fixpoint_id E L T :
    mut_subtype E L mut_fixpoint_project mut_fixpoint_project T :-
    return T.
  Proof.
    unfold mut_subtype.
    iIntros "$". iPureIntro.
    reflexivity.
  Qed.
  Definition mut_subtype_mut_fixpoint_id_inst := [instance @mut_subtype_mut_fixpoint_id].
  Global Existing Instance mut_subtype_mut_fixpoint_id_inst | 5.

  Lemma mut_subtype_mut_fixpoint_r (ty1 : type rt) E L T :
    mut_subtype E L ty1 mut_fixpoint_project T :-
    return (mut_subtype E L ty1 mut_fixpoint_project_unfolded T).
  Proof.
    unfold mut_subtype.
    iIntros "(%Ha & $)". iPureIntro.
    intros r.
    eapply subtype_trans; first apply Ha.
    apply mut_type_project_fixpoint_subtype_2.
  Qed.
  Definition mut_subtype_mut_fixpoint_r_inst := [instance @mut_subtype_mut_fixpoint_r].
  Global Existing Instance mut_subtype_mut_fixpoint_r_inst | 6.

  Lemma mut_eqtype_mut_fixpoint_id E L T :
    mut_eqtype E L mut_fixpoint_project mut_fixpoint_project T :-
    return T.
  Proof.
    unfold mut_eqtype.
    iIntros "$". iPureIntro.
    reflexivity.
  Qed.
  Definition mut_eqtype_mut_fixpoint_id_inst := [instance @mut_eqtype_mut_fixpoint_id].
  Global Existing Instance mut_eqtype_mut_fixpoint_id_inst | 5.

  Lemma mut_eqtype_mut_fixpoint_r (ty1 : type rt) E L T :
    mut_eqtype E L ty1 mut_fixpoint_project T :-
    return (mut_eqtype E L ty1 mut_fixpoint_project_unfolded T).
  Proof.
    unfold mut_eqtype.
    iIntros "(%Ha & $)". iPureIntro.
    etrans; first apply Ha.
    split.
    - apply mut_type_project_fixpoint_subtype_2.
    - apply mut_type_project_fixpoint_subtype_1.
  Qed.
  Definition mut_eqtype_mut_fixpoint_r_inst := [instance @mut_eqtype_mut_fixpoint_r].
  Global Existing Instance mut_eqtype_mut_fixpoint_r_inst | 6.
End rules.

Section mut_type_contractiveness_instances.
  Context `{!typeGS Σ}.

  (** Ergonomic contractiveness layer for mutual recursive type functors.

      [MutTypeContractive] is intentionally stated over the whole SCC, because
      the guarded fixpoint construction needs lifecycle stabilization facts for
      [F (F tys)] versus [F tys].  The classes below decompose those obligations
      by output component while keeping the whole SCC functor [F] available for
      the lifecycle fields.
   *)
  Class MutComponentContractive {rts rt}
      (F : mut_type_fun rts) (G : mut_types rts → type rt) : Type := {
    mut_comp_ctr_syn_type : ∀ tys tys' m,
      ty_syn_type (G tys) m = ty_syn_type (G tys') m;
    mut_comp_ctr_sidecond : ∀ tys tys',
      HTypeSynTypeEq tys tys' → ty_sidecond (G tys) ≡ ty_sidecond (G tys');
    mut_comp_ctr_lfts_idempotent : ∀ tys,
      ⊢ lft_equiv (lft_intersect_list (ty_lfts (G (F tys))))
          (lft_intersect_list (ty_lfts (G tys)));
    mut_comp_ctr_wf_E_idempotent : ∀ tys,
      elctx_interp (ty_wf_E (G (F tys))) ≡ elctx_interp (ty_wf_E (G tys));
    mut_comp_ctr_has_op_type : ∀ tys tys' ot,
      ty_has_op_type (G tys) ot ↔ ty_has_op_type (G tys') ot;
    mut_comp_ctr_dist : ∀ n tys tys',
      HTypeDist2 n tys tys' → TypeDist n (G tys) (G tys');
    mut_comp_ctr_dist2 : ∀ n tys tys',
      HTypeDistLater2 n tys tys' → TypeDist2 n (G tys) (G tys');
  }.

  Class MutComponentLifecycleStable {rts rt}
      (F : mut_type_fun rts) (G : mut_types rts → type rt) : Type := {
    mut_comp_lifecycle_lfts : ∀ tys,
      ⊢ lft_equiv (lft_intersect_list (ty_lfts (G (F tys))))
          (lft_intersect_list (ty_lfts (G tys)));
    mut_comp_lifecycle_wf_E : ∀ tys,
      elctx_interp (ty_wf_E (G (F tys))) ≡ elctx_interp (ty_wf_E (G tys));
  }.

  Class MutHTypeContractive {rts rts'}
      (F : mut_type_fun rts) (G : mut_types rts → mut_types rts') : Type := {
    mut_htype_ctr_syn_type : ∀ tys tys', HTypeSynTypeEq (G tys) (G tys');
    mut_htype_ctr_sidecond : ∀ tys tys',
      HTypeSynTypeEq tys tys' → HTypeSidecondEq (G tys) (G tys');
    mut_htype_ctr_lfts_idempotent : ∀ tys,
      HTypeLftsEquiv (G (F tys)) (G tys);
    mut_htype_ctr_wf_E_idempotent : ∀ tys,
      HTypeWfEEquiv (G (F tys)) (G tys);
    mut_htype_ctr_has_op_type : ∀ tys tys', HTypeHasOpTypeEq (G tys) (G tys');
    mut_htype_ctr_dist : ∀ n tys tys',
      HTypeDist2 n tys tys' → HTypeDist n (G tys) (G tys');
    mut_htype_ctr_dist2 : ∀ n tys tys',
      HTypeDistLater2 n tys tys' → HTypeDist2 n (G tys) (G tys');
  }.

  Global Instance mut_htype_contractive_nil {rts} (F : mut_type_fun rts) :
    MutHTypeContractive F (λ _ : mut_types rts, +[]).
  Proof. constructor; intros; constructor. Qed.

  Global Instance mut_htype_contractive_cons {rts rt rts'}
      (F : mut_type_fun rts)
      (G : mut_types rts → type rt)
      (Gs : mut_types rts → mut_types rts') :
    MutComponentContractive F G →
    MutHTypeContractive F Gs →
    MutHTypeContractive F (λ tys, G tys +:: Gs tys).
  Proof.
    intros HG HGs. constructor; intros; constructor.
    - apply mut_comp_ctr_syn_type.
    - apply mut_htype_ctr_syn_type.
    - eapply mut_comp_ctr_sidecond; done.
    - eapply mut_htype_ctr_sidecond; done.
    - apply mut_comp_ctr_lfts_idempotent.
    - apply mut_htype_ctr_lfts_idempotent.
    - apply mut_comp_ctr_wf_E_idempotent.
    - apply mut_htype_ctr_wf_E_idempotent.
    - apply mut_comp_ctr_has_op_type.
    - apply mut_htype_ctr_has_op_type.
    - eapply mut_comp_ctr_dist; done.
    - eapply mut_htype_ctr_dist; done.
    - eapply mut_comp_ctr_dist2; done.
    - eapply mut_htype_ctr_dist2; done.
  Qed.

  Global Instance mut_type_contractive_of_htype {rts} (F : mut_type_fun rts) :
    MutHTypeContractive F F → MutTypeContractive F.
  Proof.
    intros HF. constructor.
    - apply mut_htype_ctr_syn_type.
    - apply mut_htype_ctr_sidecond.
    - apply mut_htype_ctr_lfts_idempotent.
    - apply mut_htype_ctr_wf_E_idempotent.
    - apply mut_htype_ctr_has_op_type.
    - apply mut_htype_ctr_dist.
    - apply mut_htype_ctr_dist2.
  Qed.

  Local Lemma TypeDist_trans {rt} n (ty1 ty2 ty3 : type rt) :
    TypeDist n ty1 ty2 → TypeDist n ty2 ty3 → TypeDist n ty1 ty3.
  Proof.
    intros H12 H23. constructor.
    - intros m. etrans; [apply H12 | apply H23].
    - etrans; [apply H12 | apply H23].
    - intros. etrans; [apply H12 | apply H23].
    - intros. etrans; [apply H12 | apply H23].
  Qed.

  Local Lemma TypeDist2_trans {rt} n (ty1 ty2 ty3 : type rt) :
    TypeDist2 n ty1 ty2 → TypeDist2 n ty2 ty3 → TypeDist2 n ty1 ty3.
  Proof.
    intros H12 H23. constructor.
    - intros m. etrans; [apply H12 | apply H23].
    - etrans; [apply H12 | apply H23].
    - intros. etrans; [apply H12 | apply H23].
    - intros. etrans; [apply H12 | apply H23].
  Qed.

  (** Pointwise input decomposition.  The [cons] constructor stores the unary
      [TypeContractive] evidence for the head coordinate and recurses on the
      tail, so the bridge to [MutComponentContractive] can destruct it. *)
  Inductive MutComponentPointwiseContractive :
      ∀ {rts rt}, (mut_types rts → type rt) → Type :=
  | mut_component_pointwise_contractive_nil {rt}
      (G : mut_types [] → type rt) :
      MutComponentPointwiseContractive G
  | mut_component_pointwise_contractive_cons {rt rts rt'}
      (G : mut_types (rt :: rts) → type rt') :
      (∀ tys, TypeContractive (λ ty : type rt, G (ty +:: tys))) →
      (∀ ty, MutComponentPointwiseContractive (λ tys : mut_types rts, G (ty +:: tys))) →
      MutComponentPointwiseContractive G.
  Existing Class MutComponentPointwiseContractive.
  Global Existing Instance mut_component_pointwise_contractive_nil.
  Global Existing Instance mut_component_pointwise_contractive_cons.

  Local Lemma mut_component_pointwise_syn_type {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    ∀ tys tys' m, ty_syn_type (G tys) m = ty_syn_type (G tys') m.
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros tys tys' m. dependent destruction tys. dependent destruction tys'. done.
    - intros tys tys' m. dependent destruction tys. dependent destruction tys'.
      etrans; last eapply IHtail.
      eapply (type_ctr_syn_type (F := λ ty : type rt, G (ty +:: tys))).
  Qed.

  Local Lemma mut_component_pointwise_sidecond {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    ∀ tys tys', HTypeSynTypeEq tys tys' → ty_sidecond (G tys) ≡ ty_sidecond (G tys').
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros tys tys' Hsyn. dependent destruction tys. dependent destruction tys'. done.
    - intros tys tys' Hsyn. dependent destruction tys. dependent destruction tys'.
      dependent destruction Hsyn.
      etrans.
      { eapply (type_ctr_sidecond (F := λ ty : type rt, G (ty +:: tys))); done. }
      eapply IHtail. done.
  Qed.

  Local Lemma mut_component_pointwise_has_op_type {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    ∀ tys tys' ot, ty_has_op_type (G tys) ot ↔ ty_has_op_type (G tys') ot.
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros tys tys' ot. dependent destruction tys. dependent destruction tys'. done.
    - intros tys tys' ot. dependent destruction tys. dependent destruction tys'.
      etrans.
      { eapply (type_ctr_has_op_type (F := λ ty : type rt, G (ty +:: tys))). }
      eapply IHtail.
  Qed.

  Local Lemma mut_component_pointwise_dist {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    ∀ n tys tys', HTypeDist2 n tys tys' → TypeDist n (G tys) (G tys').
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros n tys tys' Hdist. dependent destruction tys. dependent destruction tys'. constructor; done.
    - intros n tys tys' Hdist. dependent destruction Hdist.
      eapply (TypeDist_trans n _ (G (y +:: xl)) _).
      { change (TypeDist n ((λ ty : type rt, G (ty +:: xl)) x)
          ((λ ty : type rt, G (ty +:: xl)) y)).
        eapply type_contractive_dist; [apply Hhead | done]. }
      eapply IHtail. done.
  Qed.

  Local Lemma mut_component_pointwise_dist2 {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    ∀ n tys tys', HTypeDistLater2 n tys tys' → TypeDist2 n (G tys) (G tys').
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros n tys tys' Hdist. dependent destruction tys. dependent destruction tys'. constructor; done.
    - intros n tys tys' Hdist. dependent destruction Hdist.
      eapply (TypeDist2_trans n _ (G (y +:: xl)) _).
      { change (TypeDist2 n ((λ ty : type rt, G (ty +:: xl)) x)
          ((λ ty : type rt, G (ty +:: xl)) y)).
        eapply type_contractive_dist2; [apply Hhead | done]. }
      eapply IHtail. done.
  Qed.

  Global Instance mut_type_project_cons_head_ne {rt rts} `{!Inhabited (RT_xt rt)}
      (tys : mut_types rts) :
    TypeNonExpansive (λ ty : type rt, mut_type_project (ty +:: tys) 0 eq_refl).
  Proof.
    rewrite (@mut_type_project_unfold).
    unfold mut_type_project_def, mut_component. simpl.
    set (Hrew := lookup_lnth (rt :: rts) rt 0 rt eq_refl).
    change (TypeNonExpansive (λ ty : type rt, rew [type] Hrew in ty)).
    destruct Hrew. apply _.
  Qed.

  Global Instance mut_type_project_cons_tail_ne {rt rt' rts} `{!Inhabited (RT_xt rt')}
      (tys : mut_types rts) i (Hlook : (rt :: rts) !! S i = Some rt') :
    TypeNonExpansive (λ ty : type rt, mut_type_project (ty +:: tys) (S i) Hlook).
  Proof.
    rewrite (@mut_type_project_unfold).
    unfold mut_type_project_def, mut_component. simpl.
    apply _.
  Qed.

  Global Instance mut_type_project_fixed_cons_head_ne {rt0 rt rt' rts}
      `{!Inhabited (RT_xt rt')} (ty0 : type rt0)
      (G : type rt → mut_types rts) (Hlook : (rt0 :: rts) !! 0 = Some rt') :
    TypeNonExpansive (λ ty : type rt, mut_type_project (ty0 +:: G ty) 0 Hlook).
  Proof.
    rewrite (@mut_type_project_unfold).
    unfold mut_type_project_def, mut_component. simpl.
    apply _.
  Qed.

  Global Instance mut_type_project_fixed_cons_tail_ne {rt0 rt rt' rts}
      `{!Inhabited (RT_xt rt')} (ty0 : type rt0)
      (G : type rt → mut_types rts) i (Hlook : (rt0 :: rts) !! S i = Some rt') :
    TypeNonExpansive (λ ty : type rt, mut_type_project (G ty) i Hlook) →
    TypeNonExpansive (λ ty : type rt, mut_type_project (ty0 +:: G ty) (S i) Hlook).
  Proof.
    intros Hne.
    rewrite (@mut_type_project_unfold) in Hne.
    unfold mut_type_project_def, mut_component in Hne. simpl in Hne.
    rewrite (@mut_type_project_unfold).
    unfold mut_type_project_def, mut_component. simpl.
    replace (lookup_lnth (rt0 :: rts) rt' (S i) rt' Hlook) with
      (lookup_lnth rts rt' i rt' Hlook) by apply proof_irrelevance.
    exact Hne.
  Qed.

  Lemma mut_component_contractive_of_pointwise {rts rt}
      (F : mut_type_fun rts) (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    MutComponentLifecycleStable F G →
    MutComponentContractive F G.
  Proof.
    intros Hpw Hlife.
    constructor.
    - eapply mut_component_pointwise_syn_type; done.
    - eapply mut_component_pointwise_sidecond; done.
    - apply mut_comp_lifecycle_lfts.
    - apply mut_comp_lifecycle_wf_E.
    - eapply mut_component_pointwise_has_op_type; done.
    - eapply mut_component_pointwise_dist; done.
    - eapply mut_component_pointwise_dist2; done.
  Qed.

  Global Instance mut_component_contractive_pointwise {rts rt}
      (F : mut_type_fun rts) (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    MutComponentLifecycleStable F G →
    MutComponentContractive F G :=
    mut_component_contractive_of_pointwise F G.

End mut_type_contractiveness_instances.

Ltac solve_mut_type_contractive :=
  repeat first [
    progress cbn
  | intro
  | eapply mut_type_contractive_of_htype
  | eapply mut_htype_contractive_cons
  | eapply mut_htype_contractive_nil
  | eapply mut_component_contractive_pointwise
  | eapply mut_component_pointwise_contractive_cons
  | eapply mut_component_pointwise_contractive_nil
  | apply _
  ].
