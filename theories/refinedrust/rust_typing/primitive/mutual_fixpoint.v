From refinedrust Require Import type programs lftmor.
From refinedrust Require Import options.

Import EqNotations.

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

  Definition mut_typeO (rts : list RT) : ofe :=
    hlistO (λ rt : RT, typeO (rt:=rt)) rts.

  Definition mut_ty_own_shrO (rts : list RT) : ofe :=
    hlistO (λ rt : RT,
      prodO (thread_id -d> rt -d> metadataO -d> val -d> iPropO Σ)
            (lft -d> thread_id -d> rt -d> metadataO -d> loc -d> iPropO Σ)) rts.

  Definition mut_type_fun (rts : list RT) : Type :=
    mut_types rts → mut_types rts.

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

  Lemma HTypeDist_sym {rts : list RT} n (tys1 tys2 : mut_types rts) :
    HTypeDist n tys1 tys2 → HTypeDist n tys2 tys1.
  Proof.
    eapply HForallTwo_symmetric. intros rt ty1 ty2. apply TypeDist_sym.
  Qed.

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


  Definition MutLftsEquiv {rts : list RT} (tys tys' : mut_types rts) : Prop :=
    ⊢ lft_equiv (lft_intersect_list (mut_lfts tys))
        (lft_intersect_list (mut_lfts tys')).

  Definition MutWfEEquiv {rts : list RT} (tys tys' : mut_types rts) : Prop :=
    elctx_interp (mut_wf_E tys) ≡ elctx_interp (mut_wf_E tys').


  Lemma HTypeLftsEquiv_mut_lfts {rts : list RT} (tys tys' : mut_types rts) :
    HTypeLftsEquiv tys tys' →
    MutLftsEquiv tys tys'.
  Proof.
    intros H. induction H as [|rt rts ty ty' tys tys' Hty _ IH]; simpl.
    - iApply lft_equiv_refl.
    - unfold MutLftsEquiv in *. rewrite /mut_lfts /= !lft_intersect_list_app.
      iApply lft_equiv_intersect; done.
  Qed.

  Lemma HTypeWfEEquiv_mut_wf_E {rts : list RT} (tys tys' : mut_types rts) :
    HTypeWfEEquiv tys tys' →
    MutWfEEquiv tys tys'.
  Proof.
    intros H. induction H as [|rt rts ty ty' tys tys' Hty _ IH]; simpl.
    - reflexivity.
    - unfold MutWfEEquiv in *. rewrite /mut_wf_E /= !elctx_interp_app Hty IH. done.
  Qed.

  Fixpoint HMutLftsIncl {rts : list RT}
      (approx_lfts : nat → list lft) (tys : nat → mut_types rts) : Prop :=
    match rts as rts return (nat → list lft) → (nat → mut_types rts) → Prop with
    | [] => λ _ _, True
    | _ :: _ => λ approx_lfts tys,
        (∀ n, ⊢ lft_incl (lft_intersect_list (approx_lfts n))
            (lft_intersect_list (ty_lfts (hlist_head (tys n))))) ∧
        HMutLftsIncl approx_lfts (λ n, hlist_tail (tys n))
    end approx_lfts tys.

  Lemma HMutLftsIncl_mono {rts : list RT}
      (approx_lfts approx_lfts' : nat → list lft) (tys : nat → mut_types rts) :
    (∀ n, ⊢ lft_incl (lft_intersect_list (approx_lfts n))
        (lft_intersect_list (approx_lfts' n))) →
    HMutLftsIncl approx_lfts' tys →
    HMutLftsIncl approx_lfts tys.
  Proof.
    induction rts as [|rt rts IH] in tys |-*; simpl; first done.
    intros Hincl [Hhead Htail]. split.
    - intros n. iApply lft_incl_trans; first iApply Hincl. iApply Hhead.
    - eapply IH; done.
  Qed.

  Lemma mut_lfts_incl_components {rts : list RT} (tys : nat → mut_types rts) :
    HMutLftsIncl (λ n, mut_lfts (tys n)) tys.
  Proof.
    induction rts as [|rt rts IH] in tys |-*; simpl; first done.
    split.
    - intros n. remember (tys n) as tyn. dependent destruction tyn.
      rewrite /mut_lfts /= lft_intersect_list_app.
      iApply lft_intersect_incl_l.
    - eapply (HMutLftsIncl_mono _ (λ n, mut_lfts (hlist_tail (tys n)))).
      + intros n. remember (tys n) as tyn. dependent destruction tyn.
        rewrite /mut_lfts /= lft_intersect_list_app.
        iApply lft_intersect_incl_r.
      + apply (IH (λ n, hlist_tail (tys n))).
  Qed.

  Lemma LftMorphism_mut_lfts_idempotent {rts : list RT}
      (F : mut_type_fun rts) `{!LftMorphism F} tys :
    MutLftsEquiv (F (F tys)) (F tys).
  Proof.
    change (⊢ lft_equiv
      (lft_intersect_list (lifecycle_lfts (F (F tys))))
      (lft_intersect_list (lifecycle_lfts (F tys)))).
    iApply (LftMorphism_lfts_idempotent F).
  Qed.

  Lemma LftMorphism_mut_wf_E_idempotent {rts : list RT}
      (F : mut_type_fun rts) `{!LftMorphism F} tys :
    MutWfEEquiv (F (F (F tys))) (F (F tys)).
  Proof.
    change (elctx_interp (lifecycle_wf_E (F (F (F tys)))) ≡
      elctx_interp (lifecycle_wf_E (F (F tys)))).
    apply (LftMorphism_wf_E_idempotent F).
  Qed.

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
    mut_type_ctr_lft_mor : LftMorphism F;
    mut_type_ctr_syn_type : ∀ tys tys',
      HTypeSynTypeEq (F tys) (F tys');
    mut_type_ctr_sidecond : ∀ tys tys',
      HTypeSynTypeEq tys tys' → HTypeSidecondEq (F tys) (F tys');
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
End mutual_fixpoint_defs.

Section fixpoint.
  Context `{!typeGS Σ}.

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
    eapply (@mut_type_ctr_sidecond _ _ rts F MutTypeContractive0).
    apply (@mut_Fn_syn_type_const rts F MutTypeContractive0 base).
  Qed.

  Lemma mut_Fn_lfts_const_0 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n :
    MutLftsEquiv (mut_Fn F base n) (mut_Fn F base 0).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    destruct n as [|[|n]].
    - unfold MutLftsEquiv. iApply lft_equiv_refl.
    - rewrite mut_Fn_succ mut_Fn_0.
      iApply (LftMorphism_mut_lfts_idempotent F (LftMorphism0:=mut_type_ctr_lft_mor)).
    - rewrite !mut_Fn_succ.
      iApply lft_equiv_trans.
      { iApply (LftMorphism_mut_lfts_idempotent F (LftMorphism0:=mut_type_ctr_lft_mor)). }
      specialize (IH (S n) ltac:(lia)). unfold MutLftsEquiv in IH. iApply IH.
  Qed.

  Lemma mut_Fn_wf_E_const_1 {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F} (base : mut_types rts) n :
    n ≥ 1 → MutWfEEquiv (mut_Fn F base n) (mut_Fn F base 1).
  Proof.
    intros Hn.
    induction n as [n IH] using lt_wf_ind.
    destruct n as [|[|n]].
    - lia.
    - unfold MutWfEEquiv. reflexivity.
    - unfold mut_Fn, mut_type_approximant.
      etrans.
      { exact (LftMorphism_mut_wf_E_idempotent F (LftMorphism0:=mut_type_ctr_lft_mor)
          (Nat.iter n F base)). }
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
    - eapply (@mut_type_ctr_dist2 _ _ rts F MutTypeContractive0).
      change (HTypeDistLater2 0 (mut_Fn F base (1 + i)) (mut_Fn F base 1)).
      eapply (@mut_Fn_dist_later2_0 rts F MutTypeContractive0 base); lia.
    - destruct i; first lia.
      eapply (@mut_type_ctr_dist2 _ _ rts F MutTypeContractive0).
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
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n)) {struct rts} :
      mut_types rts :=
    match rts as rts return
        ∀ (agg_lfts : list lft) (agg_wf_E : elctx)
          (tys0 tys1 : mut_types rts)
          (tys : nat → mut_types rts)
          (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
          (own_chain : chain (mut_ty_own_shrO rts)),
        (∀ n, own_chain n = mut_own_shr_of_types (tys n)) →
        (∀ n, HTypeSynTypeEq (tys n) tys0) →
        (∀ n, HTypeSidecondEq (tys n) tys1) →
        (∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
            (lft_intersect_list agg_lfts)) →
        HMutLftsIncl approx_lfts tys →
        (∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E) →
        (∀ n, HTypeHasOpTypeEq tys0 (tys n)) → mut_types rts with
    | [] => λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, +[]
    | rt :: rts => λ agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop,
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
          _ty_lfts := agg_lfts;
          _ty_wf_E := agg_wf_E |} +::
      mut_type_fixpoint_from_chain agg_lfts agg_wf_E (hlist_tail tys0) (hlist_tail tys1)
        (λ n, hlist_tail (tys n)) approx_lfts approx_wf_E (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        Hlfts
        (proj2 Hlfts_incl)
        Hwf
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))
    end agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop.
  Next Obligation.
    intros. econstructor.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. f_equiv. eapply Heq.
      + intros n. simpl.
        rewrite Hchain.
        simpl.
        pose proof (Hsyn n) as Hsynn.
        dependent destruction Hsynn.
        rewrite -x. simpl. rewrite -(H m). eapply ty_has_layout.
    - intros ot Hot. eapply ty_op_type_stable. rewrite ty_has_op_type_unfold. exact Hot.
    - intros ot Hot. eapply ty_op_type_wf. rewrite ty_has_op_type_unfold. exact Hot.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. f_equiv. eapply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        pose proof (Hside n) as Hsiden.
        dependent destruction Hsiden.
        rewrite -x. simpl. rewrite -H. eapply ty_own_val_sidecond.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. f_equiv. eapply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        pose proof (Hside n) as Hsiden.
        dependent destruction Hsiden.
        rewrite -x. simpl. rewrite -H. eapply ty_shr_sidecond.
    - unfold TCNoResolve.
      intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_Persistent.
        intros ? [] [] Heq. eapply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        remember (tys n) as tyn.
        dependent destruction tyn.
        simpl.
        eapply ty_shr_persistent.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. f_equiv. eapply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        pose proof (Hsyn n) as Hsynn.
        dependent destruction Hsynn.
        rewrite -x. simpl. rewrite -(H m). eapply ty_shr_aligned.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. do 9 f_equiv.
        { do 2 f_equiv. apply Heq. }
        apply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        pose proof (Hsyn n) as Hsynn.
        dependent destruction Hsynn.
        pose proof (Hlfts n) as Hlftsn.
        pose proof (proj1 Hlfts_incl n) as Hlfts_incln.
        rewrite -x in Hlfts_incln.
        rewrite -x. simpl.
        iIntros "#RUST Hna Htok %% Hlb Hb".
        iApply fupd_logical_step.
        iPoseProof Hlftsn as "[_ Hagg_incl]".
        iMod (lft_incl_acc with "[] Htok") as "(%q' & Htok & Hcl_tok)"; first done.
        { iApply lft_intersect_mono; first iApply lft_incl_refl.
          iApply lft_incl_trans; first iApply "Hagg_incl". iApply Hlfts_incln. }
        iPoseProof (ty_share with "RUST Hna Htok [] [//] Hlb Hb") as "Hlb"; first done.
        { rewrite (H0 m). done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hlb").
        iApply logical_step_intro.
        iModIntro. iIntros "($ & Htok)".
        iApply ("Hcl_tok" with "Htok").
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. do 2 f_equiv; eapply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        remember (tys n) as tyn.
        dependent destruction tyn.
        simpl. eapply ty_shr_mono.
    - intros. unfold own_shr.
      iIntros "_". iApply logical_step_intro. done.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. f_equiv; first eapply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        pose proof (Hop n) as Hopn.
        dependent destruction Hopn.
        rewrite -x. simpl.
        eapply ty_decodable.
        rewrite -ty_has_op_type_unfold in H.
        eapply H0. exact H.
    - intros. unfold own_shr.
      eapply @limit_preserving_compl.
      + eapply bi.limit_preserving_entails; first apply _.
        intros ? [] [] Heq. f_equiv; first eapply Heq.
        apply Heq.
      + intros n. simpl.
        rewrite Hchain. simpl.
        pose proof (Hop n) as Hopn.
        dependent destruction Hopn.
        rewrite -x. simpl.
        eapply ty_decode_compat; last done.
        rewrite -ty_has_op_type_unfold in H.
        eapply H1. exact H.
    - intros.
      rewrite -ty_has_op_type_unfold. by eapply ty_has_op_type_untyped.
    - apply _.
    - apply _.
  Qed.

  Local Definition mut_type_fixpoint {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} : mut_types rts :=
    let base := mut_type_base TCTForall0 in
    mut_type_fixpoint_from_chain (mut_lfts (mut_Fn F base 0)) (mut_wf_E (mut_Fn F base 1))
      (mut_Fn F base 0) (mut_Fn F base 1)
      (λ n, mut_Fn F base (3 + n))
      (λ n, mut_lfts (mut_Fn F base (3 + n)))
      (λ n, mut_wf_E (mut_Fn F base (3 + n)))
      (mut_ty_own_shr_chain F base)
      (λ _, eq_refl)
      (λ n, mut_Fn_syn_type_const F base (3 + n) 0)
      (λ n, mut_Fn_sidecond_const F base (3 + n) ltac:(lia))
      (λ n, mut_Fn_lfts_const_0 F base (3 + n))
      (mut_lfts_incl_components (λ n, mut_Fn F base (3 + n)))
      (λ n, mut_Fn_wf_E_const_1 F base (3 + n) ltac:(lia))
      (λ n, mut_Fn_has_op_type_const F base 0 (3 + n)).

  Local Definition mut_type_fixpoint_project {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      {rt : RT} `{!Inhabited (RT_xt rt)} (i : nat)
      (Hlook : rts !! i = Some rt) : type rt :=
    mut_type_project (mut_type_fixpoint F) i Hlook.
  Global Arguments mut_type_fixpoint_project {_} _ {_} _ {_} {_} _ _.

  Local Lemma mut_type_fixpoint_from_chain_own_val_unfold_n {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i n v π
      (r : lnth default_rt rts i) m :
    (v ◁ᵥ{π, m} r @ mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i)%I
    ≡{n}≡
    (v ◁ᵥ{π, m} r @ mut_component default_rt default (tys n) i)%I.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i r.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i r.
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
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i n l κ π
      (r : lnth default_rt rts i) m :
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i)%I
    ≡{n}≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (tys n) i)%I.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i r.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i r.
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
      (mut_lfts (mut_Fn F base 0)) (mut_wf_E (mut_Fn F base 1))
      (mut_Fn F base 0) (mut_Fn F base 1)
      (λ n0, mut_Fn F base (3 + n0))
      (λ n0, mut_lfts (mut_Fn F base (3 + n0)))
      (λ n0, mut_wf_E (mut_Fn F base (3 + n0)))
      (mut_ty_own_shr_chain F base)
      (λ _, eq_refl)
      (λ n0, mut_Fn_syn_type_const F base (3 + n0) 0)
      (λ n0, mut_Fn_sidecond_const F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_lfts_const_0 F base (3 + n0))
      (mut_lfts_incl_components (λ n0, mut_Fn F base (3 + n0)))
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
      (mut_lfts (mut_Fn F base 0)) (mut_wf_E (mut_Fn F base 1))
      (mut_Fn F base 0) (mut_Fn F base 1)
      (λ n0, mut_Fn F base (3 + n0))
      (λ n0, mut_lfts (mut_Fn F base (3 + n0)))
      (λ n0, mut_wf_E (mut_Fn F base (3 + n0)))
      (mut_ty_own_shr_chain F base)
      (λ _, eq_refl)
      (λ n0, mut_Fn_syn_type_const F base (3 + n0) 0)
      (λ n0, mut_Fn_sidecond_const F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_lfts_const_0 F base (3 + n0))
      (mut_lfts_incl_components (λ n0, mut_Fn F base (3 + n0)))
      (λ n0, mut_Fn_wf_E_const_1 F base (3 + n0) ltac:(lia))
      (λ n0, mut_Fn_has_op_type_const F base 0 (3 + n0))
      default_rt default i n l κ π r m).
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_lfts {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i :
    is_Some (rts !! i) →
    ty_lfts (mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i) =
    agg_lfts.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i Hlook.
    - destruct Hlook as (? & Hlook). done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i].
      + simpl. rewrite /mut_component /= ty_lfts_unfold. reflexivity.
      + simpl. rewrite /mut_component /=.
      eapply (IH agg_lfts agg_wf_E tys0 tys1 (λ n, hlist_tail (tys n))
        approx_lfts approx_wf_E (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        Hlfts (proj2 Hlfts_incl) Hwf
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))).
      exact Hlook.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_wf_E {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i :
    is_Some (rts !! i) →
    ty_wf_E (mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i) =
    agg_wf_E.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i Hlook.
    - destruct Hlook as (? & Hlook). done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i].
      + simpl. rewrite /mut_component /= ty_wf_E_unfold. reflexivity.
      + simpl. rewrite /mut_component /=.
      eapply (IH agg_lfts agg_wf_E tys0 tys1 (λ n, hlist_tail (tys n))
        approx_lfts approx_wf_E (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        Hlfts (proj2 Hlfts_incl) Hwf
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))).
      exact Hlook.
  Qed.

  Lemma mut_type_fixpoint_lfts {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i :
    is_Some (rts !! i) →
    ty_lfts (mut_component default_rt default (mut_type_fixpoint F) i) =
    mut_lfts (mut_Fn_canon F TCTForall0 0).
  Proof.
    intros Hlook. set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint /mut_Fn_canon.
    eapply mut_type_fixpoint_from_chain_lfts. exact Hlook.
  Qed.

  Lemma mut_type_fixpoint_wf_E {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i :
    is_Some (rts !! i) →
    ty_wf_E (mut_component default_rt default (mut_type_fixpoint F) i) =
    mut_wf_E (mut_Fn_canon F TCTForall0 1).
  Proof.
    intros Hlook. set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint /mut_Fn_canon.
    eapply mut_type_fixpoint_from_chain_wf_E. exact Hlook.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_ghost_drop {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i π
      (r : lnth default_rt rts i) :
    is_Some (rts !! i) →
    _ty_ghost_drop (mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i) π r ≡ True%I.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i r.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i r Hlook.
    - destruct Hlook as [? Hlook]. destruct i; discriminate.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i]; first done.
      simpl. rewrite /mut_component /=.
      eapply (IH agg_lfts agg_wf_E tys0 tys1 (λ n, hlist_tail (tys n))
        approx_lfts approx_wf_E (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        Hlfts (proj2 Hlfts_incl) Hwf
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))).
      exact Hlook.
  Qed.

  Lemma mut_type_fixpoint_ghost_drop {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i π
      (r : lnth default_rt rts i) :
    is_Some (rts !! i) →
    _ty_ghost_drop (mut_component default_rt default (mut_type_fixpoint F) i) π r ≡ True%I.
  Proof.
    intros Hlook. set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint /mut_Fn_canon.
    eapply mut_type_fixpoint_from_chain_ghost_drop. exact Hlook.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_syn_type {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i m :
    ty_syn_type (mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i) m =
    ty_syn_type (mut_component default_rt default tys0 i) m.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    - dependent destruction tys0. done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i]; first done.
      simpl. rewrite /mut_component /=.
      eapply (IH agg_lfts agg_wf_E tys0 tys1 (λ n, hlist_tail (tys n))
        approx_lfts approx_wf_E (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        Hlfts (proj2 Hlfts_incl) Hwf
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))).
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_sidecond {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i :
    ty_sidecond (mut_component default_rt default
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i) ≡
    ty_sidecond (mut_component default_rt default tys1 i).
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    - dependent destruction tys1. done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i as [|i]; first done.
      simpl. rewrite /mut_component /=.
      eapply (IH agg_lfts agg_wf_E tys0 tys1 (λ n, hlist_tail (tys n))
        approx_lfts approx_wf_E (hlist_chain_tail own_chain)
        (mut_ty_own_shr_chain_tail_eq tys own_chain Hchain)
        (λ n, HTypeSynTypeEq_tail _ _ (Hsyn n))
        (λ n, HTypeSidecondEq_tail _ _ (Hside n))
        Hlfts (proj2 Hlfts_incl) Hwf
        (λ n, HTypeHasOpTypeEq_tail _ _ (Hop n))).
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

  Local Lemma HTypeHasOpTypeEq_component {rts : list RT} (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i ot :
    HTypeHasOpTypeEq tys tys' →
    ty_has_op_type (mut_component default_rt default tys i) ot ↔
    ty_has_op_type (mut_component default_rt default tys' i) ot.
  Proof.
    revert tys tys' i.
    induction rts as [|rt rts IH]; intros tys tys' i Hop.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hop. destruct i as [|i]; simpl; first apply H.
      eapply IH. done.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_HTypeHasOpTypeEq {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n)) :
    HTypeHasOpTypeEq
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop)
      tys0.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop.
    - dependent destruction tys0. constructor.
    - dependent destruction tys0. dependent destruction tys1. constructor.
      + intros ot. rewrite ty_has_op_type_unfold. done.
      + eapply IH.
  Qed.

  Lemma mut_type_fixpoint_has_op_type {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i ot :
    ty_has_op_type (mut_component default_rt default (mut_type_fixpoint F) i) ot ↔
    ty_has_op_type (mut_component default_rt default (mut_Fn_canon F TCTForall0 0) i) ot.
  Proof.
    set (base := mut_type_base TCTForall0).
    rewrite /mut_type_fixpoint.
    eapply HTypeHasOpTypeEq_component.
    eapply mut_type_fixpoint_from_chain_HTypeHasOpTypeEq.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_metadata_kind {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n))
      (default_rt : RT) (default : type default_rt) i :
    ty_metadata_kind
      (mut_component default_rt default
        (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys
          approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop) i) =
    ty_metadata_kind (mut_component default_rt default tys0 i).
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain
      Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop i.
    induction rts as [|rt rts IH]; intros.
    - dependent destruction tys0. done.
    - dependent destruction tys0. dependent destruction tys1.
      destruct i; first done. eapply IH.
  Qed.

  Lemma mut_type_fixpoint_metadata_kind {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i :
    ty_metadata_kind (mut_component default_rt default (mut_type_fixpoint F) i) =
    ty_metadata_kind
      (mut_component default_rt default (mut_Fn_canon F TCTForall0 0) i).
  Proof.
    rewrite /mut_type_fixpoint.
    eapply mut_type_fixpoint_from_chain_metadata_kind.
  Qed.

  Local Lemma mut_type_fixpoint_from_chain_HTypeSynTypeEq {rts : list RT}
      (agg_lfts : list lft) (agg_wf_E : elctx)
      (tys0 tys1 : mut_types rts)
      (tys : nat → mut_types rts)
      (approx_lfts : nat → list lft) (approx_wf_E : nat → elctx)
      (own_chain : chain (mut_ty_own_shrO rts))
      (Hchain : ∀ n, own_chain n = mut_own_shr_of_types (tys n))
      (Hsyn : ∀ n, HTypeSynTypeEq (tys n) tys0)
      (Hside : ∀ n, HTypeSidecondEq (tys n) tys1)
      (Hlfts : ∀ n, ⊢ lft_equiv (lft_intersect_list (approx_lfts n))
          (lft_intersect_list agg_lfts))
      (Hlfts_incl : HMutLftsIncl approx_lfts tys)
      (Hwf : ∀ n, elctx_interp (approx_wf_E n) ≡ elctx_interp agg_wf_E)
      (Hop : ∀ n, HTypeHasOpTypeEq tys0 (tys n)) :
    HTypeSynTypeEq
      (mut_type_fixpoint_from_chain agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop)
      tys0.
  Proof.
    revert agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop.
    induction rts as [|rt rts IH]; intros agg_lfts agg_wf_E tys0 tys1 tys approx_lfts approx_wf_E own_chain Hchain Hsyn Hside Hlfts Hlfts_incl Hwf Hop.
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

  Local Lemma HTypeDist2_component_own_val {rts : list RT} n (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i v π
      (r : lnth default_rt rts i) m :
    HTypeDist2 n tys tys' →
    dist_later n
      (v ◁ᵥ{π, m} r @ mut_component default_rt default tys i)%I
      (v ◁ᵥ{π, m} r @ mut_component default_rt default tys' i)%I.
  Proof.
    revert tys tys' i r.
    induction rts as [|rt rts IH]; intros tys tys' i r Hdist.
    - dependent destruction tys. dependent destruction tys'. dist_later_intro. done.
    - dependent destruction Hdist. destruct i as [|i]; simpl; first apply type_dist2_own_val.
      eapply IH. done.
  Qed.

  Local Lemma HTypeDist2_component_shr {rts : list RT} n (tys tys' : mut_types rts)
      (default_rt : RT) (default : type default_rt) i l κ π
      (r : lnth default_rt rts i) m :
    HTypeDist2 n tys tys' →
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys i)%I ≡{n}≡
    (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys' i)%I.
  Proof.
    revert tys tys' i r.
    induction rts as [|rt rts IH]; intros tys tys' i r Hdist.
    - dependent destruction tys. dependent destruction tys'. done.
    - dependent destruction Hdist. destruct i as [|i]; simpl; first apply type_dist2_shr.
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

  Local Lemma HTypeDist_of_components {rts : list RT} n (tys tys' : mut_types rts) :
    (∀ default_rt (default : type default_rt) i,
      TypeDist n (mut_component default_rt default tys i)
        (mut_component default_rt default tys' i)) →
    HTypeDist n tys tys'.
  Proof.
    revert tys tys'. induction rts as [|rt rts IH]; intros tys tys' Hcomp.
    - dependent destruction tys. dependent destruction tys'. constructor.
    - dependent destruction tys. dependent destruction tys'. constructor.
      + exact (Hcomp rt t 0).
      + eapply IH. intros default_rt default i.
        exact (Hcomp default_rt default (S i)).
  Qed.

  Local Lemma HTypeDistLater2_of_components {rts : list RT} n (tys tys' : mut_types rts) :
    (∀ default_rt (default : type default_rt) i,
      TypeDistLater2 n (mut_component default_rt default tys i)
        (mut_component default_rt default tys' i)) →
    HTypeDistLater2 n tys tys'.
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
    eapply (@mut_type_ctr_dist _ _ rts F MutTypeContractive0).
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
    eapply (@mut_type_ctr_dist _ _ rts F MutTypeContractive0).
    eapply mut_Fn_fixpoint_dist2.
  Qed.

  Lemma mut_type_fixpoint_raw_unfold_dist {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} :
    ∀ n, HTypeDist n (mut_type_fixpoint F) (F (mut_type_fixpoint F)).
  Proof.
    intros n. eapply HTypeDist_of_components.
    intros default_rt default i. constructor.
    - intros m. rewrite (mut_type_fixpoint_syn_type F default_rt default i m).
      symmetry. eapply HTypeSynTypeEq_component.
      change (HTypeSynTypeEq (F (mut_type_fixpoint F)) (F (mut_type_base TCTForall0))).
      eapply mut_type_ctr_syn_type.
    - rewrite (mut_type_fixpoint_sidecond F default_rt default i).
      symmetry. eapply HTypeSidecondEq_component.
      change (HTypeSidecondEq (F (mut_type_fixpoint F)) (F (mut_Fn_canon F TCTForall0 0))).
      eapply mut_type_ctr_sidecond.
      eapply mut_type_fixpoint_HTypeSynTypeEq.
    - intros π r m v. rewrite mut_type_fixpoint_own_val_unfold. done.
    - intros κ π r m l. rewrite mut_type_fixpoint_shr_unfold. done.
  Qed.

  Lemma mut_type_fixpoint_unique_dist {rts : list RT} (F : mut_type_fun rts)
      `{!MutTypeContractive F}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (tys : mut_types rts) :
    (∀ n, HTypeDist n tys (F tys)) →
    ∀ n, HTypeDist n tys (mut_type_fixpoint F).
  Proof.
    intros Hfix.
    assert (Hst : HTypeSynTypeEq tys (mut_type_fixpoint F)).
    { eapply HForallTwo_transitive.
      { intros rt ty1 ty2 ty3 H12 H23 m. etrans; [apply H12 | apply H23]. }
      - eapply HForallTwo_impl; last exact (Hfix 0).
        intros rt ty ty' Hdist m. destruct Hdist as [Hst0 _ _ _]. apply Hst0.
      - eapply HForallTwo_symmetric.
        { intros rt ty ty' Hsyn m. symmetry. apply Hsyn. }
        eapply HForallTwo_transitive.
        { intros rt ty1 ty2 ty3 H12 H23 m. etrans; [apply H12 | apply H23]. }
        + eapply mut_type_fixpoint_HTypeSynTypeEq.
        + change (HTypeSynTypeEq (F (mut_type_base TCTForall0)) (F tys)).
          eapply mut_type_ctr_syn_type. }
    assert (Hsc : HTypeSidecondEq tys (mut_type_fixpoint F)).
    { eapply HForallTwo_transitive.
      { intros rt ty1 ty2 ty3 H12 H23. etrans; [apply H12 | apply H23]. }
      - eapply HForallTwo_impl; last exact (Hfix 0).
        intros rt ty ty' Hdist. destruct Hdist as [_ Hsc0 _ _]. apply Hsc0.
      - eapply HForallTwo_symmetric.
        { intros rt ty ty' Hside. symmetry. apply Hside. }
        eapply HForallTwo_transitive.
        { intros rt ty1 ty2 ty3 H12 H23. etrans; [apply H12 | apply H23]. }
        + eapply HForallTwo_impl; last exact (mut_type_fixpoint_raw_unfold_dist F 0).
          intros rt ty ty' Hdist. destruct Hdist as [_ Hsc0 _ _]. apply Hsc0.
        + eapply mut_type_ctr_sidecond.
          eapply HForallTwo_symmetric; last exact Hst.
          intros rt ty ty' Hsyn m. symmetry. apply Hsyn. }
    induction n as [|n IH].
    - assert (Hlater : HTypeDistLater2 0 tys (mut_type_fixpoint F)).
      { eapply HTypeDistLater2_of_components. intros default_rt default i. constructor.
        - intros m. eapply HTypeSynTypeEq_component. exact Hst.
        - eapply HTypeSidecondEq_component. exact Hsc.
        - intros. dist_later_2_intro. lia.
        - intros. dist_later_intro. unfold_sidx. lia. }
      assert (Hshr : ∀ default_rt (default : type default_rt) i l κ π
          (r : lnth default_rt rts i) m,
          (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys i)%I ≡{0}≡
          (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_type_fixpoint F) i)%I).
      { intros default_rt default i l κ π r m.
        etrans; first eapply HTypeDist_component_shr; first exact (Hfix 0).
        etrans.
        { eapply HTypeDist2_component_shr.
          eapply (@mut_type_ctr_dist2 _ _ rts F MutTypeContractive0). exact Hlater. }
        symmetry. eapply HTypeDist_component_shr.
        eapply mut_type_fixpoint_raw_unfold_dist. }
      assert (Hdist2 : HTypeDist2 0 tys (mut_type_fixpoint F)).
      { eapply HTypeDist2_of_components. intros default_rt default i. constructor.
        - intros m. eapply HTypeSynTypeEq_component. exact Hst.
        - eapply HTypeSidecondEq_component. exact Hsc.
        - intros. dist_later_intro. unfold_sidx. lia.
        - intros. eapply Hshr. }
      eapply HTypeDist_of_components. intros default_rt default i. constructor.
      + intros m. eapply HTypeSynTypeEq_component. exact Hst.
      + eapply HTypeSidecondEq_component. exact Hsc.
      + intros π r m v.
        etrans; first eapply HTypeDist_component_own_val; first exact (Hfix 0).
        etrans.
        { eapply HTypeDist_component_own_val.
          eapply (@mut_type_ctr_dist _ _ rts F MutTypeContractive0). exact Hdist2. }
        symmetry. eapply HTypeDist_component_own_val.
        eapply mut_type_fixpoint_raw_unfold_dist.
      + intros κ π r m l. eapply Hshr.
    - assert (Hlater : HTypeDistLater2 (S n) tys (mut_type_fixpoint F)).
      { eapply HTypeDistLater2_of_components. intros default_rt default i. constructor.
        - intros m. eapply HTypeSynTypeEq_component. exact Hst.
        - eapply HTypeSidecondEq_component. exact Hsc.
        - intros π r m v. dist_later_2_intro.
          eapply dist_le.
          { eapply HTypeDist_component_own_val. exact IH. }
          unfold_sidx. lia.
        - intros κ π r m l. dist_later_intro.
          eapply dist_le.
          { eapply HTypeDist_component_shr. exact IH. }
          unfold_sidx. lia. }
      assert (Hshr : ∀ default_rt (default : type default_rt) i l κ π
          (r : lnth default_rt rts i) m,
          (l ◁ₗ{π, m, κ} r @ mut_component default_rt default tys i)%I ≡{S n}≡
          (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_type_fixpoint F) i)%I).
      { intros default_rt default i l κ π r m.
        etrans; first eapply HTypeDist_component_shr; first exact (Hfix (S n)).
        etrans.
        { eapply HTypeDist2_component_shr.
          eapply (@mut_type_ctr_dist2 _ _ rts F MutTypeContractive0). exact Hlater. }
        symmetry. eapply HTypeDist_component_shr.
        eapply mut_type_fixpoint_raw_unfold_dist. }
      assert (Hdist2 : HTypeDist2 (S n) tys (mut_type_fixpoint F)).
      { eapply HTypeDist2_of_components. intros default_rt default i. constructor.
        - intros m. eapply HTypeSynTypeEq_component. exact Hst.
        - eapply HTypeSidecondEq_component. exact Hsc.
        - intros π r m v. dist_later_intro.
          eapply dist_le.
          { eapply HTypeDist_component_own_val. exact IH. }
          unfold_sidx. lia.
        - intros. eapply Hshr. }
      eapply HTypeDist_of_components. intros default_rt default i. constructor.
      + intros m. eapply HTypeSynTypeEq_component. exact Hst.
      + eapply HTypeSidecondEq_component. exact Hsc.
      + intros π r m v.
        etrans; first eapply HTypeDist_component_own_val; first exact (Hfix (S n)).
        etrans.
        { eapply HTypeDist_component_own_val.
          eapply (@mut_type_ctr_dist _ _ rts F MutTypeContractive0). exact Hdist2. }
        symmetry. eapply HTypeDist_component_own_val.
        eapply mut_type_fixpoint_raw_unfold_dist.
       + intros κ π r m l. eapply Hshr.
  Qed.

  Section iterated_functor.
    Context {rts : list RT}.

    Fixpoint mut_iter (F : mut_type_fun rts) (k : nat) : mut_type_fun rts :=
      match k with
      | 0 => λ tys, tys
      | S k => λ tys, F (mut_iter F k tys)
      end.

    Lemma mut_iter_0 (F : mut_type_fun rts) tys :
      mut_iter F 0 tys = tys.
    Proof. done. Qed.

    Lemma mut_iter_S (F : mut_type_fun rts) k tys :
      mut_iter F (S k) tys = F (mut_iter F k tys).
    Proof. done. Qed.

    Lemma mut_iter_commute (F : mut_type_fun rts) k tys :
      mut_iter F k (F tys) = F (mut_iter F k tys).
    Proof.
      induction k as [|k IH]; simpl; first done.
      by rewrite IH.
    Qed.

    Global Instance mut_iter_ne (F : mut_type_fun rts) k :
      MutTypeNonExpansive F → MutTypeNonExpansive (mut_iter F k).
    Proof.
      intros Hne. induction k as [|k IH]; constructor; simpl; intros n tys tys' Hdist.
      - exact Hdist.
      - exact Hdist.
      - eapply (@mut_type_ne _ _ rts F Hne).
        eapply (@mut_type_ne _ _ rts (mut_iter F k) IH). exact Hdist.
      - eapply (@mut_type_ne2 _ _ rts F Hne).
        eapply (@mut_type_ne2 _ _ rts (mut_iter F k) IH). exact Hdist.
    Qed.
  End iterated_functor.

  Definition mut_type_fixpoint_iter {rts : list RT}
      (F : mut_type_fun rts) (k : nat)
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} : mut_types rts :=
    mut_type_fixpoint (mut_iter F k).

  Lemma mut_type_fixpoint_iter_unfold_dist {rts : list RT}
      (F : mut_type_fun rts) (k : nat)
      `{!MutTypeNonExpansive F}
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} :
    ∀ n, HTypeDist n
      (mut_type_fixpoint_iter F k)
      (F (mut_type_fixpoint_iter F k)).
  Proof.
    set (G := mut_iter F k).
    set (μ := mut_type_fixpoint G).
    assert (Hfix_Fμ : ∀ n, HTypeDist n (F μ) (G (F μ))).
    { intros n. subst G μ. rewrite mut_iter_commute.
      eapply (@mut_type_ne _ _ rts F MutTypeNonExpansive0).
      eapply mut_type_fixpoint_raw_unfold_dist. }
    intros n. change (HTypeDist n μ (F μ)).
    eapply HTypeDist_sym.
    eapply (@mut_type_fixpoint_unique_dist rts G MutTypeContractive0 TCTForall0 (F μ)).
    exact Hfix_Fμ.
  Qed.

  Lemma mut_type_fixpoint_incl_1 {rts : list RT} (F : mut_type_fun rts) k
      `{!MutTypeNonExpansive F}
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i
      (r : lnth default_rt rts i) :
    ⊢ type_incl r r
      (mut_component default_rt default (mut_type_fixpoint_iter F k) i)
      (mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i).
  Proof.
    iSplit; last iSplit.
    - iModIntro. iIntros "Hsc".
      rewrite (HTypeSidecondEq_component
        (mut_type_fixpoint_iter F k) (F (mut_type_fixpoint_iter F k))
        default_rt default i).
      { iExact "Hsc". }
      eapply HForallTwo_impl; last exact (mut_type_fixpoint_iter_unfold_dist F k 0).
      intros rt ty ty' Hdist. destruct Hdist as [_ Hsc _ _]. exact Hsc.
    - iModIntro. iIntros (π m v) "Hown".
      assert ((v ◁ᵥ{π, m} r @ mut_component default_rt default (mut_type_fixpoint_iter F k) i)%I ≡
        (v ◁ᵥ{π, m} r @ mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i)%I) as Heq.
      { apply equiv_dist => n. eapply HTypeDist_component_own_val.
        exact (mut_type_fixpoint_iter_unfold_dist F k n). }
      rewrite Heq. done.
    - iModIntro. iIntros (κ π m l) "Hshr".
      assert ((l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_type_fixpoint_iter F k) i)%I ≡
        (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i)%I) as Heq.
      { apply equiv_dist => n. eapply HTypeDist_component_shr.
        exact (mut_type_fixpoint_iter_unfold_dist F k n). }
      rewrite Heq. done.
  Qed.

  Lemma mut_type_fixpoint_incl_2 {rts : list RT} (F : mut_type_fun rts) k
      `{!MutTypeNonExpansive F}
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) i
      (r : lnth default_rt rts i) :
    ⊢ type_incl r r
      (mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i)
      (mut_component default_rt default (mut_type_fixpoint_iter F k) i).
  Proof.
    iSplit; last iSplit.
    - iModIntro.
      rewrite (HTypeSidecondEq_component
        (mut_type_fixpoint_iter F k) (F (mut_type_fixpoint_iter F k))
        default_rt default i).
      { iIntros "$". }
      eapply HForallTwo_impl; last exact (mut_type_fixpoint_iter_unfold_dist F k 0).
      intros rt ty ty' Hdist. destruct Hdist as [_ Hsc _ _]. exact Hsc.
    - iModIntro. iIntros (π m v) "Hown".
      assert ((v ◁ᵥ{π, m} r @ mut_component default_rt default (mut_type_fixpoint_iter F k) i)%I ≡
        (v ◁ᵥ{π, m} r @ mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i)%I) as Heq.
      { apply equiv_dist => n. eapply HTypeDist_component_own_val.
        exact (mut_type_fixpoint_iter_unfold_dist F k n). }
      rewrite -Heq. done.
    - iModIntro. iIntros (κ π m l) "Hshr".
      assert ((l ◁ₗ{π, m, κ} r @ mut_component default_rt default (mut_type_fixpoint_iter F k) i)%I ≡
        (l ◁ₗ{π, m, κ} r @ mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i)%I) as Heq.
      { apply equiv_dist => n. eapply HTypeDist_component_shr.
        exact (mut_type_fixpoint_iter_unfold_dist F k n). }
      rewrite -Heq. done.
  Qed.

  Lemma mut_type_fixpoint_subtype_1 {rts : list RT} (F : mut_type_fun rts) k
      `{!MutTypeNonExpansive F}
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) E L i
      (r : lnth default_rt rts i) :
    subtype E L r r
      (mut_component default_rt default (mut_type_fixpoint_iter F k) i)
      (mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i).
  Proof.
    iIntros (?) "HL HE".
    iSplitR; last iApply mut_type_fixpoint_incl_1.
    iPureIntro. intros m.
    eapply HTypeSynTypeEq_component.
    eapply HForallTwo_impl; last exact (mut_type_fixpoint_iter_unfold_dist F k 0).
    intros rt ty ty' Hdist m'. destruct Hdist as [Hst _ _ _]. exact (Hst m').
  Qed.

  Lemma mut_type_fixpoint_subtype_2 {rts : list RT} (F : mut_type_fun rts) k
      `{!MutTypeNonExpansive F}
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) E L i
      (r : lnth default_rt rts i) :
    subtype E L r r
      (mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i)
      (mut_component default_rt default (mut_type_fixpoint_iter F k) i).
  Proof.
    iIntros (?) "HL HE".
    iSplitR; last iApply mut_type_fixpoint_incl_2.
    iPureIntro. intros m.
    symmetry. eapply HTypeSynTypeEq_component.
    eapply HForallTwo_impl; last exact (mut_type_fixpoint_iter_unfold_dist F k 0).
    intros rt ty ty' Hdist m'. destruct Hdist as [Hst _ _ _]. exact (Hst m').
  Qed.

  Lemma mut_type_fixpoint_unfold_eqtype {rts : list RT} (F : mut_type_fun rts) k
      `{!MutTypeNonExpansive F}
      `{!MutTypeContractive (mut_iter F k)}
      `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
      (default_rt : RT) (default : type default_rt) E L i
      (r : lnth default_rt rts i) :
    eqtype E L r r
      (mut_component default_rt default (mut_type_fixpoint_iter F k) i)
      (mut_component default_rt default (F (mut_type_fixpoint_iter F k)) i).
  Proof.
    split.
    - apply (mut_type_fixpoint_subtype_1 F k).
    - apply (mut_type_fixpoint_subtype_2 F k).
  Qed.
End fixpoint.

Arguments mut_component {_ _} _ _ _ _.

Definition mut_fixpoint_def `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !TCNoResolve(MutTypeNonExpansive F)}
    `{Hcontr : !TCNoResolve (MutTypeContractive (mut_iter F (length rts)))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts} : mut_types rts.
Proof.
  unfold TCNoResolve in *.
  refine (mut_type_fixpoint_iter F (length rts)).
Defined.
Definition mut_fixpoint_aux : seal (@mut_fixpoint_def). Proof. by eexists. Qed.
Definition mut_fixpoint := mut_fixpoint_aux.(unseal).
Definition mut_fixpoint_unfold : @mut_fixpoint = @mut_fixpoint_def :=
  mut_fixpoint_aux.(seal_eq).
Global Arguments mut_fixpoint {_ _} {_} _ {_ _ _}.

Lemma ty_lfts_rew `{!typeGS Σ} {rt rt'} (H : rt = rt') (ty : type rt) :
  ty_lfts (rew [type] H in ty) = ty_lfts ty.
Proof. destruct H. done. Qed.

Lemma ty_wf_E_rew `{!typeGS Σ} {rt rt'} (H : rt = rt') (ty : type rt) :
  ty_wf_E (rew [type] H in ty) = ty_wf_E ty.
Proof. destruct H. done. Qed.

Lemma ty_metadata_kind_rew `{!typeGS Σ} {rt rt'} (H : rt = rt') (ty : type rt) :
  ty_metadata_kind (rew [type] H in ty) = ty_metadata_kind ty.
Proof. destruct H. done. Qed.

Lemma ty_sidecond_rew `{!typeGS Σ} {rt rt'} (H : rt = rt') (ty : type rt) :
  ty_sidecond (rew [type] H in ty) ≡ ty_sidecond ty.
Proof. destruct H. done. Qed.

Lemma ty_syn_type_rew `{!typeGS Σ} {rt rt'} (H : rt = rt') (ty : type rt) m :
  ty_syn_type (rew [type] H in ty) m = ty_syn_type ty m.
Proof. destruct H. done. Qed.

Lemma ty_has_op_type_rew `{!typeGS Σ} {rt rt'} (H : rt = rt') (ty : type rt) ot :
  ty_has_op_type (rew [type] H in ty) ot ↔ ty_has_op_type ty ot.
Proof. destruct H. done. Qed.

Lemma ty_ghost_drop_rew `{!typeGS Σ} {rt rt'} (H : rt = rt')
    (ty : type rt) π (r : rt') :
  _ty_ghost_drop (rew [type] H in ty) π r ≡
  _ty_ghost_drop ty π (rew <-[RT_rt] H in r).
Proof. destruct H. done. Qed.

Lemma mut_fixpoint_project_ty_lfts `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !TCNoResolve (MutTypeNonExpansive F)}
    `{Hcontr : !TCNoResolve (MutTypeContractive (mut_iter F (length rts)))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) :
  ty_lfts (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) =
  mut_lfts (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0).
Proof.
  rewrite mut_fixpoint_unfold /mut_fixpoint_def.
  rewrite mut_type_project_unfold /mut_type_project_def.
  rewrite ty_lfts_rew.
  eapply mut_type_fixpoint_lfts.
  eexists. exact Hlook.
Qed.

Lemma mut_fixpoint_project_ty_wf_E `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) :
  ty_wf_E (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) =
  mut_wf_E (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 1).
Proof.
  rewrite mut_fixpoint_unfold /mut_fixpoint_def.
  rewrite mut_type_project_unfold /mut_type_project_def.
  rewrite ty_wf_E_rew.
  eapply mut_type_fixpoint_wf_E.
  eexists. exact Hlook.
Qed.

Lemma mut_fixpoint_project_ty_ghost_drop `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) π r :
  _ty_ghost_drop (mut_type_project (mut_fixpoint F  (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) π r ≡ True%I.
Proof.
  rewrite mut_fixpoint_unfold /mut_fixpoint_def.
  rewrite mut_type_project_unfold /mut_type_project_def.
  rewrite ty_ghost_drop_rew.
  eapply mut_type_fixpoint_ghost_drop.
  eexists. exact Hlook.
Qed.

Fixpoint mut_type_project_simpl `{!typeGS Σ} {rts : list RT} (tys : mut_types rts)
    {struct tys} : ∀ {rt : RT} `{!Inhabited (RT_xt rt)} (i : nat),
    rts !! i = Some rt → type rt :=
  match tys in hlist _ rts return ∀ {rt : RT} `{!Inhabited (RT_xt rt)} (i : nat),
      rts !! i = Some rt → type rt with
  | +[] => λ rt _ i,
      match i as i return [] !! i = Some rt → type rt with
      | 0 => λ Hlook, False_rect (type rt) (None_ne_Some rt Hlook)
      | S _ => λ Hlook, False_rect (type rt) (None_ne_Some rt Hlook)
      end
  | @hcons _ _ rt0 rts' ty tys' => λ rt Hinh i Hlook,
      match i as i return (rt0 :: rts') !! i = Some rt → type rt with
      | 0 => λ Hlook0,
          rew [type] (f_equal (λ x, match x with Some rt => rt | None => rt0 end) Hlook0) in ty
      | S i' => λ HlookS, mut_type_project_simpl tys' i' HlookS
      end Hlook
  end.

Lemma mut_type_project_simpl_head_eq `{!typeGS Σ} {rt rts}
    `{!Inhabited (RT_xt rt)} (ty : type rt) (tys : mut_types rts)
    (Hlook : (rt :: rts) !! 0 = Some rt) :
  mut_type_project_simpl (ty +:: tys) 0 Hlook = ty.
Proof.
  replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  done.
Qed.

Lemma mut_type_project_simpl_tail_eq `{!typeGS Σ} {rt0 rt rts}
    `{!Inhabited (RT_xt rt)} (ty : type rt0) (tys : mut_types rts)
    i (Hlook : (rt0 :: rts) !! S i = Some rt) :
  mut_type_project_simpl (ty +:: tys) (S i) Hlook =
    mut_type_project_simpl tys i Hlook.
Proof. done. Qed.

Lemma mut_type_project_simpl_eq `{!typeGS Σ} {rts : list RT} (tys : mut_types rts)
    {rt : RT} {Hrt : Inhabited (RT_xt rt)} i (Hlook : rts !! i = Some rt) :
  mut_type_project_simpl tys i Hlook = mut_type_project tys i Hlook.
Proof.
  revert rt Hrt i Hlook.
  induction tys as [|rt0 rts ty tys IH]; intros rt ? i Hlook.
  - destruct i; discriminate.
  - destruct i as [|i]; simpl in Hlook.
    + injection Hlook as <-.
      replace Hlook with (@eq_refl (option RT) (Some rt0)) by apply proof_irrelevance.
      rewrite mut_type_project_simpl_head_eq mut_type_project_cons_head_eq. done.
    + rewrite mut_type_project_simpl_tail_eq.
      rewrite -(mut_type_project_cons_tail_eq (ty +:: tys) i Hlook Hlook).
      apply IH.
Qed.

Lemma mut_fixpoint_project_ty_sidecond `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) :
  ty_sidecond (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) ≡
  ty_sidecond
    (mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 1) i Hlook).
Proof.
  rewrite mut_type_project_simpl_eq.
  rewrite mut_fixpoint_unfold /mut_fixpoint_def.
  rewrite !mut_type_project_unfold /mut_type_project_def.
  rewrite !ty_sidecond_rew.
  eapply mut_type_fixpoint_sidecond.
Qed.

Global Instance type_dist_mut_type_project_cons_head `{!typeGS Σ} {rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt) (tys tys' : mut_types rts)
    (Hlook Hlook' : (rt :: rts) !! 0 = Some rt) :
  TypeDist n ty ty' →
  TypeDist n (mut_type_project (ty +:: tys) 0 Hlook)
    (mut_type_project (ty' +:: tys') 0 Hlook').
Proof.
  intros Hdist.
  replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  replace Hlook' with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  rewrite !mut_type_project_cons_head_eq. exact Hdist.
Qed.

Global Instance type_dist2_mut_type_project_cons_head `{!typeGS Σ} {rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt) (tys tys' : mut_types rts)
    (Hlook Hlook' : (rt :: rts) !! 0 = Some rt) :
  TypeDist2 n ty ty' →
  TypeDist2 n (mut_type_project (ty +:: tys) 0 Hlook)
    (mut_type_project (ty' +:: tys') 0 Hlook').
Proof.
  intros Hdist.
  replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  replace Hlook' with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  rewrite !mut_type_project_cons_head_eq. exact Hdist.
Qed.

Global Instance type_dist_later_mut_type_project_cons_head `{!typeGS Σ} {rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt) (tys tys' : mut_types rts)
    (Hlook Hlook' : (rt :: rts) !! 0 = Some rt) :
  TypeDistLater n ty ty' →
  TypeDistLater n (mut_type_project (ty +:: tys) 0 Hlook)
    (mut_type_project (ty' +:: tys') 0 Hlook').
Proof.
  intros Hdist.
  replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  replace Hlook' with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  rewrite !mut_type_project_cons_head_eq. exact Hdist.
Qed.

Global Instance type_dist_later2_mut_type_project_cons_head `{!typeGS Σ} {rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt) (tys tys' : mut_types rts)
    (Hlook Hlook' : (rt :: rts) !! 0 = Some rt) :
  TypeDistLater2 n ty ty' →
  TypeDistLater2 n (mut_type_project (ty +:: tys) 0 Hlook)
    (mut_type_project (ty' +:: tys') 0 Hlook').
Proof.
  intros Hdist.
  replace Hlook with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  replace Hlook' with (@eq_refl (option RT) (Some rt)) by apply proof_irrelevance.
  rewrite !mut_type_project_cons_head_eq. exact Hdist.
Qed.

Global Instance type_dist_mut_type_project_cons_tail `{!typeGS Σ} {rt0 rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt0) (tys tys' : mut_types rts)
    i (Hlook Hlook' : (rt0 :: rts) !! S i = Some rt) :
  TypeDist n (mut_type_project tys i Hlook) (mut_type_project tys' i Hlook') →
  TypeDist n (mut_type_project (ty +:: tys) (S i) Hlook)
    (mut_type_project (ty' +:: tys') (S i) Hlook').
Proof.
  intros Hdist.
  rewrite -(mut_type_project_cons_tail_eq (ty +:: tys) i Hlook Hlook).
  rewrite -(mut_type_project_cons_tail_eq (ty' +:: tys') i Hlook' Hlook').
  exact Hdist.
Qed.

Global Instance type_dist2_mut_type_project_cons_tail `{!typeGS Σ} {rt0 rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt0) (tys tys' : mut_types rts)
    i (Hlook Hlook' : (rt0 :: rts) !! S i = Some rt) :
  TypeDist2 n (mut_type_project tys i Hlook) (mut_type_project tys' i Hlook') →
  TypeDist2 n (mut_type_project (ty +:: tys) (S i) Hlook)
    (mut_type_project (ty' +:: tys') (S i) Hlook').
Proof.
  intros Hdist.
  rewrite -(mut_type_project_cons_tail_eq (ty +:: tys) i Hlook Hlook).
  rewrite -(mut_type_project_cons_tail_eq (ty' +:: tys') i Hlook' Hlook').
  exact Hdist.
Qed.

Global Instance type_dist_later_mut_type_project_cons_tail `{!typeGS Σ} {rt0 rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt0) (tys tys' : mut_types rts)
    i (Hlook Hlook' : (rt0 :: rts) !! S i = Some rt) :
  TypeDistLater n (mut_type_project tys i Hlook) (mut_type_project tys' i Hlook') →
  TypeDistLater n (mut_type_project (ty +:: tys) (S i) Hlook)
    (mut_type_project (ty' +:: tys') (S i) Hlook').
Proof.
  intros Hdist.
  rewrite -(mut_type_project_cons_tail_eq (ty +:: tys) i Hlook Hlook).
  rewrite -(mut_type_project_cons_tail_eq (ty' +:: tys') i Hlook' Hlook').
  exact Hdist.
Qed.

Global Instance type_dist_later2_mut_type_project_cons_tail `{!typeGS Σ} {rt0 rt rts} n
    `{!Inhabited (RT_xt rt)} (ty ty' : type rt0) (tys tys' : mut_types rts)
    i (Hlook Hlook' : (rt0 :: rts) !! S i = Some rt) :
  TypeDistLater2 n (mut_type_project tys i Hlook) (mut_type_project tys' i Hlook') →
  TypeDistLater2 n (mut_type_project (ty +:: tys) (S i) Hlook)
    (mut_type_project (ty' +:: tys') (S i) Hlook').
Proof.
  intros Hdist.
  rewrite -(mut_type_project_cons_tail_eq (ty +:: tys) i Hlook Hlook).
  rewrite -(mut_type_project_cons_tail_eq (ty' +:: tys') i Hlook' Hlook').
  exact Hdist.
Qed.

Lemma mut_fixpoint_project_ty_syn_type `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) m :
  ty_syn_type (mut_type_project (mut_fixpoint F  (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) m =
  ty_syn_type
    (mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook) m.
Proof.
  rewrite mut_type_project_simpl_eq.
  rewrite mut_fixpoint_unfold /mut_fixpoint_def.
  rewrite !mut_type_project_unfold /mut_type_project_def.
  rewrite !ty_syn_type_rew.
  eapply mut_type_fixpoint_syn_type.
Qed.

Lemma mut_fixpoint_project_ty_has_op_type `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) ot :
  ty_has_op_type (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) ot ↔
  ty_has_op_type
    (mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook) ot.
Proof.
  rewrite mut_type_project_simpl_eq.
  rewrite mut_fixpoint_unfold /mut_fixpoint_def.
  rewrite !mut_type_project_unfold /mut_type_project_def.
  rewrite !ty_has_op_type_rew.
  eapply mut_type_fixpoint_has_op_type.
Qed.
Lemma mut_fixpoint_project_ty_has_op_type_1 `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) ot :
  ty_has_op_type
    (mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook) ot →
  ty_has_op_type (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) ot.
Proof.
  apply mut_fixpoint_project_ty_has_op_type.
Qed.
Lemma mut_fixpoint_project_ty_has_op_type_1_canonical `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt) :
  ty_has_op_type
    (mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook) (use_op_alg' (st_of (mut_type_project_simpl (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook) MetaNone)) →
  ty_has_op_type (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) (use_op_alg' (st_of (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook) MetaNone)).
Proof.
  intros Ha.
  apply mut_fixpoint_project_ty_has_op_type_1.
  rewrite mut_fixpoint_project_ty_syn_type//.
Qed.

Lemma mut_fixpoint_project_sized `{!typeGS Σ} {rts : list RT}
    (F : mut_type_fun rts)
    `{Hne : !MutTypeNonExpansive F}
    `{Hcontr : !MutTypeContractive (mut_iter F (length rts))}
    `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}
    {rt : RT} `{!Inhabited (RT_xt rt)} i
    (Hlook : rts !! i = Some rt)
    `{!TySized (mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook)} :
  TySized (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook).
Proof.
  constructor.
  - rewrite mut_fixpoint_unfold /mut_fixpoint_def.
    rewrite mut_type_project_unfold /mut_type_project_def.
    rewrite ty_metadata_kind_rew.
    rewrite /mut_type_fixpoint_iter.
    rewrite mut_type_fixpoint_metadata_kind.
    pose proof (ty_sized_metadata_none (ty := mut_type_project_simpl
      (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 0) i Hlook)) as Hsized.
    rewrite mut_type_project_simpl_eq in Hsized.
    rewrite mut_type_project_unfold /mut_type_project_def ty_metadata_kind_rew in Hsized.
    exact Hsized.
  - intros m1 m2.
    rewrite !mut_fixpoint_project_ty_syn_type.
    apply ty_sized_syn_type_eq.
Qed.
Global Hint Extern 10 (TySized (mut_type_project _ _ _)) =>
  apply mut_fixpoint_project_sized; simpl : typeclass_instances.

Section rules.
  Context `{!typeGS Σ}.
  Context {rts : list RT}.
  Context (F : mut_type_fun rts)
  `{Hne : !TCNoResolve (MutTypeNonExpansive F)}.
  Context `{Hcontr : !TCNoResolve (MutTypeContractive (mut_iter F (length rts)))}.
  Context `{!TCTForall (λ rt, Inhabited (RT_xt rt)) rts}.
  Context {rt : RT} `{!Inhabited (RT_xt rt)}.
  Context (i : nat) (Hlook : rts !! i = Some rt).

  Local Definition mut_fixpoint_project : type rt :=
    mut_type_project (mut_fixpoint F  (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook.

  Local Definition mut_fixpoint_project_unfolded : type rt :=
    mut_type_project_simpl (F (mut_fixpoint F  (Hne:=Hne) (Hcontr:=Hcontr))) i Hlook.

  Local Lemma subtype_rew_r {rt1 rt2 : RT} (Heq : rt1 = rt2) E L
      (r : rt2) (ty1 ty2 : type rt1) :
    subtype E L (rew <-[RT_rt] Heq in r) (rew <-[RT_rt] Heq in r) ty1 ty2 →
    subtype E L r r (rew [type] Heq in ty1) (rew [type] Heq in ty2).
  Proof. destruct Heq. done. Qed.

  Lemma mut_type_project_fixpoint_subtype_1 E L r :
    subtype E L r r mut_fixpoint_project mut_fixpoint_project_unfolded.
  Proof.
    rewrite /mut_fixpoint_project /mut_fixpoint_project_unfolded.
    rewrite mut_type_project_simpl_eq.
    rewrite !mut_type_project_unfold /mut_type_project_def.
    rewrite mut_fixpoint_unfold /mut_fixpoint_def.
    simpl.
    eapply subtype_rew_r.
    unfold TCNoResolve in *.
    apply (mut_type_fixpoint_subtype_1 F (length rts)).
  Qed.

  Lemma mut_type_project_fixpoint_subtype_2 E L r :
    subtype E L r r mut_fixpoint_project_unfolded mut_fixpoint_project.
  Proof.
    rewrite /mut_fixpoint_project /mut_fixpoint_project_unfolded.
    rewrite mut_type_project_simpl_eq.
    rewrite !mut_type_project_unfold /mut_type_project_def.
    rewrite mut_fixpoint_unfold /mut_fixpoint_def.
    simpl.
    eapply subtype_rew_r.
    unfold TCNoResolve in *.
    apply (mut_type_fixpoint_subtype_2 F (length rts)).
  Qed.

  Lemma mut_type_project_fixpoint_unfold_eqtype E L r :
    eqtype E L r r mut_fixpoint_project mut_fixpoint_project_unfolded.
  Proof.
    split.
    - apply mut_type_project_fixpoint_subtype_1.
    - apply mut_type_project_fixpoint_subtype_2.
  Qed.

  Lemma mut_type_project_fixpoint_unfold_eqltype E L :
    full_eqltype E L (◁ mut_fixpoint_project)%I (◁ mut_fixpoint_project_unfolded)%I.
  Proof.
    apply full_eqtype_eqltype.
    intros ?.
    apply mut_type_project_fixpoint_unfold_eqtype.
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

  Lemma owned_subltype_step_mut_fixpoint_id π E L step l r1 r2 T :
    owned_subltype_step π E L step l r1 r2 (◁ mut_fixpoint_project) (◁ mut_fixpoint_project) T :-
    exhale (⌜r1 = r2⌝);
    return T L True%I.
  Proof.
    iIntros "(-> & HT)".
    iIntros (????) "CTX HE HL Hl".
    iExists L, True%I. iFrame.
    iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition owned_subltype_step_mut_fixpoint_id_inst := [instance @owned_subltype_step_mut_fixpoint_id].
  Global Existing Instance owned_subltype_step_mut_fixpoint_id_inst | 5.

  Lemma owned_subltype_step_mut_fixpoint_r {rt1} (lt1 : ltype rt1) π E L step l r1 r2 T :
    owned_subltype_step π E L step l r1 r2 lt1 (◁ mut_fixpoint_project) T :-
    return (owned_subltype_step π E L step l r1 r2 lt1 (◁ mut_fixpoint_project_unfolded) T).
  Proof.
    iIntros "HT" (F' ???) "#CTX #HE HL Hl".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "(%Hst & #Heq)".
    { apply mut_type_project_fixpoint_unfold_eqltype. }
    iDestruct ("Heq" $! Owned r2) as "[_ #Hincl]".
    iMod ("HT" with "[] [] [] CTX HE HL Hl") as "(%L' & %R & Hstep & HL & HT)"; [done.. | ].
    iExists L', R. iFrame "HL HT".
    iApply maybe_logical_step_fupd.
    iApply (maybe_logical_step_wand with "[] Hstep").
    iIntros "(Hl & $)".
    iDestruct "Hincl" as "(#Hincl & _)".
    iApply (fupd_mask_mono with "(Hincl Hl)"); done.
  Qed.
  Definition owned_subltype_step_mut_fixpoint_r_inst := [instance @owned_subltype_step_mut_fixpoint_r].
  Global Existing Instance owned_subltype_step_mut_fixpoint_r_inst | 6.

  (** Unfold the target after stratification, and use the same source ownership
      to introduce its outer invariant. *)
  Lemma introduce_owned_invariant_mut_fixpoint π E L l {rt1}
      (lt : ltype rt1) (r1 : place_rfn rt1) (r : place_rfn rt) T :
    introduce_owned_invariant π E L l lt r1 mut_fixpoint_project_unfolded r T
    ⊢ introduce_owned_invariant π E L l lt r1 mut_fixpoint_project r T.
  Proof.
    iIntros "HT" (F' ???) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "(%Hst & #Heq)".
    { apply mut_type_project_fixpoint_unfold_eqltype. }
    iDestruct ("Heq" $! Owned r) as "[_ #Hincl]".
    iMod ("HT" with "[//] [//] [//] CTX HE HL")
      as "(%L' & %κs & %R & Hstep & HL & HT)".
    iExists L', κs, R. iFrame "HL HT".
    iModIntro.
    iApply (logical_step_wand with "Hstep").
    iIntros "($ & Hconvert) Hdead Hl".
    iMod ("Hconvert" with "Hdead Hl") as "Hl".
    by iApply (ltype_incl_use with "Hincl Hl").
  Qed.
  Definition introduce_owned_invariant_mut_fixpoint_inst := [instance @introduce_owned_invariant_mut_fixpoint].
  Global Existing Instance introduce_owned_invariant_mut_fixpoint_inst | 10.

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

  Lemma weak_subltype_mut_fixpoint_id E L b r1 r2 T :
    weak_subltype E L b r1 r2 (◁ mut_fixpoint_project) (◁ mut_fixpoint_project) T :-
    exhale (⌜r1 = r2⌝);
    return T.
  Proof.
    iIntros "(-> & HT)".
    by iApply weak_subltype_id.
  Qed.
  Definition weak_subltype_mut_fixpoint_id_inst := [instance @weak_subltype_mut_fixpoint_id].
  Global Existing Instance weak_subltype_mut_fixpoint_id_inst | 5.

  Lemma weak_subltype_mut_fixpoint_r {rt1} (lt1 : ltype rt1) E L b r1 r2 T :
    weak_subltype E L b r1 r2 lt1 (◁ mut_fixpoint_project) T :-
    return (weak_subltype E L b r1 r2 lt1 (◁ mut_fixpoint_project_unfolded) T).
  Proof.
    iIntros "HT" (F' ?) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "(%Hst & #Heq)".
    { apply mut_type_project_fixpoint_unfold_eqltype. }
    iMod ("HT" with "[] CTX HE HL") as "(%Hst' & Hincl & HL & $)"; first done.
    iFrame. iModIntro. iSplit.
    { iPureIntro. rewrite Hst. done. }
    iApply (ltype_incl_trans with "Hincl").
    iApply ltype_eq_ltype_incl_r.
    iApply "Heq".
  Qed.
  Definition weak_subltype_mut_fixpoint_r_inst := [instance @weak_subltype_mut_fixpoint_r].
  Global Existing Instance weak_subltype_mut_fixpoint_r_inst | 6.

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

  Lemma mut_eqltype_mut_fixpoint_id E L T :
    mut_eqltype E L (◁ mut_fixpoint_project) (◁ mut_fixpoint_project) T :-
    return T.
  Proof.
    unfold mut_eqltype.
    iIntros "$". iPureIntro.
    reflexivity.
  Qed.
  Definition mut_eqltype_mut_fixpoint_id_inst := [instance @mut_eqltype_mut_fixpoint_id].
  Global Existing Instance mut_eqltype_mut_fixpoint_id_inst | 5.

  Lemma mut_eqltype_mut_fixpoint_r (lt1 : ltype rt) E L T :
    mut_eqltype E L lt1 (◁ mut_fixpoint_project) T :-
    return (mut_eqltype E L lt1 (◁ mut_fixpoint_project_unfolded) T).
  Proof.
    unfold mut_eqltype.
    iIntros "(%Heq & $)". iPureIntro.
    etrans; first apply Heq.
    symmetry.
    apply mut_type_project_fixpoint_unfold_eqltype.
  Qed.
  Definition mut_eqltype_mut_fixpoint_r_inst := [instance @mut_eqltype_mut_fixpoint_r].
  Global Existing Instance mut_eqltype_mut_fixpoint_r_inst | 6.

  Lemma simplify_goal_mut_fixpoint_project_sidecond T :
    ty_sidecond (mut_type_project_simpl (mut_Fn_canon (mut_iter F (length rts)) TCTForall0 1) i Hlook) ∗ T
    ⊢ simplify_goal (ty_sidecond (mut_type_project (mut_fixpoint F (Hne:=Hne) (Hcontr:=Hcontr)) i Hlook)) T.
  Proof.
    unfold simplify_goal. rewrite mut_fixpoint_project_ty_sidecond.
    done.
  Qed.
  Definition simplify_goal_mut_fixpoint_project_sidecond_inst := [instance @simplify_goal_mut_fixpoint_project_sidecond with 0%N].
  Global Existing Instance simplify_goal_mut_fixpoint_project_sidecond_inst.
End rules.

Section decompose_mut_type_contractive.
  Context `{!typeGS Σ}.

  (** Decompose [MutTypeContractive]/[MutTypeNonExpansive] over [mut_types _ → mut_types _] functors into [MutHTypeContractive]/[MutHTypeNonExpansive] *)

  Class MutHTypeContractive {rts rts'}
      (F : mut_type_fun rts) (G : mut_types rts → mut_types rts') : Type := {
    mut_htype_ctr_syn_type : ∀ tys tys', HTypeSynTypeEq (G tys) (G tys');
    mut_htype_ctr_sidecond : ∀ tys tys',
      HTypeSynTypeEq tys tys' → HTypeSidecondEq (G tys) (G tys');
    mut_htype_ctr_has_op_type : ∀ tys tys', HTypeHasOpTypeEq (G tys) (G tys');
    mut_htype_ctr_dist : ∀ n tys tys',
      HTypeDist2 n tys tys' → HTypeDist n (G tys) (G tys');
    mut_htype_ctr_dist2 : ∀ n tys tys',
      HTypeDistLater2 n tys tys' → HTypeDist2 n (G tys) (G tys');
  }.

  Class MutHTypeNonExpansive {rts rts'}
      (G : mut_types rts → mut_types rts') : Type := {
    mut_htype_ne_dist : ∀ n tys tys',
      HTypeDist n tys tys' → HTypeDist n (G tys) (G tys');
    mut_htype_ne_dist2 : ∀ n tys tys',
      HTypeDist2 n tys tys' → HTypeDist2 n (G tys) (G tys');
  }.


  Global Instance mut_type_ne_of_htype {rts} (F : mut_type_fun rts) :
    MutHTypeNonExpansive F → MutTypeNonExpansive F.
  Proof.
    intros HF. constructor.
    - apply mut_htype_ne_dist.
    - apply mut_htype_ne_dist2.
  Qed.

  Global Instance mut_type_contractive_of_htype {rts} (F : mut_type_fun rts) :
    LftMorphism F →
    MutHTypeContractive F F → MutTypeContractive F.
  Proof.
    intros Hlft HF. constructor.
    - exact Hlft.
    - apply mut_htype_ctr_syn_type.
    - apply mut_htype_ctr_sidecond.
    - apply mut_htype_ctr_has_op_type.
    - apply mut_htype_ctr_dist.
    - apply mut_htype_ctr_dist2.
  Qed.
End decompose_mut_type_contractive.

Section decompose_mut_htype_contractive.
  Context `{!typeGS Σ}.

  (** Decompose [MutHTypeContractive]/[MutHTypeNonExpansive] into componentwise contractiveness/non-expansiveness. *)

  Class MutComponentContractive {rts rt}
      (F : mut_type_fun rts) (G : mut_types rts → type rt) : Type := {
    mut_comp_ctr_syn_type : ∀ tys tys' m,
      ty_syn_type (G tys) m = ty_syn_type (G tys') m;
    mut_comp_ctr_sidecond : ∀ tys tys',
      HTypeSynTypeEq tys tys' → ty_sidecond (G tys) ≡ ty_sidecond (G tys');
    mut_comp_ctr_has_op_type : ∀ tys tys' ot,
      ty_has_op_type (G tys) ot ↔ ty_has_op_type (G tys') ot;
    mut_comp_ctr_dist : ∀ n tys tys',
      HTypeDist2 n tys tys' → TypeDist n (G tys) (G tys');
    mut_comp_ctr_dist2 : ∀ n tys tys',
      HTypeDistLater2 n tys tys' → TypeDist2 n (G tys) (G tys');
  }.

  Class MutComponentNonExpansive {rts rt}
      (G : mut_types rts → type rt) : Type := {
    mut_comp_ne_dist : ∀ n tys tys',
      HTypeDist n tys tys' → TypeDist n (G tys) (G tys');
    mut_comp_ne_dist2 : ∀ n tys tys',
      HTypeDist2 n tys tys' → TypeDist2 n (G tys) (G tys');
  }.

  Global Instance mut_htype_ne_nil {rts} :
    MutHTypeNonExpansive (λ _ : mut_types rts, +[]).
  Proof. constructor; intros; constructor. Qed.

  Global Instance mut_htype_contractive_nil {rts} (F : mut_type_fun rts) :
    MutHTypeContractive F (λ _ : mut_types rts, +[]).
  Proof. constructor; intros; constructor. Qed.

  Global Instance mut_htype_ne_cons {rts rt rts'}
      (G : mut_types rts → type rt)
      (Gs : mut_types rts → mut_types rts') :
    MutComponentNonExpansive G →
    MutHTypeNonExpansive Gs →
    MutHTypeNonExpansive (λ tys, G tys +:: Gs tys).
  Proof.
    intros HG HGs. constructor; intros; constructor.
    - eapply mut_comp_ne_dist; done.
    - eapply mut_htype_ne_dist; done.
    - eapply mut_comp_ne_dist2; done.
    - eapply mut_htype_ne_dist2; done.
  Qed.
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
    - apply mut_comp_ctr_has_op_type.
    - apply mut_htype_ctr_has_op_type.
    - eapply mut_comp_ctr_dist; done.
    - eapply mut_htype_ctr_dist; done.
    - eapply mut_comp_ctr_dist2; done.
    - eapply mut_htype_ctr_dist2; done.
  Qed.
End decompose_mut_htype_contractive.

Section decompose_mut_component_contractive.
  Context `{!typeGS Σ}.

  (** Decompose [MutComponentContractive]/[MutComponentNonExpansive] pointwise over the input functor,
    so that we can reduce to ordinary [TypeContractive]/[TypeNonExpansive] facts. *)

  Inductive MutComponentPointwiseNonExpansive :
      ∀ {rts rt}, (mut_types rts → type rt) → Type :=
  | mut_component_pointwise_ne_nil {rt}
      (G : mut_types [] → type rt) :
      MutComponentPointwiseNonExpansive G
  | mut_component_pointwise_ne_cons {rt rts rt'}
      (G : mut_types (rt :: rts) → type rt') :
      (∀ tys, TypeNonExpansive (λ ty : type rt, G (ty +:: tys))) →
      (∀ ty, MutComponentPointwiseNonExpansive (λ tys : mut_types rts, G (ty +:: tys))) →
      MutComponentPointwiseNonExpansive G.
  Existing Class MutComponentPointwiseNonExpansive.
  Global Existing Instance mut_component_pointwise_ne_nil.
  Global Existing Instance mut_component_pointwise_ne_cons.

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

  Local Lemma mut_component_pointwise_ne_dist {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseNonExpansive G →
    ∀ n tys tys', HTypeDist n tys tys' → TypeDist n (G tys) (G tys').
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros n tys tys' Hdist. dependent destruction tys. dependent destruction tys'. constructor; done.
    - intros n tys tys' Hdist. dependent destruction Hdist.
      eapply (TypeDist_trans n _ (G (y +:: xl)) _).
      { change (TypeDist n ((λ ty : type rt, G (ty +:: xl)) x)
          ((λ ty : type rt, G (ty +:: xl)) y)).
        apply type_dist_use_ne; [apply Hhead | done]. }
      eapply IHtail. done.
  Qed.

  Local Lemma mut_component_pointwise_ne_dist2 {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseNonExpansive G →
    ∀ n tys tys', HTypeDist2 n tys tys' → TypeDist2 n (G tys) (G tys').
  Proof.
    intros Hpw. induction Hpw as [rt G|rt rts rt' G Hhead _ IHtail].
    - intros n tys tys' Hdist. dependent destruction tys. dependent destruction tys'. constructor; done.
    - intros n tys tys' Hdist. dependent destruction Hdist.
      eapply (TypeDist2_trans n _ (G (y +:: xl)) _).
      { change (TypeDist2 n ((λ ty : type rt, G (ty +:: xl)) x)
          ((λ ty : type rt, G (ty +:: xl)) y)).
        apply type_dist2_use_ne; [apply Hhead | done]. }
      eapply IHtail. done.
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

  Global Instance mut_component_contractive_of_pointwise {rts rt}
      (F : mut_type_fun rts) (G : mut_types rts → type rt) :
    MutComponentPointwiseContractive G →
    MutComponentContractive F G.
  Proof.
    intros Hpw.
    constructor.
    - eapply mut_component_pointwise_syn_type; done.
    - eapply mut_component_pointwise_sidecond; done.
    - eapply mut_component_pointwise_has_op_type; done.
    - eapply mut_component_pointwise_dist; done.
    - eapply mut_component_pointwise_dist2; done.
  Qed.

  Global Instance mut_component_ne_of_pointwise {rts rt}
      (G : mut_types rts → type rt) :
    MutComponentPointwiseNonExpansive G →
    MutComponentNonExpansive G.
  Proof.
    intros Hpw. constructor.
    - eapply mut_component_pointwise_ne_dist; done.
    - eapply mut_component_pointwise_ne_dist2; done.
  Qed.
End decompose_mut_component_contractive.
