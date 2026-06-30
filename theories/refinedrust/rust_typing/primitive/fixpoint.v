From refinedrust Require Import type programs.
From refinedrust Require Import options.

Section fixpoint_def.
  Context `{!typeGS Σ}.

  (* We assume a contractive functor *)
  Context {rt : RT} (F : type rt → type rt) `{Hcr : !TypeContractive F}.
  (* [rt] needs to be inhabited *)
  Context `{!Inhabited (RT_xt rt)}.

  (* Iterate the functor [S n] times, starting with the inhabitant.
     We use at least one iteration, so that the [ty_syn_type] is always constant.
  *)
  Definition Fn n := Nat.iter (S n) F inhabitant.

  Lemma Fn_succ n :
    Fn (S n) = F (Fn n).
  Proof. done. Qed.

  Lemma Fn_syn_type_const n m x :
    ty_syn_type (Fn n) x = ty_syn_type (Fn m) x.
  Proof using Hcr.
    unfold Fn. simpl. apply Hcr.
  Qed.
  Lemma Fn_sidecond_const n :
    n ≥ 1 →
    ty_sidecond (Fn n) ≡ ty_sidecond (Fn 1).
  Proof using Hcr.
    unfold Fn; simpl. intros Hn.
    eapply Hcr. intros m.
    destruct n; first lia.
    erewrite (Fn_syn_type_const 0 ).
    done.
  Qed.

  Lemma Fn_lfts_const_0 n :
    ⊢ lft_equiv (lft_intersect_list (ty_lfts (Fn n))) (lft_intersect_list (ty_lfts (Fn 0))).
  Proof using Hcr.
    induction n as [ n IH] using lt_wf_ind.
    destruct n as [ | [ | n]].
    - iApply lft_equiv_refl.
    - iApply TyLftMorphism_ty_lfts_idempotent.
    - rewrite !Fn_succ.
      iApply lft_equiv_trans.
      { iApply TyLftMorphism_ty_lfts_idempotent. }
      iApply (IH (S n)). lia.
  Qed.
  Lemma Fn_wf_E_const_1 n :
    n ≥ 1 →
    elctx_interp (ty_wf_E (Fn n)) ≡ elctx_interp (ty_wf_E (Fn 1)).
  Proof using Hcr.
    intros ?.
    induction n as [ n IH] using lt_wf_ind.
    destruct n as [ | [ | [ | n]]].
    - lia.
    - reflexivity.
    - iApply TyLftMorphism_ty_wf_E_idempotent.
    - rewrite !Fn_succ.
      etrans.
      { eapply TyLftMorphism_ty_wf_E_idempotent. apply _. }
      iApply (IH (S (S n))); lia.
  Qed.

  Lemma Fn_has_op_type_const n m ot :
    ty_has_op_type (Fn n) ot ↔ ty_has_op_type (Fn m) ot.
  Proof using Hcr.
    unfold Fn; simpl. eapply Hcr.
  Qed.

  (* We define a chain consisting of the ownership and sharing predicate and take the fixpoint over that. *)
  Definition ty_own_shrO : ofe :=
    prodO (thread_id -d> rt -d> metadataO -d> val -d> iPropO Σ)
    ((lft -d> thread_id -d> rt -d> metadataO -d> loc -d> iPropO Σ)
           )
  .

  (* We have the [2+] in order to fix up the [0] base case *)
  Lemma ty_own_shr_cauchy (i n : nat) :
    n ≤ i →
    (∀ π r m v, dist_later n (v ◁ᵥ{π, m} r @ (Fn (2+i)))%I (v ◁ᵥ{π, m} r @ (Fn (2+n)))%I) ∧
    (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ (Fn (2+i)))%I ≡{n}≡ (l ◁ₗ{π, m, κ} r @ (Fn (2+n)))%I)
  .
  Proof using Hcr.
    induction n as [ | n IH] in i |-*; simpl; intros Hle.
    { split; first (intros; dist_later_intro; unfold_sidx; lia).
      intros. eapply Hcr. constructor.
      - eapply Hcr.
      - eapply Hcr. intros ?. erewrite (Fn_syn_type_const i 0); done.
      - intros. dist_later_2_intro; lia.
      - intros. dist_later_intro. unfold_sidx. lia.
    }
    destruct i; first lia.
    destruct (IH i) as [Hown Hshr ]; first lia.
    split.
    - intros. dist_later_intro.
      simpl. eapply Hcr. constructor.
      + eapply Hcr.
      + eapply Hcr. intros ?. rewrite (Fn_syn_type_const (1+i) (1+n)); done.
      + intros. dist_later_intro.
        eapply dist_later_fin_lt; [eapply Hown | ].
        unfold_sidx. lia.
      + intros. eapply dist_le; first apply Hshr.
        unfold_sidx.
        lia.
    - intros. simpl. eapply Hcr. constructor.
      + eapply Hcr.
      + eapply Hcr. intros ?. rewrite (Fn_syn_type_const (1+i) (1+n)); done.
      + intros. dist_later_2_intro. eapply dist_later_lt; first done. unfold_sidx. lia.
      + intros. dist_later_intro. eapply dist_le; first apply Hshr. unfold_sidx. lia.
  Qed.

  (* [3+] because that's what we need to apply the above lemma proving that the chain is Cauchy *)
  Program Definition F_ty_own_val_ty_shr_chain : chain ty_own_shrO := {|
    chain_car n := ((Fn (3 + n)).(ty_own_val), ((Fn (3+n)).(ty_shr)))
  |}.
  Next Obligation.
    simpl. intros n i Hle.
    destruct (ty_own_shr_cauchy (S i) (S n)) as [Hown Hshr]; first lia.
    constructor; simpl.
    - intros ????. eapply dist_later_lt; first eapply Hown. unfold_sidx. lia.
    - intros ?????. eapply dist_le; first eapply Hshr. lia.
  Qed.
  Definition F_ty_own_val_ty_shr_fixpoint : ty_own_shrO :=
    compl F_ty_own_val_ty_shr_chain.

  (* Now we are ready to define the fixpoint *)
  (* For the ownership and sharing predicate, we take the fixpoint found above. *)
  (* For the other components, we use the 0 base case (where the functor is applied at least once) in order to be able to show the unfolding equation later. *)
  Program Definition type_fixpoint : type rt := {|
    ty_xt_inhabited := (Fn 0).(ty_xt_inhabited);
    ty_metadata_kind := (Fn 0).(ty_metadata_kind);
    ty_trivial_drop := (Fn 0).(ty_trivial_drop);
    ty_syn_type := (Fn 0).(ty_syn_type);
    _ty_has_op_type := (Fn 0).(_ty_has_op_type _);
    ty_own_val := F_ty_own_val_ty_shr_fixpoint.1;
    ty_shr := F_ty_own_val_ty_shr_fixpoint.2;
    _ty_ghost_drop _ _ := True%I;
    ty_sidecond := (Fn 1).(ty_sidecond);
    _ty_lfts := ty_lfts (Fn 0);
    _ty_wf_E := ty_wf_E (Fn 1);
  |}.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?.
      simpl. erewrite Fn_syn_type_const. eapply ty_has_layout.
  Qed.
  Next Obligation.
    eapply _ty_op_type_stable.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?.
      simpl. rewrite -(Fn_sidecond_const (3+n)); first eapply ty_own_val_sidecond.
      lia.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?.
      simpl. rewrite -(Fn_sidecond_const (3+n)); first eapply ty_shr_sidecond.
      lia.
  Qed.
  Next Obligation.
    unfold TCNoResolve.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_Persistent.
      intros ? [] [] Heq. eapply Heq.
    - intros ?.
      simpl. eapply ty_shr_persistent.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?.
      simpl. erewrite Fn_syn_type_const. eapply ty_shr_aligned.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. do 9 f_equiv.
      { do 2 f_equiv. apply Heq. }
      apply Heq.
    - intros ?. simpl.
      iIntros "#RUST Hna Htok %% Hlb Hb".
      iApply fupd_logical_step.
      iPoseProof (Fn_lfts_const_0 (3+n)) as "[_ Hincl]".
      iMod (lft_incl_acc with "[] Htok") as "(%q' & Htok & Hcl_tok)"; first done.
      { iApply lft_intersect_mono; first iApply lft_incl_refl. iApply "Hincl". }
      rewrite ty_lfts_unfold.
      iPoseProof (ty_share with "RUST Hna Htok [] [//] Hlb Hb") as "Hlb"; first done.
      { erewrite Fn_syn_type_const. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hlb").
      iApply logical_step_intro.
      iModIntro. iIntros "($ & Htok)".
      iApply ("Hcl_tok" with "Htok").
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. do 2 f_equiv; eapply Heq.
    - intros ?.
      simpl. eapply ty_shr_mono.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    iIntros "_". iApply logical_step_intro. done.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving_compl.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv; first eapply Heq.
      eapply Heq.
    - intros ?.
      simpl. eapply _ty_memcast_compat.
      rewrite -ty_has_op_type_unfold.
      eapply Fn_has_op_type_const. by rewrite ty_has_op_type_unfold.
  Qed.
  Next Obligation.
    intros ly ? Hst.
    by eapply _ty_has_op_type_untyped.
  Qed.

  Lemma type_fixpoint_own_val_unfold_n n v π r m :
    (v ◁ᵥ{π, m} r @ type_fixpoint)%I ≡{n}≡ (v ◁ᵥ{π, m} r @ Fn (3+n))%I.
  Proof.
    rewrite {1}/ty_own_val/=/F_ty_own_val_ty_shr_fixpoint/=.
    etrans. { apply (conv_compl n _). }
    simpl. done.
  Qed.
  Lemma type_fixpoint_shr_unfold_n n l κ π r m :
    (l ◁ₗ{π, m, κ} r @ type_fixpoint)%I ≡{n}≡ (l ◁ₗ{π, m, κ} r @ Fn (3+n))%I.
  Proof.
    rewrite {1}/ty_shr/=/F_ty_own_val_ty_shr_fixpoint/=.
    etrans. { apply (conv_compl n _). }
    simpl. done.
  Qed.

  Lemma type_fixpoint_syn_type :
    type_fixpoint.(ty_syn_type) = (Fn 0).(ty_syn_type).
  Proof. done. Qed.
  Lemma type_fixpoint_sidecond :
    type_fixpoint.(ty_sidecond) = (Fn 1).(ty_sidecond).
  Proof. done. Qed.

  Lemma type_fixpoint_own_val_unfold v π r m :
    (v ◁ᵥ{π, m} r @ type_fixpoint)%I ≡ (v ◁ᵥ{π, m} r @ F type_fixpoint)%I.
  Proof.
    apply equiv_dist => n. rewrite type_fixpoint_own_val_unfold_n.
    rewrite Fn_succ.
    eapply Hcr. constructor.
    - rewrite type_fixpoint_syn_type. intros. erewrite Fn_syn_type_const; done.
    - rewrite type_fixpoint_sidecond. rewrite (Fn_sidecond_const (2+n)); first done.
      lia.
    - intros. dist_later_intro.
      rewrite type_fixpoint_own_val_unfold_n.
      eapply dist_later_lt.
      { eapply (ty_own_shr_cauchy n (S _)). unfold_sidx. lia. }
      unfold_sidx. lia.
    - intros.
      rewrite type_fixpoint_shr_unfold_n.
      etrans.
      { symmetry. eapply (ty_own_shr_cauchy (S n) (n)). lia. }
      done.
  Qed.
  Lemma type_fixpoint_shr_unfold l π κ r m :
    (l ◁ₗ{π, m, κ} r @ type_fixpoint)%I ≡ (l ◁ₗ{π, m, κ} r @ F type_fixpoint)%I.
  Proof.
    apply equiv_dist => n. rewrite type_fixpoint_shr_unfold_n.
    rewrite Fn_succ.
    eapply Hcr. constructor.
    - rewrite type_fixpoint_syn_type. intros ?. erewrite Fn_syn_type_const; done.
    - rewrite type_fixpoint_sidecond.
      rewrite (Fn_sidecond_const (2+n)); first done. lia.
    - intros. dist_later_2_intro.
      rewrite type_fixpoint_own_val_unfold_n.
      simpl. eapply dist_later_lt.
      { eapply (ty_own_shr_cauchy n). lia. }
      unfold_sidx. lia.
    - intros. dist_later_intro.
      rewrite type_fixpoint_shr_unfold_n.
      eapply dist_le.
      { eapply (ty_own_shr_cauchy n (S _) ). unfold_sidx. lia. }
      lia.
  Qed.
  Lemma type_fixpoint_equiv :
    type_fixpoint ≡ F type_fixpoint.
  Proof.
    (* The fixpoint operator does NOT preserve everything (e.g. the inhabitant),
       so this does not hold. *)
  Abort.

  Lemma type_fixpoint_ty_lfts :
    ty_lfts type_fixpoint = ty_lfts (Fn 0).
  Proof.
    rewrite {1}ty_lfts_unfold; simpl.
    done.
  Qed.
  Lemma type_fixpoint_ty_wf_E :
    ty_wf_E type_fixpoint = ty_wf_E (Fn 1).
  Proof.
    rewrite {1}ty_wf_E_unfold.
    done.
  Qed.

  (** NOTE: We do not have a generic ghost_drop instance, as the solution of the recursive cycle
      strongly depends on the particular type. *)
End fixpoint_def.


Lemma type_fixpoint_ne `{!typeGS Σ} {rt : RT} `{!Inhabited (RT_xt rt)} (T1 T2 : type rt → type rt)
    `{!TypeContractive T1, !TypeContractive T2, !NonExpansive T2} n :
  (∀ t, T1 t ≡{n}≡ T2 t) → type_fixpoint T1 ≡{n}≡ type_fixpoint T2.
Proof.
  intros Heq.
  constructor.
  - simpl.
    destruct (Heq inhabitant) as [?].
    unfold Fn; simpl.
    done.
  - simpl.
    destruct (Heq inhabitant) as [? Hot].
    move: Hot. rewrite ty_has_op_type_unfold. done.
  - iIntros (????).
    rewrite !type_fixpoint_own_val_unfold_n.
    f_equiv.
    generalize (3+n) as m'.
    induction m' as [ | m' IH]; simpl.
    { apply Heq. }
    specialize (Heq (Fn T1 m')).
    setoid_rewrite Heq.
    (* here we need that T2 is also non-expansive *)
    by rewrite IH.
  - iIntros (?????).
    rewrite !type_fixpoint_shr_unfold_n.
    my_f_equiv.
    generalize (3+n) as m'.
    induction m' as [ | m' IH]; simpl.
    { apply Heq. }
    specialize (Heq (Fn T1 m')).
    setoid_rewrite Heq.
    (* here we need that T2 is also non-expansive *)
    by rewrite IH.
  - iIntros (??).
    rewrite !ty_ghost_drop_unfold. done.
  - simpl. destruct (Heq inhabitant). done.
  - simpl. unfold Fn; simpl.
    eapply ty_sidecond_ne.
    rewrite -(Heq type_inhabitant).
    rewrite Heq. done.
  - intros. simpl. destruct (Heq inhabitant).
    rewrite ty_lfts_unfold. done.
  - intros.
    rewrite ty_wf_E_unfold.
    simpl. unfold Fn; simpl.
    eapply ty_wf_E_ne.
    (* uses that T2 is also non-expansive *)
    rewrite -(Heq type_inhabitant).
    rewrite Heq. done.
Qed.

(* TODO: should we also have something that states that fixpoint is TypeNonExpansive / TypeContractive? *)
(*Lemma type_fixpoint_type_ne `{!typeGS Σ} {rt} `{!Inhabited rt} (T1 T2 : type rt → type rt)*)
    (*`{!TypeContractive T1, !TypeContractive T2, !NonExpansive T2} n :*)
  (*(∀ t, T1 t ≡{n}≡ T2 t) → TypeNonExpansive (λ type_fixpoint T1)*)

Section fixpoint.
  Context `{!typeGS Σ}.
  Context {rt : RT} `{!Inhabited (RT_xt rt)} (T : type rt → type rt) {HT: TypeContractive T}.

  (* prevent [simpl] from unfolding it too much here *)
  Opaque prod_cofe.

  Global Instance type_fixpoint_copy :
    (∀ `(!Copyable ty), Copyable (T ty)) → Copyable (type_fixpoint T).
  Proof.
    intros ?.
    (* the chain is copyable *)
    assert (∀ n, Copyable (Fn T n)).
    { induction n as [ | n IH]; simpl; apply _. }
    constructor.
    - intros. rewrite /ty_own_val/= /F_ty_own_val_ty_shr_fixpoint/=.
      simpl.
      eapply @limit_preserving_compl.
      { eapply bi.limit_preserving_Persistent.
        intros n [][][Heq1 Heq2].
        simpl in *. apply Heq1. }
      apply _.
    - intros ? ? ? ? ? ? ? ?. intros.
      rewrite /ty_shr/ty_own_val/= /F_ty_own_val_ty_shr_fixpoint/=.
      eapply @limit_preserving_compl.
      { eapply bi.limit_preserving_entails; first apply _.
        intros n [][][Heq1 Heq2].
        repeat f_equiv; simpl; [apply Heq2 | apply Heq1]. }
      intros ?.
      erewrite Fn_syn_type_const; last done.
      eapply copy_shr_acc; done.
  Qed.

  (*
  Global Instance type_fixpoint_send :
    (∀ `(!Send ty), Send (T ty)) → Send (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply send_equiv.
    - exists bool. apply _.
    - done.
    - repeat (apply limit_preserving_forall=> ?).
      apply bi.limit_preserving_entails; solve_proper.
  Qed.

  Global Instance type_fixpoint_sync :
    (∀ `(!Sync ty), Sync (T ty)) → Sync (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply sync_equiv.
    - exists bool. apply _.
    - done.
    - repeat (apply limit_preserving_forall=> ?).
      apply bi.limit_preserving_entails; solve_proper.
  Qed.
  *)

  Lemma type_fixpoint_incl_1 r : ⊢ type_incl r r (type_fixpoint T) (T (type_fixpoint T)).
  Proof.
    iSplit; last iSplit.
    - iModIntro. simpl. rewrite type_ctr_sidecond; eauto.
    - iModIntro. iIntros (π ? v). rewrite type_fixpoint_own_val_unfold. eauto.
    - iModIntro. iIntros (????). rewrite type_fixpoint_shr_unfold. eauto.
  Qed.
  Lemma type_fixpoint_incl_2 r : ⊢ type_incl r r (T (type_fixpoint T)) (type_fixpoint T).
  Proof.
    iSplit; last iSplit.
    - iModIntro. simpl. rewrite type_ctr_sidecond; eauto.
    - iModIntro. iIntros (π ? v). rewrite type_fixpoint_own_val_unfold. eauto.
    - iModIntro. iIntros (????). rewrite type_fixpoint_shr_unfold. eauto.
  Qed.

  Lemma type_fixpoint_subtype_1 E L r : subtype E L r r (type_fixpoint T) (T (type_fixpoint T)).
  Proof.
    iIntros (?) "HL HE".
    iSplitR; last iApply type_fixpoint_incl_1.
    iPureIntro. rewrite !type_fixpoint_syn_type. apply HT.
  Qed.
  Lemma type_fixpoint_subtype_2 E L r : subtype E L r r (T (type_fixpoint T)) (type_fixpoint T).
  Proof.
    iIntros (?) "HL HE".
    iSplitR; last iApply type_fixpoint_incl_2.
    iPureIntro. rewrite !type_fixpoint_syn_type. apply HT.
  Qed.

  Lemma type_fixpoint_unfold_eqtype E L r : eqtype E L r r (type_fixpoint T) (T (type_fixpoint T)).
  Proof.
    split.
    - apply type_fixpoint_subtype_1.
    - apply type_fixpoint_subtype_2.
  Qed.
End fixpoint.

Section rules.
  Context `{!typeGS Σ}.
  Context {rt : RT} `{!Inhabited (RT_xt rt)}.
  Context (F : type rt → type rt) `{!TypeContractive F}.

  (* on place access, unfold *)
  Lemma typed_place_fixpoint_unfold π E L l r k1 bmin P (T : place_cont_t rt bmin) :
    typed_place π E L l (◁ (type_fixpoint F)) r bmin k1 P T :-
    return (typed_place π E L l (◁ (F (type_fixpoint F))) r bmin k1 P T).
  Proof.
    iApply typed_place_eqltype.
    apply full_eqtype_eqltype.
    intros ?.
    apply type_fixpoint_unfold_eqtype.
  Qed.
  Definition typed_place_fixpoint_unfold_inst := [instance typed_place_fixpoint_unfold].
  Global Existing Instance typed_place_fixpoint_unfold_inst.


  Lemma owned_subtype_fixpoint_id π E L b r1 r2 T :
    owned_subtype π E L b r1 r2 (type_fixpoint F) (type_fixpoint F) T :-
    exhale (⌜r1 = r2⌝);
    return T L.
  Proof.
    iIntros "Ha". by iApply owned_subtype_id.
  Qed.
  Definition owned_subtype_fixpoint_id_inst := [instance @owned_subtype_fixpoint_id].
  Global Existing Instance owned_subtype_fixpoint_id_inst | 5.

  Lemma owned_subtype_fixpoint_r {rt1} (ty1 : type rt1) π E L b r1 r2 T :
    owned_subtype π E L b r1 r2 ty1 (type_fixpoint F) T :-
    return (owned_subtype π E L b r1 r2 ty1 (F (type_fixpoint F)) T).
  Proof.
    iIntros "HT".
    iApply owned_subtype_subtype_r; last iApply "HT".
    apply type_fixpoint_subtype_2.
  Qed.
  Definition owned_subtype_fixpoint_r_inst := [instance @owned_subtype_fixpoint_r].
  Global Existing Instance owned_subtype_fixpoint_r_inst | 6.

  Lemma weak_subtype_fixpoint_id E L r1 r2 T :
    weak_subtype E L r1 r2 (type_fixpoint F) (type_fixpoint F) T :-
    exhale (⌜r1 = r2⌝); return T.
  Proof.
    iIntros "(-> & HT)". by iApply weak_subtype_id.
  Qed.
  Definition weak_subtype_fixpoint_id_inst := [instance @weak_subtype_fixpoint_id].
  Global Existing Instance weak_subtype_fixpoint_id_inst | 5.

  Lemma weak_subtype_fixpoint_r {rt1} (ty1 : type rt1) E L r1 r2 T :
    weak_subtype E L r1 r2 ty1 (type_fixpoint F) T :-
    return (weak_subtype E L r1 r2 ty1 (F (type_fixpoint F)) T).
  Proof.
    iIntros "HT".
    iApply weak_subtype_subtype_r; last done.
    apply type_fixpoint_subtype_2.
  Qed.
  Definition weak_subtype_fixpoint_r_inst := [instance @weak_subtype_fixpoint_r].
  Global Existing Instance weak_subtype_fixpoint_r_inst | 6.

  Lemma mut_subtype_fixpoint_id E L  T :
    mut_subtype E L (type_fixpoint F) (type_fixpoint F) T :-
    return T.
  Proof.
    unfold mut_subtype.
    iIntros "$". iPureIntro.
    reflexivity.
  Qed.
  Definition mut_subtype_fixpoint_id_inst := [instance @mut_subtype_fixpoint_id].
  Global Existing Instance mut_subtype_fixpoint_id_inst | 5.

  Lemma mut_subtype_fixpoint_r (ty1 : type rt) E L  T :
    mut_subtype E L ty1 (type_fixpoint F) T :-
    return (mut_subtype E L ty1 (F (type_fixpoint F)) T).
  Proof.
    unfold mut_subtype.
    iIntros "(%Ha & $)". iPureIntro.
    intros r.
    eapply subtype_trans; first apply Ha.
    apply type_fixpoint_subtype_2.
  Qed.
  Definition mut_subtype_fixpoint_r_inst := [instance @mut_subtype_fixpoint_r].
  Global Existing Instance mut_subtype_fixpoint_r_inst | 6.

  Lemma mut_eqtype_fixpoint_id E L  T :
    mut_eqtype E L (type_fixpoint F) (type_fixpoint F) T :-
    return T.
  Proof.
    unfold mut_eqtype.
    iIntros "$". iPureIntro.
    reflexivity.
  Qed.
  Definition mut_eqtype_fixpoint_id_inst := [instance @mut_eqtype_fixpoint_id].
  Global Existing Instance mut_eqtype_fixpoint_id_inst | 5.

  Lemma mut_eqtype_fixpoint_r (ty1 : type rt) E L  T :
    mut_eqtype E L ty1 (type_fixpoint F) T :-
    return (mut_eqtype E L ty1 (F (type_fixpoint F)) T).
  Proof.
    unfold mut_eqtype.
    iIntros "(%Ha & $)". iPureIntro.
    etrans; first apply Ha.
    split.
    - apply type_fixpoint_subtype_2.
    - apply type_fixpoint_subtype_1.
  Qed.
  Definition mut_eqtype_fixpoint_r_inst := [instance @mut_eqtype_fixpoint_r].
  Global Existing Instance mut_eqtype_fixpoint_r_inst | 6.
End rules.

Section fixpoint_uniqueness.
  Context `{!typeGS Σ}.

  Lemma type_dist_full_eqtype E L {rt} (ty1 ty2 : type rt) :
    (∀ n, TypeDist n ty1 ty2) →
    full_eqtype E L ty1 ty2.
  Proof.
    intros Hdist r. apply eqtype_unfold.
    iIntros (qL) "_ _".
    iSplitR.
    { iPureIntro. intros m. destruct (Hdist 0). by apply type_dist_st. }
    iSplit; last iSplit.
    - iModIntro. iSplit; iIntros "Hsc".
      + destruct (Hdist 0). rewrite type_dist_sc. done.
      + destruct (Hdist 0). rewrite type_dist_sc. done.
    - iModIntro. iIntros (π m v). iSplit; iIntros "Hown".
      + assert ((v ◁ᵥ{π, m} r @ ty1)%I ≡ (v ◁ᵥ{π, m} r @ ty2)%I) as Heq.
        { apply equiv_dist => n. destruct (Hdist n). by apply type_dist_own_val. }
        rewrite Heq. done.
      + assert ((v ◁ᵥ{π, m} r @ ty1)%I ≡ (v ◁ᵥ{π, m} r @ ty2)%I) as Heq.
        { apply equiv_dist => n. destruct (Hdist n). by apply type_dist_own_val. }
        rewrite Heq. done.
    - iModIntro. iIntros (κ π m l). iSplit; iIntros "Hshr".
      + assert ((l ◁ₗ{π, m, κ} r @ ty1)%I ≡ (l ◁ₗ{π, m, κ} r @ ty2)%I) as Heq.
        { apply equiv_dist => n. destruct (Hdist n). by apply type_dist_shr. }
        rewrite Heq. done.
      + assert ((l ◁ₗ{π, m, κ} r @ ty1)%I ≡ (l ◁ₗ{π, m, κ} r @ ty2)%I) as Heq.
        { apply equiv_dist => n. destruct (Hdist n). by apply type_dist_shr. }
        rewrite Heq. done.
  Qed.

  Context {rt : RT} `{!Inhabited (RT_xt rt)} (F : type rt → type rt) `{!TypeContractive F}.

  Lemma type_fixpoint_unique_dist (ty : type rt) :
    (∀ n, TypeDist n ty (F ty)) →
    ∀ n, TypeDist n ty (type_fixpoint F).
  Proof.
    intros Hfix.
    assert (Hst : ∀ m, ty_syn_type ty m = ty_syn_type (type_fixpoint F) m).
    { intros m. rewrite type_fixpoint_syn_type.
      destruct (Hfix 0) as [Hst0 _ _ _].
      etrans; first apply Hst0.
      unfold Fn. simpl.
      apply type_ctr_syn_type. }
    assert (Hsc : ty_sidecond ty ≡ ty_sidecond (type_fixpoint F)).
    { rewrite type_fixpoint_sidecond.
      destruct (Hfix 0) as [_ Hsc0 _ _].
      etrans; first apply Hsc0.
      unfold Fn. simpl.
      eapply type_ctr_sidecond.
      intros m. rewrite -type_fixpoint_syn_type. apply Hst. }
    induction n as [|n IH].
    { assert (Hshr0 : ∀ κ π r m l,
        (l ◁ₗ{π, m, κ} r @ ty ≡{0}≡ l ◁ₗ{π, m, κ} r @ type_fixpoint F)%I).
      { intros κ π r m l.
        destruct (Hfix 0) as [_ _ _ Hfix_shr].
        etrans; first apply Hfix_shr.
        etrans.
        { eapply type_ctr_shr. constructor; [done | done | | ].
          - intros π' r' m' v'. dist_later_2_intro. lia.
          - intros κ' π' r' m' l'. dist_later_intro. unfold_sidx. lia. }
        rewrite -type_fixpoint_shr_unfold. done. }
      constructor; [done | done | | done].
      intros π r m v.
      destruct (Hfix 0) as [_ _ Hfix_own _].
      etrans; first apply Hfix_own.
      etrans.
      { eapply type_ctr_own_val. constructor; [done | done | | done].
        intros π' r' m' v'. dist_later_intro. unfold_sidx. lia. }
      rewrite -type_fixpoint_own_val_unfold. done. }
    assert (HshrS : ∀ κ π r m l,
      (l ◁ₗ{π, m, κ} r @ ty ≡{S n}≡ l ◁ₗ{π, m, κ} r @ type_fixpoint F)%I).
    { intros κ π r m l.
      destruct (Hfix (S n)) as [_ _ _ Hfix_shr].
      etrans; first apply Hfix_shr.
      etrans.
      { eapply type_ctr_shr. constructor; [done | done | | ].
        - intros π' r' m' v'. dist_later_2_intro.
          destruct IH as [_ _ Hown_n _].
          eapply dist_le; first apply Hown_n. lia.
        - intros κ' π' r' m' l'. dist_later_intro.
          destruct IH as [_ _ _ Hshr_n].
          eapply dist_le; first apply Hshr_n. unfold_sidx. lia. }
      rewrite -type_fixpoint_shr_unfold. done. }
    constructor; [done | done | | done].
    intros π r m v.
    destruct (Hfix (S n)) as [_ _ Hfix_own _].
    etrans; first apply Hfix_own.
    etrans.
    { eapply type_ctr_own_val. constructor; [done | done | | done].
      intros π' r' m' v'. dist_later_intro.
      destruct IH as [_ _ Hown_n _].
      eapply dist_le; first apply Hown_n. unfold_sidx. lia. }
    rewrite -type_fixpoint_own_val_unfold. done.
  Qed.

  Lemma type_fixpoint_unique_eqtype_dist E L (ty : type rt) :
    (∀ n, TypeDist n ty (F ty)) →
    full_eqtype E L ty (type_fixpoint F).
  Proof.
    intros Hdist. eapply type_dist_full_eqtype.
    apply type_fixpoint_unique_dist. done.
  Qed.

  Lemma type_fixpoint_unique_eqtype E L (ty : type rt) :
    ty ≡ F ty →
    full_eqtype E L ty (type_fixpoint F).
  Proof.
    intros Heq. eapply type_fixpoint_unique_eqtype_dist.
    intros n. destruct Heq as [_ _ Hown Hshr _ Hst Hsc _ _].
    constructor; [done | done | | ]; intros; apply equiv_dist; [apply Hown | apply Hshr].
  Qed.
End fixpoint_uniqueness.
