From refinedrust Require Import type.
From iris.prelude Require Import options.

Section type_inh. 
  Context `{!typeGS Σ}.

  (* We need [Inhabited T_rt] because of [ty_rt_inhabited]. *)
  Context {T_rt : Type} `{!Inhabited T_rt}.

  Global Program Instance simple_type_inhabited : Inhabited (simple_type T_rt) := populate {|
      st_own π r v := ⌜v = []⌝%I;
      st_syn_type := UnitSynType;
      st_has_op_type ot _ := ot = UntypedOp unit_sl;
  |}.
  Next Obligation.
    simpl. 
    iIntros (??? ->).
    iExists unit_sl. iPureIntro. 
    split. 
    - by apply syn_type_has_layout_unit.
    - done.
  Qed.
  Next Obligation.
    simpl. intros ? ? ->. done.
  Qed.
  Next Obligation.
    simpl. intros ??? ??? ->.
    iIntros "->".
    destruct mt; simpl; iPureIntro; done.
  Qed.
  Global Instance type_inhabited : Inhabited (type T_rt) := populate (ty_of_st _ inhabitant).
End type_inh.

Section fixpoint_def.
  Context `{!typeGS Σ}.
  
  (* We assume a contractive functor *)
  Context {rt : Type} (F : type rt → type rt) `{Hcr : !TypeContractive F}.
  (* [rt] needs to be inhabited *)
  Context `{!Inhabited rt}.

  (* Iterate the functor [S n] times, starting with the inhabitant.
     We use at least one iteration, so that the [ty_syn_type] is always constant.
  *)
  Definition Fn n := Nat.iter (S n) F inhabitant. 

  Lemma Fn_syn_type_const n m : 
    ty_syn_type (Fn n) = ty_syn_type (Fn m).
  Proof using Hcr.
    unfold Fn. simpl. apply Hcr.
  Qed.
  Lemma Fn_sidecond_const n m : 
    ty_sidecond (Fn n) ≡ ty_sidecond (Fn m).
  Proof using Hcr.
    unfold Fn; simpl. eapply Hcr.
  Qed.

  Search logical_step.


  (* what can we prove about ghost_drop? *)
  (* TODO The problem: 
     I don't have laters over there. 
     With the current setup, I probably cannot prove that it's a fixpoint wrt ghost_drop 

     What do I expect the ghost_drop to be?

     Let's say I have a linked list defined via Box.
     I store mutable references in there.
     Now I drop the linked list.
     Ideally, I want a bigsep over all the observations.
     - i.e., the Box needs to pass through the inner ghost drop, with the respective smaller refinement.
      For this, I need to make this guarded over that also. 
     I guess in the end I get some laters. But I can also provide some later credits. 
     Ideally, logical_step would be contractive....
     But I guess it's not.

     I want amortized reasoning also at the logic level!! 

     Alternatively, I would define a version that has laters and provides a later credit, to make it guarded.
     Then I want to derive something on top that uses the logical step.

   *)

  Lemma Fn_lfts_const n m : 
    ty_lfts (Fn n) = ty_lfts (Fn m).
  Proof.
    (* TODO *)
    (*
       What can I do about this? 
       - we need a notion of lifetime equivalence that is okay with idempotence.
       - 



    *)


  Admitted.


  Lemma Fn_has_op_type_const n m ot mt :
    ty_has_op_type (Fn n) ot mt ↔ ty_has_op_type (Fn m) ot mt.
  Proof using Hcr.
    unfold Fn; simpl. eapply Hcr.
  Qed.

  Lemma Fn_succ n : 
    Fn (S n) = F (Fn n).
  Proof. done. Qed.

  (* We define a chain consisting of the ownership and sharing predicate and take the fixpoint over that. *)
  Definition ty_own_shrO : ofe := prodO (thread_id -d> rt -d> val -d> iPropO Σ) (lft -d> thread_id -d> rt -d> loc -d> iPropO Σ).

  (* We have the [2+] in order to fix up the [0] base case *)
  Lemma ty_own_shr_cauchy (i n : nat) : 
    n ≤ i →
    (∀ π r v, dist_later n (v ◁ᵥ{π} r @ (Fn (2+i)))%I (v ◁ᵥ{π} r @ (Fn (2+n)))%I) ∧
    (∀ κ π r l, (l ◁ₗ{π, κ} r @ (Fn (2+i)))%I ≡{n}≡ (l ◁ₗ{π, κ} r @ (Fn (2+n)))%I).
  Proof using Hcr.
    induction n as [ | n IH] in i |-*; simpl; intros Hle.
    { split; first (intros; dist_later_intro; lia).
      intros. eapply Hcr.
      - eapply Hcr.
      - eapply Hcr.
      - intros. dist_later_2_intro; lia.
      - intros. dist_later_intro; lia.
    } 
    destruct i; first lia.
    destruct (IH i) as [Hown Hshr]; first lia.
    split.
    - intros. dist_later_intro.
      simpl. eapply Hcr.
      + eapply Hcr.
      + eapply Hcr.
      + intros. dist_later_intro.
        eapply dist_later_lt; [eapply Hown | ]. lia.
      + intros. eapply dist_le; first apply Hshr. lia.
    - intros. simpl. eapply Hcr.
      + eapply Hcr.
      + eapply Hcr.
      + intros. dist_later_2_intro. eapply dist_later_lt; first done. lia. 
      + intros. dist_later_intro. eapply dist_le; first apply Hshr. lia.
  Qed.

  (* [3+] because that's what we need to apply the above lemma proving that the chain is Cauchy *)
  Program Definition F_ty_own_val_ty_shr_chain : chain ty_own_shrO := {|
    chain_car n := ((Fn (3 + n)).(ty_own_val), (Fn (3+n)).(ty_shr))
  |}.
  Next Obligation.
    simpl. intros n i Hle.
    destruct (ty_own_shr_cauchy (S i) (S n)) as [Hown Hshr]; first lia.
    constructor; simpl.
    - intros ???. eapply dist_later_lt; first eapply Hown. lia.
    - intros ????. eapply dist_le; first eapply Hshr. lia.
  Qed.
  Definition F_ty_own_val_ty_shr_fixpoint : ty_own_shrO :=
    compl F_ty_own_val_ty_shr_chain.

  (* Now we are ready to define the fixpoint *)
  (* For the ownership and sharing predicate, we take the fixpoint found above. *)
  (* For the other components, we use the 0 base case (where the functor is applied at least once) in order to be able to show the unfolding equation later. *)
  Program Definition type_fixpoint : type rt := {|
    ty_rt_inhabited := _;
    ty_syn_type := (Fn 0).(ty_syn_type);
    _ty_has_op_type := (Fn 0).(_ty_has_op_type _);
    ty_own_val := F_ty_own_val_ty_shr_fixpoint.1;
    ty_shr := F_ty_own_val_ty_shr_fixpoint.2;
    ty_sidecond := (Fn 0).(ty_sidecond);
    ty_ghost_drop := (Fn 0).(ty_ghost_drop);
    ty_lfts := (Fn 0).(ty_lfts);
    ty_wf_E := (Fn 0).(ty_wf_E);
  |}.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
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
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?. 
      simpl. erewrite Fn_sidecond_const. eapply ty_own_val_sidecond.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?. 
      simpl. erewrite Fn_sidecond_const. eapply ty_shr_sidecond.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_Persistent.
      intros ? [] [] Heq. eapply Heq.
    - intros ?. 
      simpl. eapply ty_shr_persistent.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?. 
      simpl. erewrite Fn_syn_type_const. eapply ty_shr_aligned.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. do 8 f_equiv. 
      { do 2 f_equiv. apply Heq. }
      apply Heq.
    - intros ?. simpl. 
      erewrite Fn_syn_type_const. 
      erewrite Fn_lfts_const.
      eapply ty_share.
      done.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. do 2 f_equiv; eapply Heq.
    - intros ?. 
      simpl. eapply ty_shr_mono.
  Qed.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv. eapply Heq.
    - intros ?. simpl.

      (* TODO *)
  Admitted.
  Next Obligation.
    intros. unfold F_ty_own_val_ty_shr_fixpoint.
    eapply @limit_preserving.
    - eapply bi.limit_preserving_entails; first apply _.
      intros ? [] [] Heq. f_equiv; first eapply Heq.
      f_equiv. eapply Heq.
    - intros ?. 
      simpl. eapply _ty_memcast_compat.
      rewrite -ty_has_op_type_unfold.
      eapply Fn_has_op_type_const. by rewrite ty_has_op_type_unfold. 
  Qed.

  Lemma type_fixpoint_own_val_unfold_n n v π r : 
    (v ◁ᵥ{π} r @ type_fixpoint)%I ≡{n}≡ (v ◁ᵥ{π} r @ Fn (3+n))%I.
  Proof.
    rewrite {1}/ty_own_val/=/F_ty_own_val_ty_shr_fixpoint/=.
    etrans. { apply (conv_compl n _). }
    simpl. done.
  Qed.
  Lemma type_fixpoint_shr_unfold_n n l κ π r : 
    (l ◁ₗ{π, κ} r @ type_fixpoint)%I ≡{n}≡ (l ◁ₗ{π, κ} r @ Fn (3+n))%I.
  Proof.
    rewrite {1}/ty_shr/=/F_ty_own_val_ty_shr_fixpoint/=.
    etrans. { apply (conv_compl n _). }
    simpl. done.
  Qed.

  Lemma type_fixpoint_syn_type : 
    type_fixpoint.(ty_syn_type) = (Fn 0).(ty_syn_type).
  Proof. done. Qed.
  Lemma type_fixpoint_sidecond :
    type_fixpoint.(ty_sidecond) = (Fn 0).(ty_sidecond).
  Proof. done. Qed.

  Lemma type_fixpoint_own_val_unfold v π r : 
    (v ◁ᵥ{π} r @ type_fixpoint)%I ≡ (v ◁ᵥ{π} r @ F type_fixpoint)%I.
  Proof.
    apply equiv_dist => n. rewrite type_fixpoint_own_val_unfold_n.
    rewrite Fn_succ.
    eapply Hcr.
    - rewrite type_fixpoint_syn_type. erewrite Fn_syn_type_const; done.
    - rewrite type_fixpoint_sidecond. erewrite Fn_sidecond_const; done.
    - intros. dist_later_intro.
      rewrite type_fixpoint_own_val_unfold_n.
      eapply dist_later_lt.
      { eapply (ty_own_shr_cauchy n (S m)). lia. }
      lia.
    - intros.
      rewrite type_fixpoint_shr_unfold_n.
      etrans. 
      { symmetry. eapply (ty_own_shr_cauchy (S n) (n)). lia. }
      done.
  Qed.
  Lemma type_fixpoint_shr_unfold l π κ r : 
    (l ◁ₗ{π, κ} r @ type_fixpoint)%I ≡ (l ◁ₗ{π, κ} r @ F type_fixpoint)%I.
  Proof.
    apply equiv_dist => n. rewrite type_fixpoint_shr_unfold_n.
    rewrite Fn_succ.
    eapply Hcr.
    - rewrite type_fixpoint_syn_type. erewrite Fn_syn_type_const; done.
    - rewrite type_fixpoint_sidecond. erewrite Fn_sidecond_const; done.
    - intros. dist_later_2_intro.
      rewrite type_fixpoint_own_val_unfold_n.
      simpl. eapply dist_later_lt.
      { eapply (ty_own_shr_cauchy n). lia. }
      lia.
    - intros. dist_later_intro.
      rewrite type_fixpoint_shr_unfold_n.
      eapply dist_le.
      { eapply (ty_own_shr_cauchy n (S m) ). lia. }
      lia. 
  Qed.
  Lemma type_fixpoint_equiv : 
    type_fixpoint ≡ F type_fixpoint.
  Proof.
    (* The fixpoint operator does NOT preserve everything (e.g. the inhabitant),
       so this does not hold. *)
  Abort.

  Lemma type_fixpoint_ty_lfts : 
    type_fixpoint.(ty_lfts) = (Fn 0).(ty_lfts).
  Proof.
  Admitted.
  Lemma type_fixpoint_ty_wf_E : 
    type_fixpoint.(ty_wf_E) = (Fn 0).(ty_wf_E).
  Proof.
  Admitted.

  (*Lemma type_fixpoint_ghost_drop : *)
    (*type_fixpoint.(ty_ghost_drop) *)

End fixpoint_def.

Lemma type_fixpoint_ne `{!typeGS Σ} {rt} `{!Inhabited rt} (T1 T2 : type rt → type rt)
    `{!TypeContractive T1, !TypeContractive T2, !NonExpansive T2} n :
  (∀ t, T1 t ≡{n}≡ T2 t) → type_fixpoint T1 ≡{n}≡ type_fixpoint T2.
Proof. 
  intros Heq.
  constructor.
  - done.
  - simpl.
    destruct (Heq inhabitant) as [_ Hot].
    move: Hot. rewrite ty_has_op_type_unfold. done.
  - iIntros (???).
    rewrite !type_fixpoint_own_val_unfold_n.
    f_equiv. 
    generalize (3+n) as m.
    induction m as [ | m IH]; simpl.
    { apply Heq. }
    specialize (Heq (Fn T1 m)).
    setoid_rewrite Heq. 
    (* here we need that T2 is also non-expansive *)
    by rewrite IH.
  - iIntros (????). 
    rewrite !type_fixpoint_shr_unfold_n.
    f_equiv. 
    generalize (3+n) as m.
    induction m as [ | m IH]; simpl.
    { apply Heq. }
    specialize (Heq (Fn T1 m)).
    setoid_rewrite Heq. 
    (* here we need that T2 is also non-expansive *)
    by rewrite IH.
  - simpl. destruct (Heq inhabitant). done.
  - simpl. destruct (Heq inhabitant). done.
  - intros. simpl. destruct (Heq inhabitant). done.
  - intros. simpl. destruct (Heq inhabitant). done.
  - intros. simpl. destruct (Heq inhabitant). done.
Qed.

(* TODO: should we also have something that states that fixpoint is TypeNonExpansive / TypeContractive? *)
(*Lemma type_fixpoint_type_ne `{!typeGS Σ} {rt} `{!Inhabited rt} (T1 T2 : type rt → type rt)*)
    (*`{!TypeContractive T1, !TypeContractive T2, !NonExpansive T2} n :*)
  (*(∀ t, T1 t ≡{n}≡ T2 t) → TypeNonExpansive (λ type_fixpoint T1)*)

Section fixpoint.
  Context `{!typeGS Σ}.
  Context {rt} `{!Inhabited rt} (T : type rt → type rt) {HT: TypeContractive T}.

  Global Instance type_fixpoint_copy :
    (∀ `(!Copyable ty), Copyable (T ty)) → Copyable (type_fixpoint T).
  Proof.
    intros ?.
    (* the chain is copyable *)
    assert (∀ n, Copyable (Fn T n)). 
    { induction n as [ | n IH]; simpl; apply _. }
    constructor.
    - intros. rewrite /ty_own_val/= /F_ty_own_val_ty_shr_fixpoint/=.
      eapply @limit_preserving.
      { eapply bi.limit_preserving_Persistent. 
        intros n [][][Heq1 Heq2].
        simpl in *. apply Heq1. }
      apply _.
    - intros ? ? ? ? ? ? ? ? ? Hst. intros. 
      rewrite /ty_shr/ty_own_val/= /F_ty_own_val_ty_shr_fixpoint/=.
      eapply @limit_preserving.
      { eapply bi.limit_preserving_entails; first apply _. 
        intros n [][][Heq1 Heq2].
        repeat f_equiv; simpl; [apply Heq2 | apply Heq1]. }
      intros ?. 
      eapply copy_shr_acc; [done | | done].
      move: Hst. rewrite type_fixpoint_syn_type.  
      erewrite Fn_syn_type_const; done.
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
    iSplit; last iSplit; last iSplit.
    - iPureIntro. rewrite !type_fixpoint_syn_type. apply HT.
    - iModIntro. simpl. rewrite type_ctr_sidecond. eauto.
    - iModIntro. iIntros (π v). rewrite type_fixpoint_own_val_unfold. eauto.
    - iModIntro. iIntros (???). rewrite type_fixpoint_shr_unfold. eauto.
  Qed.
  Lemma type_fixpoint_incl_2 r : ⊢ type_incl r r (T (type_fixpoint T)) (type_fixpoint T).
  Proof. 
    iSplit; last iSplit; last iSplit.
    - iPureIntro. rewrite !type_fixpoint_syn_type. apply HT.
    - iModIntro. simpl. rewrite type_ctr_sidecond. eauto.
    - iModIntro. iIntros (π v). rewrite type_fixpoint_own_val_unfold. eauto.
    - iModIntro. iIntros (???). rewrite type_fixpoint_shr_unfold. eauto.
  Qed.

  Lemma type_fixpoint_subtype_1 E L r : subtype E L r r (type_fixpoint T) (T (type_fixpoint T)).
  Proof. 
    iIntros (?) "HL HE". iApply type_fixpoint_incl_1.
  Qed.
  Lemma type_fixpoint_subtype_2 E L r : subtype E L r r (T (type_fixpoint T)) (type_fixpoint T).
  Proof. 
    iIntros (?) "HL HE". iApply type_fixpoint_incl_2.
  Qed.

  Lemma type_fixpoint_unfold_eqtype E L r : eqtype E L r r (type_fixpoint T) (T (type_fixpoint T)).
  Proof. 
    split.
    - apply type_fixpoint_subtype_1.
    - apply type_fixpoint_subtype_2.
  Qed.

  (* TODO subtyping -- think of the right lemmas here *)
End fixpoint.
