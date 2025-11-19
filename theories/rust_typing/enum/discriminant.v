From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype programs.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section discriminant.
  Context `{!typeGS Σ}.

  Program Definition enum_discriminant_t {rt} (en : enum rt) : type rt := {|
    st_own π r v :=
      ∃ tag, ⌜en.(enum_tag) r = Some tag⌝ ∗
      v ◁ᵥ{π} (els_lookup_tag en.(enum_els) tag) @ int en.(enum_els).(els_tag_it);
    st_has_op_type ot mt := is_int_ot ot en.(enum_els).(els_tag_it);
    st_syn_type := IntSynType en.(enum_els).(els_tag_it);
  |}%I.
  Next Obligation.
    intros. apply populate. apply (enum_xt_inhabited en).
  Qed.
  Next Obligation.
    simpl. intros.
    iIntros "(%tag & %Htag & Hv)".
    iApply (ty_has_layout with "Hv").
  Qed.
  Next Obligation.
    simpl. intros. eapply (@ty_op_type_stable _ _ _ (int _) _ mt).
    rewrite ty_has_op_type_unfold. done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. intros ???????? Hv. iIntros "(%tag & %Htag & Hv)".
    iPoseProof (ty_memcast_compat _ _ _ mt with "Hv") as "Ha".
    { rewrite ty_has_op_type_unfold. apply Hv. }
    destruct mt; eauto.
  Qed.
  Next Obligation.
    intros ?? mt ly Hst.
    apply syn_type_has_layout_int_inv in Hst as ->.
    done.
  Qed.

  Definition typed_discriminant_end_cont_t : Type :=
    llctx → val → ∀ (rt : RT), type rt → rt → iProp Σ.
  Definition typed_discriminant_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt: RT} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (els : enum_layout_spec) (T : typed_discriminant_end_cont_t) :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      (* given ownership of the read location *)
      l ◁ₗ[π, b2] r @ lt ={F}=∗
      ∃ q v discr,
        ⌜GetEnumDiscriminantLocSt l els `has_layout_loc` els.(els_tag_it)⌝ ∗
        ⌜v `has_layout_val` els.(els_tag_it)⌝ ∗
        (GetEnumDiscriminantLocSt l els) ↦{q} v ∗
        ▷ v ◁ᵥ{π} discr @ (int els.(els_tag_it)) ∗
        (* prove the continuation after the client is done *)
        logical_step F (
          (* assuming that the client provides the ownership back... *)
          (GetEnumDiscriminantLocSt l els) ↦{q} v ={F}=∗
          ∃ (L' : llctx) (rt3 : RT) (ty3 : type rt3) (r3 : rt3),
            v ◁ᵥ{ π} r3 @ ty3 ∗
            llctx_interp L' ∗
            l ◁ₗ[π, b2] r @ lt ∗
            T L' v rt3 ty3 r3))%I.
  Class TypedDiscriminantEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (els : enum_layout_spec) : Type :=
    typed_discriminant_end_proof T : iProp_to_Prop (typed_discriminant_end π E L l lt r b2 els T).

  Lemma typed_discriminant_end_enum_ltype π E L l {rt rte} (en : enum rt) tag (lte : ltype rte) (re : rte) r b2 els (T : typed_discriminant_end_cont_t) :
    typed_discriminant_end π E L l (EnumLtype en tag lte re) (#r) b2 els T :-
    exhale (⌜en.(enum_els) = els⌝);
    ∀ v,
    return (T L v rt  (enum_discriminant_t en) (r)).
  Proof.
  Admitted.
  Global Instance typed_discriminant_end_enum_ltype_inst π E L l {rt rte} (en : enum rt) tag (lte : ltype rte) (re : rte) r b2 els:
    TypedDiscriminantEnd π E L l (EnumLtype en tag lte re) (#r) b2 els :=
    λ T, i2p (typed_discriminant_end_enum_ltype π E L l en tag lte re r b2 els T).

  Lemma typed_discriminant_end_enum π E L l {rt} (en : enum rt) r b2 els (T : typed_discriminant_end_cont_t) :
    typed_discriminant_end π E L l (◁ enum_t en) (#r) b2 els T :-
    exhale (⌜en.(enum_els) = els⌝);
    ∀ v,
    return (T L v rt (enum_discriminant_t en) (r)).
  Proof.
  Admitted.
  Global Instance typed_discriminant_end_enum_inst π E L l {rt} (en : enum rt) r b2 els:
    TypedDiscriminantEnd π E L l (◁ enum_t en)%I (#r) b2 els :=
    λ T, i2p (typed_discriminant_end_enum π E L l en r b2 els T).

  Lemma type_discriminant E L e els T' (T : typed_read_cont_t) :
    IntoPlaceCtx E e T' →
    (** Decompose the expression *)
    T' L (λ L' K l,
      (** Find the type assignment *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      (** Check the place access *)
      typed_place π E L' l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto _ _),
        (** Stratify *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (** Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (** Finish reading *)
        typed_discriminant_end π E L2 l2 lt3 ri3 b2 els (λ L3 v rt3 ty3 r3,
        typed_place_finish π E L3 updcx upd (llft_elt_toks κs) l b lt3 ri3 (λ L4, T L4 π v _ (ty3) r3))
      )))))%I
    ⊢ typed_val_expr E L (EnumDiscriminant els e)%E T.
  Proof.
    (*iIntros "[% Hread]" (Φ) "#(LFT & TIME & LLCTX) #HE HL HΦ".*)
    (*wp_bind.*)
    (*iApply ("Hread" $! _ ⊤ with "[//] [//] [//] [//] [$TIME $LFT $LLCTX] HE HL").*)
    (*iIntros (l) "Hl".*)
    (*iApply ewp_fupd.*)
    (*rewrite /Use. wp_bind.*)
    (*iApply (wp_logical_step with "TIME Hl"); [solve_ndisj.. | ].*)
    (*iMod (persistent_time_receipt_0) as "#Hp".*)
    (*iMod (additive_time_receipt_0) as "Ha".*)
    (*iApply (wp_skip_credits with "TIME Ha Hp"); first done.*)
    (*iNext. iIntros "Hcred Hat".*)
    (*iIntros "(%v & %q & %π & %rt & %ty & %r & %Hlyv & %Hv & Hl & Hv & Hcl)".*)
    (*iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].*)
    (*iApply (wp_deref_credits with "TIME Hat Hp Hl") => //; try by eauto using val_to_of_loc.*)
    (*{ destruct o; naive_solver. }*)
    (*iIntros "!> %st Hl Hcred2 Hat Hcl".*)
    (*iMod ("Hcl" with "Hl Hv") as "(%L' & %rt' & %ty' & %r' & HL & Hv & HT)"; iModIntro.*)
    (*iDestruct "Hcred2" as "(Hcred1' & Hcred2)".*)
    (*iMod ("HT" with "[] HE HL [$Hat $Hcred2]") as "(%L3 & HL & HT)"; first done.*)
    (*by iApply ("HΦ" with "HL Hv HT").*)
  (*Qed.*)
  Admitted.

End discriminant.

Section switch.
  Context `{!typeGS Σ}.

  Inductive destruct_hint_switch_enum :=
  (* We did a case analysis *)
  | DestructHintSwitchEnumCase {rt} (r : rt) (n : string)
  (* The case was already known *)
  | DestructHintSwitchEnumKnown {rt} (r : rt) (n : string)
  .

  Lemma type_switch_enum π E L {rt} (en : enum rt) r (it : int_type) m ss def fn R ϝ v:
    ⌜it = en.(enum_els).(els_tag_it)⌝ ∗
    case_destruct r (λ c b,
      ∃ tag, ⌜enum_tag en c = Some tag⌝ ∗
        li_trace (if b then DestructHintSwitchEnumCase c tag else DestructHintSwitchEnumKnown c tag) (
        li_tactic (compute_map_lookup_goal (list_to_map (els_tag_int en.(enum_els))) tag false) (λ idx,
        li_tactic (compute_map_lookup_goal m (default 0%Z idx) false) (λ o,
        match o with
        | Some mi =>
           ∃ s, ⌜ss !! mi = Some s⌝ ∗ typed_stmt E L s fn R ϝ
        | None =>
          typed_stmt E L def fn R ϝ
        end))))
    ⊢ typed_switch π E L v _ (enum_discriminant_t en) r it m ss def fn R ϝ.
  Proof.
    unfold li_trace.
    iIntros "HT Hit". rewrite /ty_own_val/=.
    iDestruct "Hit" as "(%tag & %Htag & %Hv)".
    iDestruct "HT" as "(-> & Hc)".
    rewrite /compute_map_lookup_goal.
    iDestruct "Hc" as "(%b & %tag' & %Htag' & %idx & <- & %res & <- & Ha)".
    simplify_eq.
    iExists _. iR.
    unfold els_lookup_tag. done.
  Qed.
  Global Instance type_switch_enum_inst π E L {rt} (en : enum rt) r v it : TypedSwitch π E L v _ (enum_discriminant_t en) r it :=
    λ m ss def fn R ϝ, i2p (type_switch_enum π E L en r it m ss def fn R ϝ v).

End switch.
