From refinedrust Require Export type ltypes programs.
From refinedrust Require Import uninit int ltype_rules.
From refinedrust Require Import options.

(** * Existential types and invariants *)

(** ** Existential types with "simple" invariants that are tacked on via a separating conjunction *)
(* Note: this does not allow for, e.g., Cell or Mutex -- we will need a different version using non-atomic/atomic invariants for those *)
(*
  [X] is the inner refinement type,
  [Y] is the type it is being abstracted to.
*)
Record ex_inv_def `{!typeGS Σ} (X : RT) (Y : RT) : Type := mk_ex_inv_def' {
  inv_xr_inh : Inhabited (RT_xt Y);

  inv_P : thread_id → X → Y → iProp Σ;
  inv_P_shr : thread_id → lft → X → Y → iProp Σ;

  (* extra requirements on E and lfts, e.g. in case that P asserts extra location ownership *)
  inv_P_lfts : list lft;
  inv_P_wf_E : elctx;

  inv_P_shr_pers : ∀ π κ x y, Persistent (inv_P_shr π κ x y);
  inv_P_shr_mono : ∀ π κ κ' x y, κ' ⊑ κ -∗ inv_P_shr π κ x y -∗ inv_P_shr π κ' x y;
  inv_P_share :
    ∀ F π κ x y q,
    lftE ⊆ F →
    rrust_ctx -∗
    let κ' := lft_intersect_list inv_P_lfts in
    q.[κ ⊓ κ'] -∗
    &{κ} (inv_P π x y) -∗
    logical_step F (inv_P_shr π κ x y ∗ q.[κ ⊓ κ']);
}.
(* Stop Typeclass resolution for the [inv_P_shr_pers] argument, to make it more deterministic. *)
Definition mk_ex_inv_def `{!typeGS Σ} {X Y : RT} `{!Inhabited (RT_xt Y)}
  (inv_P : thread_id → X → Y → iProp Σ)
  (inv_P_shr : thread_id → lft → X → Y → iProp Σ)
  inv_P_lfts
  (inv_P_wf_E : elctx)
  (inv_P_shr_pers : TCNoResolve (∀ (π : thread_id) (κ : lft) (x : X) (y : Y), Persistent (inv_P_shr π κ x y)))
  inv_P_shr_mono
  inv_P_share := mk_ex_inv_def' _ _ _ _ _ inv_P inv_P_shr inv_P_lfts inv_P_wf_E inv_P_shr_pers inv_P_shr_mono inv_P_share.
Global Arguments inv_P {_ _ _ _ _}.
Global Arguments inv_P_shr {_ _ _ _ _}.
Global Arguments inv_P_lfts {_ _ _ _ _}.
Global Arguments inv_P_wf_E {_ _ _ _ _}.
Global Arguments inv_P_share {_ _ _ _ _}.
Global Arguments inv_P_shr_mono {_ _ _ _ _}.
Global Arguments inv_P_shr_pers {_ _ _ _ _}.
Global Existing Instance inv_P_shr_pers.

(** Smart constructor for persistent and timeless [P] *)
Program Definition mk_pers_ex_inv_def `{!typeGS Σ} {X : RT} {Y : RT} `{!Inhabited (RT_xt Y)} (P : X → Y → iProp Σ)
  (_: TCNoResolve (∀ x y, Persistent (P x y))) (_: TCNoResolve (∀ x y, Timeless (P x y))) : ex_inv_def X Y :=
  mk_ex_inv_def (λ _, P) (λ _ _, P) [] [] _ _ _.
Next Obligation.
  rewrite /TCNoResolve.
  eauto with iFrame.
Qed.
Next Obligation.
  rewrite /TCNoResolve. eauto with iFrame.
Qed.
Next Obligation.
  rewrite /TCNoResolve.
  iIntros (????? P ?? F ? κ x y q ?) "#CTX Htok Hb".
  iDestruct "CTX" as "(LFT & TIME & LLCTX)".
  iApply fupd_logical_step.
  rewrite right_id. iMod (bor_persistent with "LFT Hb Htok") as "(>HP & Htok)"; first done.
  iApply logical_step_intro. by iFrame.
Qed.



Class ExInvDefNonExpansive `{!typeGS Σ} {rt X Y : RT} (F : type rt → ex_inv_def X Y) : Type := {
  ex_inv_def_ne_lft_mor : DirectLftMorphism (λ ty, (F ty).(inv_P_lfts)) (λ ty, (F ty).(inv_P_wf_E));

  ex_inv_def_ne_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist n ty ty' →
      ∀ π x y,
        (F ty).(inv_P) π x y ≡{n}≡ (F ty').(inv_P) π x y;

  ex_inv_def_ne_shr :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π κ x y,
        (F ty).(inv_P_shr) π κ x y ≡{n}≡ (F ty').(inv_P_shr) π κ x y;
}.

Class ExInvDefContractive `{!typeGS Σ} {rt X Y : RT} (F : type rt → ex_inv_def X Y) : Type := {
  ex_inv_def_contr_lft_mor : DirectLftMorphism (λ ty, (F ty).(inv_P_lfts)) (λ ty, (F ty).(inv_P_wf_E));

  ex_inv_def_contr_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π x y,
        (F ty).(inv_P) π x y ≡{n}≡ (F ty').(inv_P) π x y;

  ex_inv_def_contr_shr :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDistLater2 n ty ty' →
      ∀ π κ x y,
        (F ty).(inv_P_shr) π κ x y ≡{n}≡ (F ty').(inv_P_shr) π κ x y;
}.

Section insts.
  Context `{!typeGS Σ}.

  Global Instance ex_inv_def_contractive_const {rt X Y} (v : ex_inv_def X Y) :
    ExInvDefContractive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
    - eauto.
  Qed.

  Global Instance ex_inv_def_ne_const {rt X Y} (v : ex_inv_def X Y) :
    ExInvDefNonExpansive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
    - eauto.
  Qed.

  (* TODO: instance for showing non-expansiveness from contractiveness *)

End insts.

Section ex.
  Context `{!typeGS Σ}.
  (* [Y] is the abstract refinement type, [X] is the inner refinement type *)
  Context (X Y : RT)
    (* invariant on the contained refinement *)
    (P : ex_inv_def X Y)
  .

  (** Provide an abstraction over [ty], by accepting a refinement [Y] and existentially quantifying over [X].
     [P] is a predicate specifying an invariant, potentially containing additional ownership.
     [R] determines a relation between the inner and outer refinement. *)
  Program Definition ex_plain_t (ty : type X) : type Y := {|
    ty_xt_inhabited := _;
    ty_own_val π r v :=
      (∃ x : X, P.(inv_P) π x r ∗ ty.(ty_own_val) π x v)%I;
    ty_shr κ π r l :=
      (∃ x : X, P.(inv_P_shr) π κ x r ∗ ty.(ty_shr) κ π x l)%I;
    ty_syn_type := ty.(ty_syn_type);
    _ty_has_op_type ot mt := ty_has_op_type ty ot mt;
    ty_sidecond :=
    ty.(ty_sidecond);
    _ty_lfts := P.(inv_P_lfts) ++ ty_lfts ty;
    _ty_wf_E := P.(inv_P_wf_E) ++ ty_wf_E ty;
  |}.
  Next Obligation.
    intros. apply P.
  Qed.
  Next Obligation.
    iIntros (ty π r v) "(%x & HP & Hv)".
    by iApply ty_has_layout.
  Qed.
  Next Obligation.
    iIntros (ty ot mt Hot). by eapply ty_op_type_stable.
  Qed.
  Next Obligation.
    iIntros (ty π r v) "(%x & HP & Hv)". by iApply ty_own_val_sidecond.
  Qed.
  Next Obligation.
    iIntros (ty ? π r v) "(%x & HP & Hs)". by iApply ty_shr_sidecond.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (ty κ π l r) "(%x & HP & Hv)". by iApply ty_shr_aligned.
  Qed.
  Next Obligation.
    iIntros (ty E κ l ly π r q ?) "#(LFT & TIME & LLCTX) Htok %Halg %Hly Hlb Hb".
    iApply fupd_logical_step.
    setoid_rewrite bi.sep_exist_l. setoid_rewrite bi_exist_comm.
    iDestruct "Htok" as "(Htok & Htok2)".
    rewrite lft_intersect_list_app.
    rewrite -{1}lft_tok_sep -{1}lft_tok_sep. iDestruct "Htok" as "(Htok & HtokP & Htoki)".
    rewrite lft_intersect_assoc. rewrite -lft_tok_sep. iDestruct "Htok2" as "(Htok2 & Htoki2)".
    iMod (bor_exists_tok with "LFT Hb Htok") as "(%x & Hb & Htok)"; first solve_ndisj.
    iPoseProof (bor_iff _ _ (P.(inv_P) π x r ∗ (∃ a : val, l ↦ a ∗ a ◁ᵥ{ π} x @ ty)) with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit; [iIntros "(% & ? & ? & ?)" | iIntros "(? & (% & ? & ?))"]; eauto with iFrame. }
    iMod (bor_sep with "LFT Hb") as "(HP & Hb)"; first solve_ndisj.
    iPoseProof (P.(inv_P_share) E with "[$LFT $TIME $LLCTX] Htok2 HP") as "HP"; first done.
    iCombine "Htok Htoki" as "Htok". rewrite lft_tok_sep.
    rewrite ty_lfts_unfold.
    iPoseProof (ty_share with "[$] Htok [//] [//] Hlb Hb") as "Hb"; first solve_ndisj.
    iModIntro. iApply (logical_step_compose with "HP"). iApply (logical_step_wand with "Hb").
    iIntros "(Hshr & Htok) (HP & Htok2)".
    iSplitL "HP Hshr". { eauto with iFrame. }
    iCombine "Htok2 Htoki2" as "Htok2". rewrite lft_tok_sep -lft_intersect_assoc.
    iCombine "Htok HtokP" as "Htok". rewrite lft_tok_sep -lft_intersect_assoc.
    rewrite [lft_intersect_list (_ty_lfts _ ty) ⊓ lft_intersect_list P.(inv_P_lfts)]lft_intersect_comm.
    iCombine "Htok Htok2" as "$".
  Qed.
  Next Obligation.
    iIntros (ty κ κ' π r l) "#Hincl (%x & HP & Hshr)".
    iExists x. iSplitL "HP".
    { by iApply P.(inv_P_shr_mono). }
    iApply (ty_shr_mono with "Hincl Hshr").
  Qed.
  Next Obligation.
    iIntros (ty ot mt st π r v Hot) "(%x & HP & Hv)".
    iPoseProof (ty_memcast_compat with "Hv") as "Hm"; first done.
    destruct mt; eauto with iFrame.
  Qed.
  Next Obligation.
    intros ty ly mt Hst. simpl.
    by apply ty_has_op_type_untyped.
  Qed.

  (* TODO generalize ghost_drop in the type def *)
  (* Instance has low priority to allow overrides *)
  Global Program Instance ex_plain_t_ghost_drop ty `{Hg : !TyGhostDrop ty} : TyGhostDrop (ex_plain_t ty) | 100 :=
    mk_ty_ghost_drop _ (λ π r, (∃ x, P.(inv_P) π x r ∗ ty_ghost_drop_for ty Hg π x)%I) _.
  Next Obligation.
    iIntros (ty Hg π r v F ?) "(%x & HP & Ha)".
    iPoseProof (ty_own_ghost_drop with "Ha") as "Ha"; first done.
    iApply (logical_step_compose with "Ha").
    iApply logical_step_intro.
    iIntros "Hdrop". eauto with iFrame.
  Qed.
End ex.

Section contr.
  Context `{!typeGS Σ}.

  Global Instance ex_inv_def_contractive {rt X Y : RT}
    (P : type rt → ex_inv_def X Y)
    (F : type rt → type X) :
    ExInvDefContractive P →
    TypeContractive F →
    TypeContractive (λ ty, ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - destruct HP as [Hlft _ _].
      destruct HF as [_ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. eapply HF.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' ?.
      intros ????. rewrite /ty_shr/=.
      do 3 f_equiv.
      { apply HP. done. }
      apply HF; done.
  Qed.
  (* This should also work if only one of them is actually using the recursive argument. The other argument is trivially contractive, as it is constant. *)

  Global Instance ex_inv_def_ne {rt X Y : RT}
    (P : type rt → ex_inv_def X Y)
    (F : type rt → type X)
    :
    ExInvDefNonExpansive P →
    TypeNonExpansive F →
    TypeNonExpansive (λ ty, ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - destruct HP as [Hlft _ _].
      destruct HF as [_ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. intros.
      eapply HF; first done.
      rewrite ty_has_op_type_unfold. done.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' ?.
      intros ????. rewrite /ty_shr/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
  Qed.
End contr.

Notation "'∃;' P ',' τ" := (ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section open.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : ex_inv_def rt X).

  Global Program Instance learn_from_hyp_val_ex_plain_t ty r :
    LearnFromHypVal (∃; P, ty) r :=
    {| learn_from_hyp_val_Q := ∃ π, boringly (∃ x : rt, P.(inv_P) π x r) |}.
  Next Obligation.
    rewrite /ty_own_val/=.
    iIntros (? r ?? v ?) "(%x & Hinv & Hv)".
    iPoseProof (boringly_intro with "Hinv") as "#Hinv'".
    iModIntro. iSplitL; first by eauto with iFrame.
    iExists π.
    iApply boringly_exists. eauto.
  Qed.

  Lemma ex_plain_t_open_owned F π (ty : type rt) wl l (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Owned wl] PlaceIn x @ (◁ (∃; P, ty)) ={F}=∗
    ∃ r : rt, P.(inv_P) π r x ∗
    l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty) ∗
    (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
      l ◁ₗ[π, Owned false] r' @ lt' -∗
      ⌜ltype_st lt' = ty_syn_type ty⌝ -∗
      l ◁ₗ[π, Owned wl] r' @
        (OpenedLtype lt' (◁ ty) (◁ ∃; P, ty)
          (λ (r : rt) (x : X), P.(inv_P) π r x)
          (λ r x, True)))%I.
  Proof.
    iIntros (?) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & %x' & Hrfn & Hb)".
    iMod (maybe_use_credit with "Hcred Hb") as "(Hcred & Hat & Hb)"; first done.
    iDestruct "Hb" as "(%v & Hl & %r & HP & Hv)".
    iDestruct "Hrfn" as "<-".
    iModIntro. iExists r. iFrame.
    iSplitL "Hl Hv".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iFrame "#%". iSplitR; first done.
      iExists r. iSplitR; first done. iModIntro. eauto with iFrame. }
    iIntros (rt' lt' r') "Hb %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iFrame. clear -Halg Hly.
    iApply (logical_step_intro_maybe with "Hat").
    iIntros "Hcred' !>".
    iIntros (r' r'' κs) "HP".
    iSplitR; first done.
    iIntros "Hdead Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & _ & _ & Hsc' & _ & _ & %r0 & -> & >Hb)".
    iDestruct "Hb" as "(%v' & Hl & Hv)".
    iMod ("HP" with "Hdead" ) as "HP".
    iModIntro.
    rewrite ltype_own_core_equiv. simp_ltypes.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. simpl. iFrame "#%". by iFrame.
  Qed.

  (* We open this into a ShadowedLtype for [Shared].
     In terms of ownership, this doesn't do anything interesting, because we are working with persistent sharing predicates.
     However, we basically "overrride" the type at this place with [◁ ty], in order to not have to eliminate the existentials multiple times on subsequent accesses.
     This allows us to retain more information.

     This is not to be confused with "properly opening" the shared type, which we can only do for types with interior mutability.
  *)
  Lemma ex_plain_t_open_shared F π (ty : type rt) κ l (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] PlaceIn x @ (◁ (∃; P, ty)) ={F}=∗
    ∃ r : rt, P.(inv_P_shr) π κ r x ∗
    l ◁ₗ[π, Shared κ] PlaceIn x @ (ShadowedLtype (◁ ty) #r (◁ (∃; P, ty))).
  Proof.
    iIntros (?) "#Ha". iPoseProof "Ha" as "Hb".
    rewrite {2}ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & Hsc & Hlb & %r' & -> & #Hb)".
    iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done. iClear "Hb".
    iDestruct "Hb'" as "(%r & HP & Hb)".
    iModIntro. iExists r. iFrame "#".
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
    simp_ltypes. iSplitL; last done.
    iApply ltype_own_ofty_unfold. rewrite /lty_of_ty_own.
    iExists ly. iSplitR; first done. do 3 iR.
    iExists r. iSplitR; first done. iModIntro. done.
  Qed.

  Lemma ex_plain_t_open_uniq F π (ty : type rt) l (x : X) q κ γ κs :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ llft_elt_toks κs) -∗
    l ◁ₗ[π, Uniq κ γ] PlaceIn x @ (◁ (∃; P, ty)) ={F}=∗
    ∃ r : rt, P.(inv_P) π r x ∗
    l ◁ₗ[π, Owned false] PlaceIn r @ (◁ ty) ∗
    (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
      l ◁ₗ[π, Owned false] r' @ lt' -∗
      ⌜ltype_st lt' = ty_syn_type ty⌝ -∗
      l ◁ₗ[π, Uniq κ γ] r' @
      (OpenedLtype (lt') (◁ ty) (◁ ∃; P, ty)
        (λ (r : rt) (x : X), P.(inv_P) π r x)
        (λ r x, llft_elt_toks κs)))%I.
  Proof.
    (* TODO duplicated a lot with opened_ltype_create_uniq_simple, mostly due to the different invariant.
        Can we generalize? *)
    iIntros (?) "#(LFT & TIME & LLCTX) Htok Hcl_tok Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ' & #Hincl & Hb & ? & Hcl_b)"; first done.
    iMod "Hcl_F" as "_".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iDestruct "Hb" as "(%v & Hl & %r & HP & Hv)".
    iModIntro. iExists r. iFrame.
    iSplitL "Hl Hv".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iFrame "#%". iSplitR; first done.
      iExists r. iSplitR; first done. iModIntro. eauto with iFrame. }
    iIntros (rt' lt' r') "Hb %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iFrame. clear -Hly Halg.
    iApply (logical_step_intro_atime with "Hat").
    iIntros "Hcred' Hat". iModIntro.
    iIntros (own_lt_cur' κs' r0 r') "HP #Hincl' Hown #Hub".
    rewrite ltype_own_core_equiv. simp_ltypes.
    (* update *)
    iMod (gvar_update r' with "Hauth Hrfn") as "(Hauth & $)".

    iAssert (□ ([† κ] ={lftE}=∗ lft_dead_list κs'))%I as "#Hkill".
    { iModIntro. iIntros "#Hdead".
      iApply big_sepL_fupd. iApply big_sepL_intro. iIntros "!>" (?? Hlook).
      iPoseProof (big_sepL_lookup with "Hincl'") as "Ha"; first done.
      iApply (lft_incl_dead with "[] Hdead"); first done.
      done. }
      (*iApply lft_incl_trans; done. }*)

    (* close the borrow *)
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    set (V := (gvar_auth γ r' ∗ (lft_dead_list κs' ={lftE}=∗ P.(inv_P) π r0 r') ∗ own_lt_cur' π r0 l)%I).
    iMod ("Hcl_b" $! V with "[] Hcred1 [HP Hown Hauth ]") as "(Hb & Htok)".
    { iNext. iIntros "(Hauth & HP & Hb) Hdead".
      iModIntro. iNext. iExists r'. iFrame.
      iMod (lft_incl_dead _ κ with "[] Hdead") as "#Hdead"; [done.. | ].
      iMod ("Hkill" with "Hdead") as "#Hdead'".
      iMod ("HP" with "Hdead'") as "HP".
      iMod ("Hub" with "Hdead' Hb") as "Hown".
      rewrite {2}ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hown" as "(% &_ & _ & _ & _ & _ & %r1 & -> & >(%v1 & Hl & Hv))".
      iModIntro. iFrame. }
    { iNext. rewrite /V. iFrame. }
    iMod ("Hcl_tok" with "Htok") as "$".

    (* show that we can shift it back *)
    iModIntro. iIntros "#Hdead Hobs". iModIntro.
    rewrite ltype_own_core_equiv. simp_ltypes.
    rewrite (ltype_own_ofty_unfold _ (Uniq _ _)) /lty_of_ty_own.
    iExists ly. iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iModIntro.
    iApply (pinned_bor_shorten with "Hincl").
    iApply (pinned_bor_impl with "[] Hb").
    iNext. iModIntro. iSplit; first last. { eauto. }
    iIntros "(Hauth & HP & Hcur)".
    iExists r'. iFrame. iMod ("Hub" with "Hdead Hcur") as "Hb".
    iClear "Hub". rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(% & _ & _ & _ & _ & _ & Hb)".
    iDestruct "Hb" as "(%r1 & -> & >(%v1 & Hl & Hv1))".
    iMod ("HP" with "Hdead") as "HP".
    iModIntro. iFrame.
  Qed.
End open.

Section subtype.
  Context `{!typeGS Σ}.
  Context {rt X : RT}.
  Lemma weak_subtype_ex_plain_t E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) (r1 r2 : X) T :
    ⌜r1 = r2⌝ ∗ ⌜ty1 = ty2⌝ ∗ ⌜P1 = P2⌝ ∗ T
    ⊢ weak_subtype E L r1 r2 (∃; P1, ty1) (∃; P2, ty2) T.
  Proof.
    iIntros "(-> & -> & -> & HT)".
    iIntros (? ?) "#CTX #HE HL".
    iFrame. iApply type_incl_refl.
  Qed.
  Global Instance weak_subtype_ex_plain_t_inst E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) (r1 r2 : X) :
    Subtype E L r1 r2 (∃; P1, ty1) (∃; P2, ty2) := λ T, i2p (weak_subtype_ex_plain_t E L P1 P2 ty1 ty2 r1 r2 T).
  Lemma mut_subtype_ex_plain_t E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) T :
    ⌜P1 = P2⌝ ∗ ⌜ty1 = ty2⌝ ∗ T
    ⊢ mut_subtype E L (∃; P1, ty1) (∃; P2, ty2) T.
  Proof.
    iIntros "(-> & -> & HT)". iFrame. iPureIntro. intros ?. apply subtype_refl.
  Qed.
  Global Instance mut_subtype_ex_plain_t_inst E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) :
    MutSubtype E L (∃; P1, ty1) (∃; P2, ty2) := λ T, i2p (mut_subtype_ex_plain_t E L P1 P2 ty1 ty2 T).

  Lemma mut_eqtype_ex_plain_t E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) T :
    ⌜P1 = P2⌝ ∗ ⌜ty1 = ty2⌝ ∗ T ⊢ mut_eqtype E L (∃; P1, ty1) (∃; P2, ty2) T.
  Proof.
    iIntros "(-> & -> & HT)". iFrame. iPureIntro. intros ?. apply eqtype_refl.
  Qed.
  Global Instance mut_eqtype_ex_plain_t_inst E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) :
    MutEqtype E L (∃; P1, ty1) (∃; P2, ty2) := λ T, i2p (mut_eqtype_ex_plain_t E L P1 P2 ty1 ty2 T).
End subtype.

Section stratify.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : ex_inv_def rt X).

  (** Subsumption rule for introducing an existential *)
  (* TODO could have a more specific instance for persistent invariants with pers = true *)
  Lemma owned_subtype_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (prove_with_subtype E L false ProveDirect (P.(inv_P) π r r') (λ L1 _ R, R -∗ T L1))
    ⊢ owned_subtype π E L false r r' ty (∃; P, ty) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iSplitR; last iSplitR.
    - simpl. iPureIntro.
      intros ly1 ly2 Hly1 HLy2. f_equiv. by eapply syn_type_has_layout_inj.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      eauto with iFrame.
  Qed.
  Global Instance owned_subtype_ex_plain_t_inst π E L (ty : type rt) (r : rt) (r' : X) :
    OwnedSubtype π E L false r r' ty (∃; P, ty) :=
    λ T, i2p (owned_subtype_ex_plain_t π E L ty r r' T).

  Lemma owned_subtype_ex_plain_t_strong {rt0 : RT} π E L (ty : type rt0) (ty2 : type rt) (r : rt0) (r' : X) T :
    (∃ r1, owned_subtype π E L false r r1 ty ty2 (λ L2, 
    (prove_with_subtype E L2 false ProveDirect (P.(inv_P) π r1 r') (λ L1 _ R, 
    R -∗ T L1))))
    ⊢ owned_subtype π E L false r r' ty (∃; P, ty2) T.
  Proof.
    iIntros "HT".
    unfold owned_subtype, prove_with_subtype.
    iIntros (????) "#CTX #HE HL".
    iDestruct "HT" as "(%r1 & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L0 & Hincl & HL & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iDestruct "Hincl" as "(%Hst_eq & Hsc & Hv)".
    iSplitR; last iSplitL "Hsc".
    - simpl. iPureIntro. done.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      iPoseProof ("Hv" with "Hv0") as "Hv".
      eauto with iFrame.
  Qed.
  Definition owned_subtype_ex_plain_t_strong_inst := [instance @owned_subtype_ex_plain_t_strong].
  Global Existing Instance owned_subtype_ex_plain_t_strong_inst.

  (*
  Lemma owned_subtype_unfold_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (∀ r2 : rt, introduce_with_hooks E L (P.(inv_P) π r2 r') (λ L1,
      owned_subtype π E L1 false r2 r ty ty T)) -∗
    owned_subtype π E L false r' r (∃; P, ty) ty T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL".

    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iSplitR; last iSplitR.
    - simpl. iPureIntro.
      intros ly1 ly2 Hly1 HLy2. f_equiv. by eapply syn_type_has_layout_inj.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      eauto with iFrame.
  Qed.
  Global Instance owned_subtype_ex_plain_t_inst π E L (ty : type rt) (r : rt) (r' : X) :
    OwnedSubtype π E L false r r' ty (∃; P, ty) :=
    λ T, i2p (owned_subtype_ex_plain_t π E L ty r r' T).
   *)



  (** Stratification rules *)

  (* Unfolding by stratification *)
  Lemma stratify_unfold_ex_plain_t_owned {M} π E L smu sa (sm : M) l (ty : type rt) x wl T :
    (∀ r, P.(inv_P) π r x -∗ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ ty) (#r) (Owned false)
      (λ L2 R' rt' lt' r',
        T L2 R' _ (OpenedLtype lt' (◁ ty) (◁ (∃; P, ty)) (λ (r : rt) (x : X), P.(inv_P) π r x) (λ r x, True)) r'))
    ⊢ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty)) (#x) (Owned wl) T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hb".
    iMod (ex_plain_t_open_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iMod ("HT" with "HP [//] [//] [//] CTX HE HL Hb") as "Ha".
    iDestruct "Ha" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
    iExists _, _, _, _, _. iFrame.
    iModIntro.
    iSplitR. { iPureIntro. simp_ltypes. rewrite -Hst. done. }
    iApply (logical_step_compose with "Hstep").
    iApply logical_step_intro. iIntros "(Hb & $)".
    iApply ("Hcl" with "Hb []").
    iPureIntro; done.
  Qed.
  (*Global Instance stratify_unfold_ex_plain_t_owned_inst {M} π E L smu sa (sm : M) l (ty : type rt) x wl :*)
  (*StratifyLtype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty))%I (PlaceIn x) (Owned wl) :=*)
    (*λ T, i2p (stratify_unfold_ex_plain_t_owned π E L smu sa sm l ty x wl T).*)

  Lemma stratify_unfold_ex_plain_t_uniq {M} π E L smu sa (sm : M) l (ty : type rt) x κ γ T :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L'),
    (∀ r, P.(inv_P) π r x -∗ stratify_ltype π E L' smu StratDoUnfold sa sm l (◁ ty) (PlaceIn r) (Owned false)
      (λ L2 R' rt' lt' r',
        T L2 R' _ (OpenedLtype lt' (◁ ty) (◁ (∃; P, ty)) (λ (r : rt) (x : X), P.(inv_P) π r x) (λ r x, llft_elt_toks κs)) r')))
    ⊢ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty)) (PlaceIn x) (Uniq κ γ) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal. iIntros "(%κs & %L' & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hb".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "Hcl_F" as "_".
    iMod (ex_plain_t_open_uniq with "CTX Htok Hcl_tok Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iMod ("HT" with "HP [//] [//] [//] CTX HE HL Hb") as "Ha".
    iDestruct "Ha" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
    iExists _, _, _, _, _. iFrame.
    iSplitR. { iPureIntro. simp_ltypes. done. }
    iModIntro.
    iApply (logical_step_compose with "Hstep").
    iApply logical_step_intro. iIntros "(Hb & $)".
    iApply ("Hcl" with "Hb []").
    done.
  Qed.
  (*Global Instance stratify_unfold_ex_plain_t_uniq_inst {M} π E L smu sa (sm : M) l (ty : type rt) x κ γ :*)
    (*StratifyLtype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty))%I (PlaceIn x) (Uniq κ γ) :=*)
    (*λ T, i2p (stratify_unfold_ex_plain_t_uniq π E L smu sa sm l ty x κ γ T).*)


  Lemma stratify_unfold_ex_plain_t_shared {M} π E L smu sa (sm : M) l (ty : type rt) x κ T :
    (∀ r, P.(inv_P_shr) π κ r x -∗ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ ty) (PlaceIn r) (Shared κ)
      (λ L2 R' rt' lt' r',
        ∃ r'', ⌜r' = PlaceIn r''⌝ ∗ T L2 R' _ (ShadowedLtype lt' #r'' (◁ (∃; P, ty))) (PlaceIn x)))
    ⊢ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty)) (PlaceIn x) (Shared κ) T.
  Proof.
    iIntros "HT" (F ???) "#CTX #HE HL Hb".
    iMod (ex_plain_t_open_shared with "Hb") as "(%r & HP & Hb)"; first done.
    iPoseProof (shadowed_ltype_acc_cur with "Hb") as "(Hb & Hcl_b)".
    iMod ("HT" with "HP [//] [//] [//] CTX HE HL Hb") as (L2 R' rt' lt' r') "(HL & Hst & Hstep & HT)".
    iDestruct "HT" as "(%r'' & -> & HT)".
    iModIntro. iExists  _, _, _, _, _. iFrame.
    simp_ltypes. iSplitR; first done.
    iApply (logical_step_wand with "Hstep"). iIntros "(Ha & $)".
    iApply ("Hcl_b" with "Hst Ha").
  Qed.
  (*Global Instance stratify_unfold_ex_plain_t_shared_inst {M} π E L smu sa (sm : M) l (ty : type rt) x κ :*)
    (*StratifyLtype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty))%I (PlaceIn x) (Shared κ) :=*)
    (*λ T, i2p (stratify_unfold_ex_plain_t_shared π E L smu sa sm l ty x κ T).*)

  (** Unfolding by place access *)
  Lemma typed_place_ex_plain_t_owned π E L l (ty : type rt) x wl K `{!TCDone (K ≠ [])} T :
    (∀ r, 
      introduce_with_hooks E L (P.(inv_P) π r x) (λ L2, typed_place π E L2 l
      (OpenedLtype (◁ ty) (◁ ty) (◁ (∃; P, ty)) (λ (r : rt) (x : X), P.(inv_P) π r x) (λ r x, True)) (#r) UpdStrong (Owned wl) K
      (λ L2 κs li b2 bmin' rti ltyi ri updcx,
        T L2 κs li b2 bmin' rti ltyi ri 
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I))))))
    ⊢ typed_place π E L l (◁ (∃; P, ty))%I (#x) UpdStrong (Owned wl) K T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (ex_plain_t_open_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
    iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hb").
    iModIntro. iIntros (L' κs l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hc" with "HL Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_ex_plain_t_owned_inst := [instance @typed_place_ex_plain_t_owned].
  Global Existing Instance typed_place_ex_plain_t_owned_inst | 15.

  Lemma typed_place_ex_plain_t_uniq π E L l (ty : type rt) x κ γ K `{!TCDone (K ≠ [])} T :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    (∀ r, introduce_with_hooks E L2 (P.(inv_P) π r x) (λ L3, typed_place π E L3 l
      (OpenedLtype (◁ ty) (◁ ty) (◁ (∃; P, ty)) (λ (r : rt) (x : X), P.(inv_P) π r x) (λ r x, llft_elt_toks κs)) (#r) UpdStrong (Uniq κ γ) K
      (λ L4 κs li b2 bmin' rti ltyi ri updcx,
        T L4 κs li b2 bmin' rti ltyi ri 
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I)))
        ))))
    ⊢ typed_place π E L l (◁ (∃; P, ty))%I (#x) UpdStrong (Uniq κ γ) K T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hb Hcont".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "HT" as "(%κs & %L' & %Hal & HT)".
    iApply fupd_place_to_wp.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "Hcl_F" as "_".
    iMod (ex_plain_t_open_uniq with "CTX Htok Hcl_tok Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
    iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hb").
    iModIntro. iIntros (L'' κs' l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hc" with "HL Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_ex_plain_t_uniq_inst := [instance @typed_place_ex_plain_t_uniq].
  Global Existing Instance typed_place_ex_plain_t_uniq_inst | 15.

  Lemma typed_place_ex_plain_t_shared π E L l (ty : type rt) x κ K `{!TCDone (K ≠ [])} T :
    (∀ r, introduce_with_hooks E L (P.(inv_P_shr) π κ r x) (λ L2, 
      typed_place π E L2 l (ShadowedLtype (◁ ty) #r (◁ (∃; P, ty))) (#x) UpdStrong (Shared κ) K
        (λ L3 κs li b2 bmin' rti ltyi ri updcx,
          T L3 κs li b2 bmin' rti ltyi ri 
            (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I)))
          )))
    ⊢ typed_place π E L l (◁ (∃; P, ty))%I (#x) UpdStrong (Shared κ) K T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (ex_plain_t_open_shared with "Hb") as "(%r & HP & Hb)"; first done.
    iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hb").
    iModIntro. iIntros (L'' κs' l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hc" with "HL Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_ex_plain_t_shared_inst := [instance @typed_place_ex_plain_t_shared].
  Global Existing Instance typed_place_ex_plain_t_shared_inst | 15.

End stratify.

(* TODO move *)
(* ty_share *)
Lemma ltype_own_ofty_share `{!typeGS Σ} π F κ q l {rt} (ty : type rt) r :
  lftE ⊆ F →
  rrust_ctx -∗
  let κ' := lft_intersect_list (ty_lfts ty) in
  q.[κ ⊓ κ'] -∗
  (&{κ} (l ◁ₗ[π, Owned true] r @ ◁ ty)) -∗
  logical_step F ((l ◁ₗ[π, Shared κ] r @ ◁ ty) ∗ q.[κ ⊓ κ']).
Proof.
  iIntros (?) "#(LFT & TIME & LLCTX) Htok Hl".
  iApply fupd_logical_step.
  iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
  rewrite -lft_tok_sep.
  iDestruct "Htok" as "(Htok & Htok2)".
  iMod (bor_exists_tok with "LFT Hl Htok") as "(%ly & Hl & Htok)"; first done.
  iMod (bor_sep with "LFT Hl") as "(Hst & Hl)"; first done.
  iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst & Htok)"; first done.
  iMod (bor_sep with "LFT Hl") as "(Hly & Hl)"; first done.
  iMod (bor_persistent with "LFT Hly Htok") as "(>%Hly & Htok)"; first done.
  iMod (bor_sep with "LFT Hl") as "(Hsc & Hl)"; first done.
  iMod (bor_persistent with "LFT Hsc Htok") as "(>#Hsc & Htok)"; first done.
  iMod (bor_sep with "LFT Hl") as "(Hlb & Hl)"; first done.
  iMod (bor_persistent with "LFT Hlb Htok") as "(>#Hlb & Htok)"; first done.
  iMod (bor_sep with "LFT Hl") as "(Hcred & Hl)"; first done.
  iMod (bor_exists_tok with "LFT Hl Htok") as "(%r' & Hl & Htok)"; first done.
  iMod (bor_sep with "LFT Hl") as "(Hrfn & Hl)"; first done.

  iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok") as "(Hrfn & Htok)"; first done.
  iDestruct "Htok" as "(Htok & Htok1)".
  iMod (bor_acc with "LFT Hcred Htok1") as "(>Hcred & Hcl_cred)"; first done.
  iDestruct "Hcred" as "(Hcred & Hat)".
  iDestruct "Hcred" as "(Hcred1 & Hcred)".
  iMod (bor_later with "LFT Hl") as "Hl"; first done.
  iApply (lc_fupd_add_later with "Hcred1"). iNext. iMod "Hl" as "Hl".
  iMod (bor_fupd_later with "LFT Hl Htok") as "Ha"; [done.. | ].
  iDestruct "Hcred" as "(Hcred1 & Hcred)".
  iApply (lc_fupd_add_later with "Hcred1"). iNext. iMod "Ha" as "(Hl & Htok)".
  iDestruct "Htok2" as "(Htok2 & Htok2')".
  iPoseProof (ty_share _ F with "[$LFT $TIME $LLCTX] [Htok Htok2] [//] [//] Hlb Hl") as "Hstep"; [done | ..].
  { rewrite ty_lfts_unfold. rewrite -lft_tok_sep. iFrame. }
  iApply logical_step_fupd.
  iApply (logical_step_compose with "Hstep").
  iApply (logical_step_intro_atime with "Hat").
  iModIntro. iIntros "Hcred' Hat".
  iModIntro. iIntros "(#Hshr & Htok)".
  iMod ("Hcl_cred" with "[$Hcred' $Hat]") as "(Hcred' & Htok1)".
  rewrite ty_lfts_unfold.
  iCombine "Htok1 Htok2'" as "Htok1".
  rewrite !lft_tok_sep. iFrame "Htok Htok1".
  iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own/=.
  iExists _. iR. iR. iR. iR.
  iExists _. iFrame. iModIntro. iModIntro. done.
Qed.

(* TODO : make lft_intersect_list simpl never in the lemmas using this. *)
Lemma ltype_own_ofty_share' `{!typeGS Σ} π F κ κ' q l {rt} (ty : type rt) r :
  lftE ⊆ F →
  (ty_lfts ty) ⊆ κ' →
  rrust_ctx -∗
  q.[κ] -∗
  q.[lft_intersect_list κ'] -∗
  (&{κ} (l ◁ₗ[π, Owned true] r @ ◁ ty)) -∗
  logical_step F ((l ◁ₗ[π, Shared κ] r @ ◁ ty) ∗ q.[κ] ∗ q.[lft_intersect_list κ']).
Proof.
  iIntros (? Hsub) "#CTX Htok1 Htok2 Hl".
  iApply fupd_logical_step.
  iMod (lft_incl_acc _ _ (lft_intersect_list (ty_lfts ty)) with "[] Htok2") as "(%q' & Htok2 & Hcltok2)"; first done.
  { iApply list_incl_lft_incl_list. done. }
  set (q0 := Qp.min q q').
  iPoseProof (Fractional_fractional_le (λ q, q.[κ])%I q q0 with "Htok1") as "[Htok1 Hcltok1]".
  { apply Qp.le_min_l. }
  iPoseProof (Fractional_fractional_le (λ q, q.[lft_intersect_list (ty_lfts ty)])%I q' q0 with "Htok2") as "[Htok2 Hcltok2']".
  { apply Qp.le_min_r. }
  iPoseProof (ltype_own_ofty_share with "CTX [Htok1 Htok2] Hl") as "Hstep"; first done.
  { rewrite -lft_tok_sep. iFrame. }
  iApply logical_step_fupd.
  iApply (logical_step_wand with "Hstep").
  rewrite -lft_tok_sep.
  iIntros "!> ($ & Htok1 & Htok2)".
  iPoseProof ("Hcltok1" with "Htok1") as "$".
  iPoseProof ("Hcltok2'" with "Htok2") as "Htok2".
  iMod ("Hcltok2" with "Htok2") as "$". done.
Qed.
Lemma ltype_own_ofty_share_tac `{!typeGS Σ} π F κ κ' q l {rt} (ty : type rt) r P :
  lftE ⊆ F →
  (ty_lfts ty) ⊆ κ' →
  rrust_ctx -∗
  q.[κ] -∗
  q.[lft_intersect_list κ'] -∗
  (&{κ} (l ◁ₗ[π, Owned true] r @ ◁ ty)) -∗
  ((q/2).[κ] -∗ (q/2).[lft_intersect_list κ'] -∗ logical_step F (((l ◁ₗ[π, Shared κ] r @ ◁ ty) ∗ (q/2).[κ] ∗ (q/2).[lft_intersect_list κ']) -∗ P)) -∗
  logical_step F P.
Proof.
  iIntros (??) "#CTX [Htok11 Htok12] [Htok21 Htok22] Hl Hstep".
  iPoseProof (ltype_own_ofty_share' with "CTX Htok11 Htok21 Hl") as "Hstep'"; [done.. | ].
  iApply (logical_step_compose with "(Hstep Htok12 Htok22)").
  iApply (logical_step_wand with "Hstep'").
  iIntros "Ha Hb". by iApply "Hb".
Qed.


