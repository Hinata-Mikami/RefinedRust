From refinedrust Require Export type ltypes programs lftmor.
From refinedrust Require Import uninit.
From refinedrust Require Import options.

(** * A type modelled after Rust's MaybeUninit *)
(** We do not represent this directly with a union abstraction for simplicity, but rather directly define what the Rust memory representation of [MaybeUninit] is. *)

Section type.
  Context `{!typeGS Σ}.

  Definition maybe_uninit_own_val_def {rt} (T : type rt) π r m v : iProp Σ :=
    match r with
    | Some r' => ∃ r'', place_rfn_interp_owned r' r'' ∗ T.(ty_own_val) π r'' m v
    | None => (uninit (T.(ty_syn_type) m)).(ty_own_val) π () m v
    end%I.
  Definition maybe_uninit_own_val_aux : seal (@maybe_uninit_own_val_def).
  Proof. by eexists. Qed.
  Definition maybe_uninit_own_val := maybe_uninit_own_val_aux.(unseal).
  Definition maybe_uninit_own_val_unfold : @maybe_uninit_own_val = @maybe_uninit_own_val_def := maybe_uninit_own_val_aux.(seal_eq).

  (** We refine by [option (place_rfn rt)] in order to borrow the optional contents.
     Note that this really makes it isomorphic to [MaybeUninit<T>] in our model,
     which is a union and thus would also get the place wrapper. *)
  (* NOTE: ideally this should require `{TySized T}, but this doesn't work well for the current [TypeNonExpansive] setup.
    Probably we should have a [TypeSizedNonExpansive] or so.
  *)
  Program Definition maybe_uninit {rt} (T : type rt) : type (option (place_rfn rt)) := {|
    ty_metadata_kind := T.(ty_metadata_kind);
    ty_trivial_drop := T.(ty_trivial_drop);
    ty_own_val := @maybe_uninit_own_val rt T;
    ty_syn_type m := UntypedSynType ((T.(ty_syn_type) m));
    _ty_has_op_type ot :=
      ∃ ly,
      syn_type_has_layout (T.(ty_syn_type) MetaNone) ly ∧
      T.(ty_metadata_kind) = MetadataNone ∧
      ot_layout ot = ly ∧
      ot = UntypedOp ly;
    ty_shr κ π r m l :=
      match r with
      | Some r' => ∃ r'', place_rfn_interp_shared r' r'' ∗ T.(ty_shr) κ π r'' m l
      | None => (uninit (T.(ty_syn_type) m)).(ty_shr) κ π () m l
      end%I;
    _ty_ghost_drop π r :=
      match r with
      | None => True
      | Some r =>
          ∃ r', place_rfn_interp_owned r r' ∗ ty_ghost_drop T π r'
      end%I;
    ty_sidecond := True;
    _ty_lfts := ty_lfts T;
    _ty_wf_E := ty_wf_E T;
  |}.
  Next Obligation.
    iIntros (rt T π r m v) "Hv". destruct r as [r | ].
    - rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
      iDestruct "Hv" as "(%r'' & Hrfn & Hv)".
      iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst & %Hly)".
      iExists ly. iPureIntro. split; last done.
      by apply syn_type_has_layout_untyped.
    - rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
      iApply (ty_has_layout with "Hv").
  Qed.
  Next Obligation.
    simpl; iIntros (rt T ot Hmt Hot).
    destruct Hot as (ly & Hst & ? & Hly & ->).
    rewrite Hly.
    by apply syn_type_has_layout_untyped.
  Qed.
  Next Obligation.
    intros rt T ot (ly & Hst & ? & _ & ->). constructor.
  Qed.
  Next Obligation.
    iIntros (rt T π r m v) "_". done.
  Qed.
  Next Obligation.
    iIntros (rt T ? π r m v) "_". done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (rt T κ π l r m) "Hl". destruct r as [r | ].
    - iDestruct "Hl" as "(%r'' & Hrfn & Hl)". iPoseProof (ty_shr_aligned with "Hl") as "Ha".
      iDestruct "Ha" as "(%ly & %Hly & %Hst)". iExists _. iR.
      iPureIntro.
      by apply syn_type_has_layout_untyped.
    - iPoseProof (ty_shr_aligned with "Hl") as "Ha".
      done.
  Qed.
  Next Obligation.
    iIntros (rt T E κ l ly π [r | ] m ? ?) "#CTX #Hna Htok %Hst %Hly #Hlb Hb".
    -
      iAssert (&{κ} (∃ r', place_rfn_interp_owned r r' ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π, m} r' @ T))%I with "[Hb]" as "Hb".
      { iApply (bor_iff with "[] Hb"). iNext. iModIntro. iSplit.
        - iIntros "(%v & Hl & Hown)".
          rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
          iDestruct "Hown" as "(%r' & ? & ?)". eauto with iFrame.
        - iIntros "(%r' & ? & %v & ? & ?)".
          rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
          eauto with iFrame. }
      iDestruct "CTX" as "(LFT & LLCTX)".
      iApply fupd_logical_step.
      rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Hb & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine ("Htok1 Htok2") as "Htok". rewrite lft_tok_sep.
      rewrite ty_lfts_unfold.
      apply syn_type_has_layout_untyped_inv in Hst.
      iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna Htok [//] [//] Hlb Hb") as "Hstep"; first done.
      iApply (logical_step_wand with "Hstep").
      iIntros "!> (Hl & $)". eauto with iFrame.
    - rewrite -lft_tok_sep. iDestruct "Htok" as "[Htok1 Htok2]".
      (*iAssert (&{κ} (ty_sidecond T ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π} .@ uninit (ty_syn_type T)))%I with "[Hb]" as "Hb".*)
      (*{ iApply (bor_iff with "[] Hb"). iNext. iModIntro. iSplit.*)
        (*- iIntros "(%v & ? & ? & ?)". eauto with iFrame.*)
        (*- iIntros "($ & ?)". done. }*)
      (*iDestruct "CTX" as "(LFT & TIME & LLCTX)".*)
      (*iApply fupd_logical_step. iMod (bor_sep with "LFT Hb") as "(_ & Hb)"; first done.*)
      iEval (rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def) in "Hb".
      iPoseProof ((uninit _).(ty_share) with "CTX Hna [Htok1] [] [//] [//] Hb") as "Ha"; simpl; first done.
      { rewrite right_id. done. }
      { done. }
      iApply (logical_step_wand with "Ha"). iIntros "(? & Htok1)".
      rewrite right_id. iFrame.
  Qed.
  Next Obligation.
    iIntros (rt T κ κ' π r m l) "#Hincl Ha".
    destruct r as [r | ]; last by iApply ty_shr_mono.
    iDestruct "Ha" as "(%r'' & ? & Hv)".
    iExists _. iFrame. by iApply ty_shr_mono.
  Qed.
  Next Obligation.
    iIntros (rt ty π r m v F ? Ht) "Hv".
    rewrite /ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    destruct r as [r' | ]; first last.
    { by iApply logical_step_intro. }
    iDestruct "Hv" as "(%r'' & Hinterp & Hv)".
    iApply (logical_step_wand with "[Hv]").
    { iApply (ty_own_ghost_drop_trivial with "Hv"); done. }
    iIntros "Ha".
    iExists _. iFrame.
  Qed.
  Next Obligation.
    iIntros (rt T ot st π r v Hmt (ly & Hst & ? & <- & Hot)) "Ha".
    subst.
    destruct r as [r | ]; simpl; first last.
    { rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
      iApply (ty_decodable unitRT (uninit (ty_syn_type T MetaNone)) ot st π () v with "Ha").
      - done.
      - rewrite ty_has_op_type_unfold/=. exists (ot_layout ot). done.
    }
    rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    iDestruct "Ha" as "(%r'' & Hrfn & Hv)".
    iApply (ty_decodable rt T ot st π r'' v with "Hv").
    - done.
    - rewrite Hot. rewrite ty_has_op_type_unfold. apply _ty_has_op_type_untyped; done.
  Qed.
  Next Obligation.
    iIntros (rt T ot st π r v v' Hmt (ly & Hst & ? & <- & Hot) Hsame) "Ha".
    subst.
    destruct r as [r | ]; simpl; first last.
    { rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
      iApply (ty_decode_compat unitRT (uninit (ty_syn_type T MetaNone)) ot st π () v v' with "Ha").
      - done.
      - rewrite ty_has_op_type_unfold/=. exists (ot_layout ot). done.
      - done.
    }
    rewrite maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    iDestruct "Ha" as "(%r'' & Hrfn & Hv)".
    iExists r''. iFrame.
    iApply (ty_decode_compat rt T ot st π r'' v v' with "Hv").
    - done.
    - rewrite Hot. rewrite ty_has_op_type_unfold.
      apply _ty_has_op_type_untyped; done.
    - done.
  Qed.
  Next Obligation.
    intros ?? ly Heq Hst.
    simpl. exists ly.
    apply syn_type_has_layout_untyped_inv in Hst.
    done.
  Qed.

  Global Instance maybe_uninit_sized {rt} (ty : type rt) :
    TySized ty →
    TySized (maybe_uninit ty).
  Proof.
    intros Hsz. econstructor; simpl.
    - apply Hsz.
    - intros m1 m2. by rewrite (ty_sized_syn_type_eq m1 m2).
  Qed.
End type.

Section ne.
  Context `{!typeGS Σ}.

  Global Program Instance maybe_uninit_dep_lft_morphism {rts rt} deps
      (T : mut_types rts → type rt) :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x, maybe_uninit (T x)) :=
    λ HT, dep_lft_morph_make_id deps T (λ x, maybe_uninit (T x)) HT _ _.
  Next Obligation.
    simpl. rewrite {1}ty_lfts_unfold. done.
  Qed.
  Next Obligation.
    simpl. rewrite {1}ty_wf_E_unfold. done.
  Qed.

  Global Instance maybe_uninit_ne {rt} :
    TypeNonExpansive (maybe_uninit (rt:=rt)).
  Proof.
    constructor; simpl.
    - done.
    - intros ty ty' Heq m. rewrite Heq. done.
    - rewrite ty_has_op_type_unfold/=.
      intros ?? -> -> Hot.
      intros ot.
      do 4 f_equiv.
    - done.
    - intros n ty ty' ?.
      intros π r m v. rewrite /ty_own_val/= !maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
      destruct r as [r | ]; solve_type_proper.
    - solve_type_proper.
  Qed.
End ne.

Section subtype.
  Context `{!typeGS Σ}.

  Lemma ty_own_val_Some_maybe_uninit {rt} (ty : type rt) x π v m :
    v ◁ᵥ{π, m} (Some (#x)) @ maybe_uninit ty -∗ v ◁ᵥ{π, m} x @ ty.
  Proof.
    rewrite {1}/ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    iIntros "(% & -> & ?)". done.
  Qed.
  Lemma ty_own_val_maybe_uninit_Some {rt} (ty : type rt) x π v m :
    v ◁ᵥ{π, m} x @ ty -∗ v ◁ᵥ{π, m} (Some #x) @ maybe_uninit ty.
  Proof.
    rewrite {2}/ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    iIntros "$". done.
  Qed.
  Lemma maybe_uninit_Some_unfold {rt} (ty : type rt) x π v m  :
    v ◁ᵥ{π, m} (Some (#x)) @ maybe_uninit ty ⊣⊢ v ◁ᵥ{π, m} x @ ty.
  Proof.
    iSplit.
    - iApply ty_own_val_Some_maybe_uninit.
    - iApply ty_own_val_maybe_uninit_Some.
  Qed.

  Lemma ty_own_val_None_maybe_uninit {rt} (ty : type rt) π v m :
    v ◁ᵥ{π, m} None @ maybe_uninit ty -∗ v ◁ᵥ{π, m} .@ uninit (ty.(ty_syn_type) MetaNone).
  Proof.
    rewrite {1}/ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    rewrite /ty_own_val/=.
    iIntros "(-> & ?)". iFrame. done.
  Qed.
  Lemma ty_own_val_maybe_uninit_None {rt} (ty : type rt) π v m :
    v ◁ᵥ{π, m} .@ uninit (ty.(ty_syn_type) MetaNone) -∗ v ◁ᵥ{π, m} None @ maybe_uninit ty.
  Proof.
    rewrite {2}/ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    rewrite /ty_own_val/=.
    iIntros "(-> & ?)". iFrame. done.
  Qed.
  Lemma maybe_uninit_None_unfold {rt} (ty : type rt) π v m :
    v ◁ᵥ{π, m} None @ maybe_uninit ty ⊣⊢ v ◁ᵥ{π, m} .@ uninit (ty.(ty_syn_type) MetaNone).
  Proof.
    iSplit.
    - iApply ty_own_val_None_maybe_uninit.
    - iApply ty_own_val_maybe_uninit_None.
  Qed.

  (** Subtyping *)
  Lemma type_incl_maybe_uninit_Some {rt} (ty : type rt) (x : rt) :
    ⊢ type_incl x (Some (#x)) ty (maybe_uninit ty).
  Proof.
    iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π m v) "Hv".
      rewrite maybe_uninit_Some_unfold. done.
    - iIntros (κ π m l) "Hl". iExists x. eauto with iFrame.
  Qed.

  Lemma type_incl_Some_maybe_uninit {rt} (ty : type rt) (x : rt) :
    ty_sidecond ty -∗
    type_incl (Some (#x)) x (maybe_uninit ty) ty.
  Proof.
    iIntros "#Hsc". iSplitR; first iModIntro. { simpl; eauto. }
    iSplit; iModIntro.
    - iIntros (???). iApply ty_own_val_Some_maybe_uninit.
    - rewrite {1}/ty_shr/=. iIntros (κ π m v) "(% & <- & Hl)". done.
  Qed.

  Lemma type_incl_maybe_uninit_None {rt} (ty : type rt) `{!TySized ty} :
    ⊢ type_incl () None (uninit (ty.(ty_syn_type) MetaNone)) (maybe_uninit ty).
  Proof.
    iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π m v) "Hv". simpl.
      rewrite maybe_uninit_None_unfold.
      done.
    - iIntros (κ π m l) "Hl".
      iEval (rewrite /ty_shr/=).
      rewrite (ty_sized_syn_type_eq _ m). done.
  Qed.

  Lemma type_incl_None_maybe_uninit {rt} (ty : type rt) `{!TySized ty} :
    ⊢ type_incl None () (maybe_uninit ty) (uninit (ty.(ty_syn_type) MetaNone)).
  Proof.
    iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π m v) "Hv". simpl.
      rewrite maybe_uninit_None_unfold. done.
    - iIntros (κ π m l) "Hl".
      iEval (rewrite /ty_shr/=).
      rewrite (ty_sized_syn_type_eq _ m). done.
  Qed.
End subtype.

Section rules.
  Context `{!typeGS Σ}.

  (** subtyping rules: *)
  Lemma strong_subtype_None_maybe_uninit E L {rt} (ty : type rt) `{!TySized ty} (r2 : unit) T :
    ⌜r2 = tt⌝ ∗ T ⊢ strong_subtype E L None r2 (maybe_uninit ty) (uninit (ty.(ty_syn_type) MetaNone)) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame.
    iSplitR; last by iApply type_incl_None_maybe_uninit.
    iPureIntro. simpl. intros m.
    by rewrite (ty_sized_syn_type_eq _ MetaNone).
  Qed.
  Definition strong_subtype_None_maybe_uninit_inst := [instance @strong_subtype_None_maybe_uninit].
  Global Existing Instance strong_subtype_None_maybe_uninit_inst.

  (* a variant that works in case the goal is an evar *)
  Lemma strong_subtype_None_maybe_uninit_evar E L {rt} (ty : type rt) `{!TySized ty} (r2 : unit) (ty2 : type unit) `{!IsProtected ty2} T :
    ⌜r2 = tt⌝ ∗ ⌜ty2 = (uninit (ty.(ty_syn_type) MetaNone))⌝ ∗ T ⊢ strong_subtype E L None r2 (maybe_uninit ty) ty2 T.
  Proof.
    iIntros "(-> & -> & HT)". iApply strong_subtype_None_maybe_uninit. iR; done.
  Qed.
  Definition strong_subtype_None_maybe_uninit_evar_inst := [instance @strong_subtype_None_maybe_uninit_evar].
  Global Existing Instance strong_subtype_None_maybe_uninit_evar_inst.

  Lemma strong_subtype_maybe_uninit_None E L {rt} (ty : type rt) `{!TySized ty} r2 T :
    ⌜r2 = None⌝ ∗ T ⊢ strong_subtype E L () r2 (uninit (ty.(ty_syn_type) MetaNone)) (maybe_uninit ty) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame.
    iSplitR; last by iApply type_incl_maybe_uninit_None.
    iPureIntro. intros m. simpl. by rewrite (ty_sized_syn_type_eq _ MetaNone).
  Qed.
  Definition strong_subtype_maybe_uninit_None_inst := [instance @strong_subtype_maybe_uninit_None].
  Global Existing Instance strong_subtype_maybe_uninit_None_inst.

  Lemma strong_subtype_Some_maybe_uninit E L {rt} (ty : type rt) (x : place_rfn rt) r2 T :
    (∃ x', ⌜x = #x'⌝ ∗ ⌜r2 = x'⌝ ∗ ty_sidecond ty ∗ T) ⊢ strong_subtype E L (Some x) r2 (maybe_uninit ty) ty T.
  Proof.
    iIntros "(%x' & -> & -> & Hsc & HT)" (??) "#CTX #HE HL". iFrame.
    iSplitR; last by iApply type_incl_Some_maybe_uninit.
    iPureIntro. intros m. apply syn_type_compat_untyped_l. done.
  Qed.
  Definition strong_subtype_Some_maybe_uninit_inst := [instance @strong_subtype_Some_maybe_uninit].
  Global Existing Instance strong_subtype_Some_maybe_uninit_inst.

  (* a variant that works in case the goal is an evar *)
  Lemma strong_subtype_Some_maybe_uninit_evar E L {rt} (ty : type rt) (x : place_rfn rt) r2 ty2 `{!IsProtected ty2} T :
    (∃ x', ⌜x = #x'⌝ ∗ ⌜r2 = x'⌝ ∗ ⌜ty2 = ty⌝ ∗ ty_sidecond ty ∗ T) ⊢ strong_subtype E L (Some x) r2 (maybe_uninit ty) ty2 T.
  Proof.
    iIntros "(%x' & -> & -> & -> & Hsc & HT)" (??) "#CTX #HE HL". iFrame.
    iSplitR; last by iApply type_incl_Some_maybe_uninit.
    iPureIntro. intros m. apply syn_type_compat_untyped_l. done.
  Qed.
  Definition strong_subtype_Some_maybe_uninit_evar_inst := [instance @strong_subtype_Some_maybe_uninit_evar].
  Global Existing Instance strong_subtype_Some_maybe_uninit_evar_inst.

  Lemma strong_subtype_maybe_uninit_Some E L {rt} (ty : type rt) (x : rt) r2 T :
    ⌜r2 = Some #x⌝ ∗ T ⊢ strong_subtype E L x r2 ty (maybe_uninit ty) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame.
    iSplitR; last by iApply type_incl_maybe_uninit_Some.
    iPureIntro. intros m. by apply syn_type_compat_untyped_r.
  Qed.
  Definition strong_subtype_maybe_uninit_Some_inst := [instance @strong_subtype_maybe_uninit_Some].
  Global Existing Instance strong_subtype_maybe_uninit_Some_inst.

  Lemma strong_subltype_maybe_uninit_ghost E L {rt} (ty : type rt) γ r2 T :
    ⌜r2 = #(Some (👻 γ))⌝ ∗ T
    ⊢ strong_subltype E L (Owned) (👻 γ) r2 (◁ ty) (◁ (maybe_uninit ty)) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (??) "#CTX #HE HL". iFrame. iModIntro.
    iSplitR. { iPureIntro. by apply syn_type_compat_untyped_r. }
    iModIntro. simp_ltypes.
    rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & Hlb & %r' & Hrfn & Hl)".
    iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists ly.
    iSplitR. { iPureIntro. by apply syn_type_has_layout_untyped. }
    iR. iSplitR. { rewrite /maybe_uninit. done. }
    iFrame. iExists (Some (👻 γ)). iR. iModIntro.
    rewrite {2}/ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def.
    eauto with iFrame.
  Qed.
  Definition strong_subltype_maybe_uninit_ghost_inst := [instance @strong_subltype_maybe_uninit_ghost].
  Global Existing Instance strong_subltype_maybe_uninit_ghost_inst | 40.

  Lemma owned_subtype_uninit_maybe_uninit π E L pers {rt} (ty : type rt) (st : syn_type) T :
    li_tactic (compute_layout_goal st) (λ ly1,
      li_tactic (compute_layout_goal (ty_syn_type ty MetaNone)) (λ ly2,
        ⌜ly_size ly1 = ly_size ly2⌝ ∗ T L))
    ⊢ owned_subtype π E L pers () None (uninit st) (maybe_uninit ty) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Halg1 & %ly2 & %Halg2 & %Hsz & HT)".
    iIntros (????) "#CTX #HE HL". iExists L. iModIntro. iFrame.
    iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    iSplit; last iSplitR.
    { iPureIntro. simpl.
      eapply syn_type_size_eq_prove; [apply syn_type_has_layout_untyped.. | ]; done. }
    { simpl. done. }
    iIntros (v) "Hv". rewrite !uninit_own_spec.
    iDestruct "Hv" as "(_ & %ly &  %Hst & %Hly)".
    assert (ly1 = ly) as <- by by eapply syn_type_has_layout_inj.
    rewrite /ty_own_val/= maybe_uninit_own_val_unfold /maybe_uninit_own_val_def. iApply uninit_own_spec.
    iR.
    iExists _. iR.
    iPureIntro. rewrite /has_layout_val -Hsz//.
  Qed.
  Definition owned_subtype_uninit_maybe_uninit_inst := [instance @owned_subtype_uninit_maybe_uninit].
  Global Existing Instance owned_subtype_uninit_maybe_uninit_inst.

End rules.



  (*
     What happens with borrowing?
     - if it is Some, I want to create a borrow for the whole thing.
        To do that, I will probably need a place rule that just makes a maybeuninit into the inner type for the place access, and in the continuation wraps it again.
     - what happens with the blocked then? I cannot wrap a blocked directly in this type.
       In principle, this is fine from the perspective of the mutref contract, because the borrow enforces that I actually get a T back, so it is fine to put a Some there.
       Should I just bubble the blocked up (i.e. use openedltype/coreable)?
       In principle I know that I will get a maybe_uninit T back after the borrow ends, so this is fine intuitively. The only diff is how the ghost resolution does stuff. (NOTE: here ghost resolution would need to descend below the maybeuninit. But I have the right infrastructure for that, we just need to add a ghost_resolve instance for ◁ (maybe_uninit T)
       So I guess the place instance will just work via openedltype.
   *)

  (*
     How will the write of an initialized element to a maybeuninit location look?
     - in principle, if we can write strongly, just write. OpenedLtype closing should later apply the subtyping rule for injection into maybe_uninit.

     - for an array_ltype, subtyping should work elementwise. The openedltype in that case will require to go to an array where every field has the same type. Afterwards, that can be folded to an array_type again.


     TODO one thing to think about: we can't do refinement type updates for array_ltype, so we need to do the injection already at time of writing.
     How should writing work?
      - have: current type of place (ltype), type of value to write
      - options for rules we can use:
        + do a strong write, just put in the current value at its type.
        + do a strong write, but just put in a value_t for the written value and assemble ownership later on when needed.
        + directly adapt the type via subtyping so they match
      - we can also combine the options:
        + have specific instances (high priority) for particular combinations of types, and use one of the other options as default if they don't match.
          -> already doing that currently for writing to a mutltype etc.
          -> for maybe_uninit: have two specific instances for writing to it.
        + and then, as a fallback: just do a strong write (or decide based on the type change).

   *)

  (* Issue for borrowing:
     if we borrow a maybe_uninit T but really need a T, we need to know that and commit to it ahead of time (when borrowing) because of restricted subtyping.
     Solutions:
     - actually do a reborrow when subtyping, since the refinement gives us enough information
        then there's a lot of stuff happening there. it also needs later credits. so this gets quite fragile.
     - can we do the previous thing without reborrowing? could this ability be directly built into mut refs?
        in principle, stuff like this that is enabled by the refinements should be more natural.
        Point is: our refinement model is too inflexible. we need more leverage to say that the other case (None) is vacuous because of refinement info.
          - this is not quite true, because the lender will still expect the maybe_uninit back, not the full thing.
            in a sense, this case is really similar to the [u8; 2] ≈ u16 case. It's basically equivalent according to the intuitive notion of subtyping (taking into account the refinement) but it doesn't hold in our model.
     - have custom rules and just say that we generally borrow the T instead of the maybe_uninit when the refinement says so.
        this makes it a bit less flexible, but it's probably fine. the annoying part is that we have to duplicate the borrowing logic a bit.
     => TODO which of these makes most sense?
   *)
