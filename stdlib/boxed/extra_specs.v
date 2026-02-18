Section box.
  Context `{!LayoutAlg}.

  (* Notation used for Rust's magic box deref *)
  Definition magic_box_deref (T_st A_st : syn_type) (e : expr) : expr :=
    (*b.0.pointer.pointer*)
    (!{PtrOp} (((e at{Box_sls T_st A_st} "0") at{unique_Unique_sls T_st} "ptr") at{nonnull_NonNull_sls T_st} "pointer"))%E
  .
End box.
#[export] Hint Unfold magic_box_deref : solve_into_place_unfold.
Notation "'!box{' T_st ',' A_st '}' e" := (magic_box_deref T_st A_st e) (at level 9, format "!box{ T_st , A_st } e") : expr_scope.

Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance Box_inv_t_contr {rt1 T_rt A_rt : RT} (T : type rt1 → type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, Box_inv_t T_rt A_rt A_attrs <TY> (T ty) <TY> A_ty <INST!>).
  Proof.
    intros X.
    apply ex_inv_def_contractive.
    - constructor.
      + simpl. apply ty_lft_morphism_to_direct.
        apply X.
      + solve_proper_prepare.
        repeat solve_proper_step.
      + solve_proper_prepare.
        repeat solve_proper_step.
    - cbn; apply _.
  Qed.
  Global Instance Box_inv_t_ne {rt1 T_rt A_rt : RT} (T : type rt1 → type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, Box_inv_t T_rt A_rt A_attrs <TY> (T ty) <TY> A_ty <INST!>).
  Proof. apply _. Qed.

  (** Resolve ghost: Resolve observations on the contained value. *)
  Lemma resolve_ghost_box {T_rt A_rt} A_attrs (T_ty : type T_rt) (A_ty : type A_rt) π E L r rm T :
    (∀ l', resolve_ghost π E L rm true l' (◁ T_ty) (Owned false) r T)
    ⊢ resolve_ghost_adt π E L rm r (Box_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>) T.
  Proof.
    rewrite /resolve_ghost_adt /resolve_ghost.
    iIntros "HT" (????) "#CTX #HE HL Hv".
    iEval (rewrite /ty_own_val/=) in "Hv".
    iDestruct "Hv" as ((l' & a & [])) "(Hinv & Hv)". simpl in *.
    iDestruct "Hinv" as "(%l'' & %a'' & %Heq & Hl' & Halloc & _)".
    inversion Heq. subst.
    unfold guarded. iDestruct "Hl'" as "(Hc & Hl')".
    iDestruct "Hc" as "((Hc1 & Hc) & Ht)".
    iApply (lc_fupd_add_later with "Hc1"). iNext.
    iMod ("HT" with "[] [] CTX HE HL Hl'") as "(%L2 & %r' & %R & %progress & Hstep & HL & HT)"; [done.. | ].
    iFrame.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Ht").
    iModIntro. iIntros "Ht Hcreds' !> (Hl' & $)".
    iEval (rewrite /ty_own_val/=).
    iFrame. iR.
    rewrite /guarded. iFrame.
    iDestruct "Ht" as "(_ & $)".
  Qed.

  (* Box is covariant in T and A *)
  Lemma subtype_box {T_rt A_rt} A_attrs (T_ty_1 T_ty_2 : type T_rt) (A_ty_1 A_ty_2 : type A_rt) E L T :
    mut_subtype E L T_ty_1 T_ty_2 (mut_subtype E L A_ty_1 A_ty_2 T)
    ⊢ subtype_adt E L (Box_inv_t_inv_spec T_rt A_rt A_attrs <TY> T_ty_1 <TY> A_ty_1 <INST!>) (Box_inv_t_inv_spec T_rt A_rt A_attrs <TY> T_ty_2 <TY> A_ty_2 <INST!>) T.
  Proof.
    rewrite /mut_subtype /subtype_adt.
    iIntros "(%HsubT & %HsubA & $)". iPureIntro.
    iIntros (?) "HL HE".
    iPoseProof (full_subtype_acc_noend with "HE HL") as "#HinclT"; first apply HsubT.
    iPoseProof (full_subtype_acc_noend with "HE HL") as "#HinclA"; first apply HsubA.
    iSplit; iModIntro.
    - iIntros (? x r). simpl.
      iIntros "(%l & %a & -> & Hl & Hperm)".
      iExists _, _. iR.
      iDestruct ("HinclT" $! inhabitant) as "(%Hst & _ )".
      rewrite Hst. iFrame.
      iApply (guarded_mono with "[] Hl").
      iIntros "Hl". by iApply type_incl_ltype_owned_wand.
    - iIntros (? ? x r). simpl.
      iIntros "(%l & %a & -> & Hl & Hperm)".
      iExists _, _. iR. iL.
      iApply (guarded_mono with "[] Hl").
      iIntros "Hl". by iApply type_incl_ltype_shared_wand.
  Qed.
  Definition subtype_box_inst := [instance @subtype_box].
  Global Existing Instance subtype_box_inst.
End contractive.
