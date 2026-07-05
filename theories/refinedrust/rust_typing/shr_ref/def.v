From refinedrust Require Export type lftmor.
From refinedrust Require Import options.

(** * Shared references *)
Section shr_ref.
  Context `{typeGS Σ}.
  Implicit Types (κ : lft).

  Definition shr_ref_own_val_def {rt : RT} κ (inner : type rt) π r m v : iProp Σ :=
    (∃ (l : loc) (ly : layout) (r' : rt),
      ⌜m = MetaNone⌝ ∗
      ⌜val_to_loc v = Some l⌝ ∗
      ⌜use_layout_alg (inner.(ty_syn_type) MetaNone) = Some ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      inner.(ty_sidecond) ∗
      place_rfn_interp_shared r r' ∗
      □ |={lftE}=> inner.(ty_shr) κ π r' MetaNone l)%I
  .
  Definition shr_ref_own_val_aux : seal (@shr_ref_own_val_def).
  Proof. by eexists. Qed.
  Definition shr_ref_own_val := shr_ref_own_val_aux.(unseal).
  Definition shr_ref_own_val_unfold : @shr_ref_own_val = @shr_ref_own_val_def := shr_ref_own_val_aux.(seal_eq).

  Definition shr_ref_shr_def {rt : RT} κ (inner : type rt) κ' π r m l : iProp Σ :=
    (∃ (li : loc) (ly : layout) (ri : rt),
      ⌜m = MetaNone⌝ ∗
      ⌜l `has_layout_loc` void*⌝ ∗
      (*loc_in_bounds l void*.(ly_size) ∗*)
      ⌜use_layout_alg (inner.(ty_syn_type) MetaNone) = Some ly⌝ ∗
      ⌜li `has_layout_loc` ly⌝ ∗
      loc_in_bounds li 0 ly.(ly_size) ∗
      inner.(ty_sidecond) ∗
      place_rfn_interp_shared r ri ∗
      &frac{κ'} (λ q, l ↦{q} li) ∗ ▷ □ |={lftE}=> inner.(ty_shr) (κ) π ri MetaNone li)%I.
  Definition shr_ref_shr_aux : seal (@shr_ref_shr_def).
  Proof. by eexists. Qed.
  Definition shr_ref_shr := shr_ref_shr_aux.(unseal).
  Definition shr_ref_shr_unfold : @shr_ref_shr = @shr_ref_shr_def := shr_ref_shr_aux.(seal_eq).

  (* this is almost a simple type, but we have to be careful with
    the sharing predicate: we want to obtain the knowledge that l points to
    a location not under a later (to prove the agreement with the ltype unfolding),
     so the simple_type interface doesn't suffice *)
  Program Definition shr_ref {rt : RT} κ (inner : type rt) : type (place_rfn rt) := {|
    ty_sidecond := True;
    ty_metadata_kind := MetadataNone;
    ty_trivial_drop := true;
    ty_own_val := shr_ref_own_val _ κ inner;

    _ty_has_op_type ot := is_ptr_ot ot;
    ty_syn_type m := PtrSynType;

    ty_shr := shr_ref_shr _ κ inner;
    _ty_ghost_drop _ _ := True%I;
    _ty_lfts := [κ] ++ ty_lfts inner;
    _ty_wf_E := ty_wf_E inner ++ ty_outlives_E inner κ;
  |}.
  Next Obligation.
    intros. simpl. apply _.
  Qed.
  Next Obligation.
    rewrite shr_ref_own_val_unfold.
    iIntros (???????) "(%l & %ly & %r' & -> & % & ? & ? & ?)".
    iPureIntro. eexists. split; first by apply syn_type_has_layout_ptr.
    by apply val_to_loc_length.
  Qed.
  Next Obligation.
    iIntros (??? ot Hot) => /=.
    destruct ot => /=//.
    - by apply syn_type_has_layout_ptr.
    - by apply syn_type_has_layout_ptr.
  Qed.
  Next Obligation. iIntros (??? ????) "_". done. Qed.
  Next Obligation. iIntros (??? ?????) "_". done. Qed.
  Next Obligation.
    unfold TCNoResolve.
    rewrite shr_ref_shr_unfold.
    apply _.
  Qed.
  Next Obligation.
    iIntros (??? ?????). simpl.
    rewrite shr_ref_shr_unfold.
    iIntros "(%l' & %ly & %r' & % & % & ? & ? & _)".
    iPureIntro. eexists _. split; last by apply syn_type_has_layout_ptr.
    done.
  Qed.
  Next Obligation.
    iIntros (??? E κ' l ly π r m q ?) "#[LFT TIME] #Hna Htok %Halg %Hly _ Hb".
    rewrite shr_ref_own_val_unfold shr_ref_shr_unfold.
    simpl. rewrite -{1}lft_tok_sep -{1}lft_tok_sep.
    iDestruct "Htok" as "(Htok_κ' & Htok_κ & Htok)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%v & Hb)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hl Hb]"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as "(%l' & Hb)"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first solve_ndisj.
    iMod (bor_exists_tok with "LFT Hb Htok_κ'") as "(%r' & Hb & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Heq Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Heq Htok_κ'") as "(>%Hv & Htok_κ')"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hb Htok_κ'") as "(Ha & Htok_κ')"; first solve_ndisj.
    iDestruct "Ha" as "(>%Halg' & >%Hly' & >#Hlb & >#Hsc & >Hrfn & Hshr)".
    iMod (bor_fracture (λ q, l ↦{q} v)%I with "LFT Hl") as "Hl"; first solve_ndisj.
    iModIntro.
    iApply logical_step_intro.
    rewrite -!lft_tok_sep. iFrame.
    apply syn_type_has_layout_ptr_inv in Halg as ->.
    iExists ly'.
    iR.
    do 4 iR.
    erewrite l2v_correct'; last done.
    iFrame. iFrame "Hsc".
  Qed.
  Next Obligation.
    iIntros (??? κ' κ'' π r m l) "#Hord H".
    rewrite shr_ref_shr_unfold.
    iDestruct "H" as (li ly ri ->) "(? & ? & ? & Hlb & Hsc & Hr & #Hf & #Hown)".
    iExists li, ly, ri. iR. iFrame. iSplit.
    - by iApply (frac_bor_shorten with "Hord").
    - iNext. iDestruct "Hown" as "#Hown". iModIntro. iMod "Hown". iModIntro.
      done.
  Qed.
  Next Obligation.
    intros. iIntros "_". by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (??? ot st ? r m ? Hot).
    rewrite shr_ref_own_val_unfold.
    iIntros "(%l & %ly & %ri & -> & %Hv & ? & ? & ?)".
    iExists l, ly, ri. iFrame.
    iPureIntro. split; first done.
    move: ot Hot => [] /= // _.
    rewrite /mem_cast Hv//.
  Qed.
  Next Obligation.
    intros ??? ly _ Hst. apply syn_type_has_layout_ptr_inv in Hst as ->.
    done.
  Qed.
End shr_ref.

Section props.
  Context `{!typeGS Σ}.

  Global Instance shr_ref_sized {rt} (ty : type rt) κ : TySized (shr_ref κ ty).
  Proof.
    econstructor; done.
  Qed.

  Global Instance shr_ref_copyable {rt} (ty : type rt) κ : Copyable (shr_ref κ ty).
  Proof.
    constructor.
    { intros. rewrite /ty_own_val/= shr_ref_own_val_unfold. apply _. }
    rewrite /ty_shr/= shr_ref_shr_unfold.
    iIntros (κ' π E l r ? ? ?) "[LFT TIME] (%li & %ly' & %r' & -> & %Hly' & % & % & #Hlb & #Hsc & #Hr & Hf & #Hown) Hlft".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first solve_ndisj.
    iModIntro.
    (*apply syn_type_has_layout_ptr_inv in Ha as ->.*)
    (*iSplitR; first done.*)
    iExists _.
    iSplitR. { simpl. iPureIntro. by apply syn_type_has_layout_ptr. }
    iR.
    iExists _, li. iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iPoseProof (loc_in_bounds_in_range_usize with "Hlb") as "%".
    iSplitL "Hmt1". { iNext. iFrame "Hmt1".
      rewrite /ty_own_val/= shr_ref_own_val_unfold.
      iExists li, ly', r'.
      iFrame "#". iPureIntro. split_and!; try done.
      apply val_to_of_loc. by apply val_of_loc_Some_l2v. }
    iIntros "Hmt1".
    iApply "Hclose". iModIntro. rewrite -{3}(Qp.div_2 q').
    iPoseProof (heap_pointsto_agree with "Hmt1 Hmt2") as "%Heq"; first done.
    rewrite heap_pointsto_fractional. iFrame.
  Qed.

  Lemma shr_ref_ty_lft_morphism {rt : RT} κ : TyLftMorphism (shr_ref (rt:=rt) κ).
  Proof.
    eapply ty_lft_morph_make_ref.
    - rewrite {1}ty_lfts_unfold; done.
    - rewrite {1}ty_wf_E_unfold; done.
  Qed.

  Global Instance shr_ref_lft_morphism {A rt} `{!Lifecycle A}
      (T : A → type rt) κ :
    LftMorphism T →
    LftMorphism (λ x, shr_ref κ (T x)).
  Proof.
    intros HT.
    change (LftMorphism ((shr_ref κ) ∘ T)).
    eapply LftMorphism_compose; first exact HT.
    apply shr_ref_ty_lft_morphism.
  Qed.

  Global Program Instance shr_ref_dep_lft_morphism {rts rt} deps
      (T : mut_types rts → type rt) κ :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x, shr_ref κ (T x)) :=
    λ HT, dep_lft_morph_make_ref deps T (λ x, shr_ref κ (T x)) κ HT _ _.
  Next Obligation.
    rewrite {1}ty_lfts_unfold. done.
  Qed.
  Next Obligation.
    rewrite {1}ty_wf_E_unfold. done.
  Qed.

  Global Instance shr_ref_type_contractive {rt : RT} κ : TypeContractive (shr_ref (rt:=rt) κ).
  Proof.
    constructor; simpl.
    - done.
    - done.
    - apply shr_ref_ty_lft_morphism.
    - rewrite ty_has_op_type_unfold/=. done.
    - done.
    - rewrite /ty_own_val/= shr_ref_own_val_unfold. solve_type_proper.
    - rewrite /ty_shr/= shr_ref_shr_unfold. solve_type_proper.
  Qed.

  Global Instance shr_ref_type_ne {rt : RT} κ : TypeNonExpansive (shr_ref (rt:=rt) κ).
  Proof. apply type_contractive_type_ne, _. Qed.
End props.


Notation "&shr< κ , τ >" := (shr_ref τ κ) (only printing, format "'&shr<' κ , τ '>'") : stdpp_scope.
