From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.array Require Import def.
From refinedrust Require Import options.

(** ** Initialization rule for arrays *)

Definition size_of_array_in_bytes `{!LayoutAlg} (st : syn_type) (len : nat) : nat :=
  let ly := use_layout_alg' st in
  ly.(ly_size) * len.

Lemma size_of_array_in_bytes_mono `{!LayoutAlg} st (len1 len2 : nat) :
  (len1 ≤ len2)%Z →
  (size_of_array_in_bytes st len1 ≤ size_of_array_in_bytes st len2)%Z.
Proof.
  unfold size_of_array_in_bytes. nia.
Qed.

Section init.
  Context `{!typeGS Σ}.

  Fixpoint array_init_fold E L f (es : list expr) {rt} (ty : type rt)
      (vs : list val) (rs : list rt) (T : llctx → list val → list rt → iProp Σ) : iProp Σ :=
    match es with
    | [] => T L vs rs
    | e :: es =>
        typed_val_expr E L f e (λ L1 v m rt' ty' r',
          ⌜m = MetaNone⌝ ∗
          ∃ r, owned_subtype f.1 E L1 false r' r ty' ty (λ L2,
            array_init_fold E L2 f es ty (vs ++ [v]) (rs ++ [r]) T))%I
    end.

  Lemma array_init_fold_elim E L f es {rt} (ty : type rt) ly n vs rs T Φ :
    syn_type_has_layout (ty_syn_type ty MetaNone) ly →
    length vs = length rs →
    length vs + length es = n →
    Forall (λ v, v `has_layout_val` ly) vs →
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    current_frame f.1 f.2 -∗
    ([∗ list] v;r ∈ vs;rs, v ◁ᵥ{f.1, MetaNone} r @ ty) -∗
    array_init_fold E L f es ty vs rs T -∗
    (∀ L' vs' rs',
      ⌜length vs' = length rs'⌝ -∗
      ⌜length vs' = n⌝ -∗
      ⌜Forall (λ v, v `has_layout_val` ly) vs'⌝ -∗
      llctx_interp L' -∗
      current_frame f.1 f.2 -∗
      ([∗ list] v;r ∈ vs';rs', v ◁ᵥ{f.1, MetaNone} r @ ty) -∗
      T L' vs' rs' -∗
      WPe{f.1} (Concat (Val <$> vs')) {{ Φ }}) -∗
    foldr (λ e k, λ vs', WPe{f.1} e {{ λ v, k (vs' ++ [v]) }})
      (λ vs', WPe{f.1} (Concat (Val <$> vs')) {{ Φ }}) es vs.
  Proof.
    intros Hst Hlen Htotal Hlys.
    iIntros "#CTX #HE HL Hf Hvals HT Hcont".
    iAssert ⌜length vs = length rs⌝%I as "#Hlen"; first done.
    iAssert ⌜(length vs + length es = n)%nat⌝%I as "#Htotal"; first done.
    iAssert ⌜Forall (λ v, v `has_layout_val` ly) vs⌝%I as "#Hlys"; first done.
    clear Hlen Htotal Hlys.
    iRevert (L vs rs) "HL Hf Hvals HT Hlen Htotal Hlys".
    iInduction es as [|e es] "IH"; iIntros (L vs rs) "HL Hf Hvals HT #Hlen #Htotal #Hlys"; simpl.
    { iPoseProof "Htotal" as "%Htotal'". simpl in Htotal'.
      iApply ("Hcont" with "Hlen [] Hlys HL Hf Hvals HT"). iPureIntro. lia. }
    iApply wpe_fupd.
    iApply ("HT" with "CTX HE HL Hf").
    iIntros (L1 v rt' ty' r' m) "HL Hf Hv (-> & %r & Hsub)".
    iMod ("Hsub" with "[] [] [] CTX HE HL") as (L2) "(Hincl & HL & HT)"; [done.. |].
    iDestruct "Hincl" as "(_ & _ & Hincl)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hvly"; first done.
    iPoseProof "Hlen" as "%Hlen'". iPoseProof "Htotal" as "%Htotal'".
    iPoseProof "Hlys" as "%Hlys'".
    iModIntro. iSpecialize ("IH" with "Hcont").
    iApply ("IH" $! L2 (vs ++ [v]) (rs ++ [r]) with "HL Hf [Hvals Hv] HT [] [] []").
    - rewrite big_sepL2_snoc. iFrame.
    - iPureIntro. by rewrite !length_app /= Hlen'.
    - iPureIntro. rewrite !length_app /= in Htotal' |-*; lia.
    - iPureIntro. apply Forall_app. split; first done. by constructor.
  Qed.

  Lemma type_array_init E L f (rty : rust_type) (es : list expr) (T : typed_val_expr_cont_t) :
    (∃ M, named_lfts M ∗ (named_lfts M -∗
      li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt ty),
      li_tactic (compute_layout_goal (ty_syn_type ty MetaNone)) (λ ly,
        ⌜(size_of_array_in_bytes (ty_syn_type ty MetaNone) (length es) ≤ MaxInt ISize)%Z⌝ ∗
        array_init_fold E L f es ty [] [] (λ L' vs rs,
          T L' (mjoin vs) MetaNone _ (array_t (length es) ty) (PlaceIn <$> rs))))))
    ⊢ typed_val_expr E L f (ArrayInit{rty} es)%E T.
  Proof.
    iIntros "(%M & Hnamed & HT)".
    iPoseProof ("HT" with "Hnamed") as "HT".
    rewrite /interpret_rust_type_goal /compute_layout_goal.
    iDestruct "HT" as (rt ty ly Hst Hsz) "HT".
    iIntros (Φ) "#CTX #HE HL Hf HΦ".
    rewrite /ArrayInit. iApply wp_concat_bind.
    iApply (array_init_fold_elim with "CTX HE HL Hf [] HT [-]"); [done.. |].
    iIntros (L' vs rs) "%Hlen %Htotal %Hlys HL Hf Hvals HT".
    iApply wp_concat. iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf [Hvals] HT").
    rewrite /ty_own_val /= array_t_own_val_unfold.
    iExists ly. iR. iR.
    unfold size_of_array_in_bytes in Hsz.
    rewrite /use_layout_alg' Hst/= in Hsz.
    iSplitR. { iPureIntro. lia. }
    iSplitR. { iPureIntro. by rewrite length_fmap -Hlen Htotal. }
    iSplitR.
    { iPureIntro. rewrite /has_layout_val length_join ly_size_mk_array_layout.
      have Hsum : sum_list (length <$> vs) = ly_size ly * length vs.
      { clear Hlen Htotal rs. induction Hlys as [|v vs Hv Hvs IH].
        - done.
        - simpl. unfold has_layout_val in Hv. rewrite Nat.mul_succ_r Hv IH. lia. }
      simpl in Htotal. lia. }
    rewrite reshape_join.
    2: { apply Forall2_replicate_r; [done | exact Hlys]. }
    rewrite big_sepL2_fmap_l big_sepL2_flip.
    iApply (big_sepL2_impl with "Hvals"). iModIntro.
    iIntros (i r v _ _) "Hv". iExists r. iR. iExact "Hv".
  Qed.

  Lemma type_array_repeat E L f (st : syn_type) (n : nat) e (T : typed_val_expr_cont_t) :
    li_tactic (compute_layout_goal st) (λ ly,
      ⌜(size_of_array_in_bytes st n ≤ MaxInt ISize)%Z⌝ ∗
      typed_val_expr E L f e (λ L' v m rt ty r,
        ⌜m = MetaNone⌝ ∗
        ⌜ty_syn_type ty MetaNone = st⌝ ∗
        ∃ _ : Copyable ty,
        T L' (mjoin (replicate n v)) MetaNone _ (array_t n ty)
          (replicate n (PlaceIn r))))
    ⊢ typed_val_expr E L f (Repeat{st} e n)%E T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly & %Hst & %Hsz & He)" (Φ) "#CTX #HE HL Hf HΦ".
    wpe_bind. iApply ("He" with "CTX HE HL Hf").
    iIntros (L' v m rt ty r) "HL Hf Hv (-> & <- & HT)".
    iDestruct "HT" as (Hcopy) "HT".
    assert (Copyable rt) as ? by exact Hcopy.
    iDestruct "Hv" as "#Hv".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hvly"; first done.
    iApply wp_repeat; [done | done |].
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf [Hv] HT").
    rewrite /ty_own_val /= array_t_own_val_unfold.
    iExists ly. iR. iR.
    unfold size_of_array_in_bytes in Hsz.
    rewrite /use_layout_alg' Hst/= in Hsz.
    iSplitR. { iPureIntro. lia. }
    iSplitR. { iPureIntro. rewrite length_replicate //. }
    iSplitR.
    { iPureIntro. rewrite /has_layout_val length_join fmap_replicate
        sum_list_replicate Hvly ly_size_mk_array_layout. lia. }
    rewrite reshape_join.
    2: { apply Forall2_replicate. exact Hvly. }
    rewrite big_sepL2_replicate_l; last by rewrite length_replicate.
    iApply big_sepL_intro. iModIntro. iIntros (i v' Hlook_v).
    apply lookup_replicate_1 in Hlook_v as [-> _].
    iExists ty. iR. iExact "Hv".
  Qed.
End init.
