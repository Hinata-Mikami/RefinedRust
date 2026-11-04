Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance NonNull_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper.
      + solve_proper.
    - cbn. apply _.
  Qed.
  Global Instance NonNull_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.

  Global Program Instance NonNull_inv_t_dep_lft_mor rts (T_rt : RT) (T : mut_types rts → type T_rt) :
    DepLftMorphism ∅ (λ x : mut_types rts, nonnull_NonNull_inv_t T_rt *[] *[(T x)]) :=
      mk_dep_lft_morph_const _ static [] _ _.
  Next Obligation.
    intros. simpl.
    iIntros (?).
    repeat rewrite !ty_lfts_unfold/=.
    iApply lft_equiv_refl.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    done.
  Qed.

  Global Instance Unique_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper.
      + solve_proper.
    - cbn; apply _.
  Qed.
  Global Instance Unique_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.

  Global Program Instance Unique_inv_t_dep_lft_mor rts (rt : RT) (T : mut_types rts → type rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, unique_Unique_inv_t rt *[] *[(T x)]) :=
    λ Ht,
      dep_lft_morph_make_id _ _ _ Ht _ _.
  Next Obligation.
    intros. rewrite /lifecycle_lfts/=.
    repeat rewrite !ty_lfts_unfold/=.
    rewrite !right_id//.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    rewrite !right_id//.
  Qed.
End contractive.
