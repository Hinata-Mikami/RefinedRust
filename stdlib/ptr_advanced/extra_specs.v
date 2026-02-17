Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance NonNull_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_inv_def_contractive.
    - constructor.
      + simpl. apply _.
      + solve_proper.
      + solve_proper.
    - cbn. apply _.
  Qed.
  Global Instance NonNull_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, nonnull_NonNull_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.
  Global Instance Unique_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_inv_def_contractive.
    - constructor.
      + simpl. apply _.
      + solve_proper.
      + solve_proper.
    - cbn; apply _.
  Qed.
  Global Instance Unique_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, unique_Unique_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.
End contractive.
