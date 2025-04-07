Section Vec_inv_t_ne.
  Context `{!refinedrustGS Σ}.

  Global Instance Vec_inv_t_contr {rt1 T_rt A_rt} (T : type rt1 → type T_rt) (A : type A_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, Vec_inv_t T_rt A_rt <TY> (T ty) <TY> A <INST!>).
  Proof.
  Admitted.
  Global Instance Vec_inv_t_ne {rt1 T_rt A_rt} (T : type rt1 → type T_rt) (A : type A_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, Vec_inv_t T_rt A_rt <TY> (T ty) <TY> A <INST!>).
  Proof. Admitted.
End Vec_inv_t_ne.
