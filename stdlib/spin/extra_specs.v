
Section extra.
Context `{RRGS : !refinedrustGS Σ}.


Lemma resolve_ghost_writeguard {T_rt R_rt} (T_ty : type T_rt) (R_ty : type R_rt) (lft_a : lft) π E L r rm T :
    (∀ l', resolve_ghost π E L rm true l' (◁ T_ty) Owned r T)
    ⊢ resolve_ghost_adt π E L rm r (rwlock_RwLockWriteGuard_inv_t T_rt R_rt <LFT> lft_a <TY> T_ty <TY> R_ty <INST!>) T.
  Proof.
  Admitted.
Definition resolve_ghost_writeguard_inst := [instance @resolve_ghost_writeguard].
Global Existing Instance resolve_ghost_writeguard_inst.

End extra.
