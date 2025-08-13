From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** ** Unit type *)
(** [unit_t] gets some special treatment, because it occurs frequently and is specced to be a ZST *)
Section unit.
  Context `{!typeGS Σ}.

  Program Definition unit_t : type unit := {|
    st_own π _ v := ⌜v = zst_val⌝;
    st_syn_type := UnitSynType;
    st_has_op_type ot mt := is_unit_ot ot;
  |}%I.
  Next Obligation.
    iIntros (π _ v ->).
    iPureIntro. eexists. split; first by apply syn_type_has_layout_unit.
    done.
  Qed.
  Next Obligation.
    intros ot mt ->%is_unit_ot_layout.
    by apply syn_type_has_layout_unit.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. iIntros (ot ?? _ _  v Hot ->).
    destruct mt.
    - done.
    - destruct ot; try by destruct Hot. destruct Hot as [-> ->]. done.
    - iApply (mem_cast_compat_unit (λ _, True)%I); eauto.
  Qed.
  Next Obligation.
    intros mt ly Hst.
    apply syn_type_has_layout_unit_inv in Hst as ->.
    done.
  Qed.

  Global Instance unit_copyable : Copyable unit_t.
  Proof. apply _. Qed.

  Global Instance unit_timeless l z π:
    Timeless (l ◁ᵥ{π} z @ unit_t)%I.
  Proof. apply _. Qed.

  Lemma type_val_unit π (T : typed_value_cont_t):
    T _ (unit_t) () ⊢ typed_value π (zst_val) T.
  Proof.
    iIntros "HT #LFT".
    iExists _, unit_t, (). iFrame "HT". done.
  Qed.
  Global Instance type_val_unit_inst π : TypedValue π zst_val :=
    λ T, i2p (type_val_unit π T).
End unit.

Global Hint Unfold unit_t : tyunfold.
