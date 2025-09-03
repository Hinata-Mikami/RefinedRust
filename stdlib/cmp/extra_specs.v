
(** Lift to Rocq-level typeclasses *)
Lemma eq_correct_eq `{!refinedrustGS Σ} rt
  (partial_eq_attrs : PartialEq_spec_attrs rt rt)
  (eq_attrs : Eq_spec_attrs rt partial_eq_attrs) : CorrectEq (PartialEq_PEq partial_eq_attrs).
Proof.
  constructor.
  - by apply Eq_PEq_refl.
  - by unshelve eapply Eq_PEq_sym.
  - by unshelve eapply Eq_PEq_trans.
Qed.
Global Hint Extern 1 (CorrectEq (PartialEq_PEq _)) => apply eq_correct_eq; done : typeclass_instances.

Lemma ord_correct_ord `{!refinedrustGS Σ} rt
  (partial_eq_attrs : PartialEq_spec_attrs rt rt)
  (eq_attrs : Eq_spec_attrs rt partial_eq_attrs)
  (partial_ord_attrs : PartialOrd_spec_attrs rt rt partial_eq_attrs)
  (ord_attrs : Ord_spec_attrs rt partial_eq_attrs eq_attrs partial_ord_attrs) : CorrectOrd (PartialEq_PEq partial_eq_attrs) (Ord_Ord ord_attrs). 
Proof.
  constructor.
  - apply _.
  - intros. rewrite PartialOrd_POrd_eq_cons.
    erewrite Ord_Ord_POrd. split; intros; simplify_eq; [done | f_equiv; done].
  - apply Ord_Ord_lt_trans.
  - apply Ord_Ord_gt_trans.
  - apply Ord_Ord_antisym.
  - intros. 
    unshelve rewrite PartialOrd_POrd_eq_cons; first done.
    unshelve erewrite Ord_Ord_POrd; [done.. | ].
    rewrite -Ord_Ord_leibniz.
    split; intros ?; simplify_eq; [done | f_equiv; done].
Qed.
Global Hint Extern 1 (CorrectOrd _ (Ord_Ord _)) => apply ord_correct_ord; done : typeclass_instances.

