From refinedrust Require Export base hlist type ltypes.
From lithium Require Export simpl_classes normalize.
Set Default Proof Using "Type".

(** ** Additional Simpl instances *)
Global Instance simpl_eq_hlist_cons A {F} (X : A) (XS : list A) (x : F X) (y : F X) (xs ys : hlist F XS) :
  SimplAnd ((x +:: xs) = (y +:: ys)) (λ T, x = y ∧ xs = ys ∧ T).
Proof.
  split.
  - intros (-> & -> & HT). done.
  - intros (Heq & HT). injection Heq.
    intros ->%existT_inj ->%existT_inj. done.
Qed.

Global Instance simpl_eq_plist_cons A {F} (X : A) (XS : list A) (x : F X) (y : F X) (xs ys : plist F XS) :
  SimplAnd ((x -:: xs) = (y -:: ys)) (λ T, x = y ∧ xs = ys ∧ T).
Proof.
  split.
  - intros (-> & -> & HT). done.
  - intros (Heq & HT). injection Heq. done.
Qed.
Global Instance simpl_eq_plist_cons' A B (x : A) (y : A) (xs ys : B) :
  SimplAnd ((x *:: xs) = (y *:: ys)) (λ T, x = y ∧ xs = ys ∧ T).
Proof.
  split.
  - intros (-> & -> & HT). done.
  - intros (Heq & HT). injection Heq. done.
Qed.

Global Instance simpl_eq_phd {A} {F : A → Type} (Xs : list A) (X : A) (xs : plist F (X :: Xs)) (x : F X)   :
  SimplBothRel (eq) (x) (phd xs) (∃ c : plist F Xs, xs = pcons x c).
Proof.
  split.
  - intros ->. destruct xs as [? ?]. eauto.
  - intros (c & ->). done.
Qed.
Global Instance simpl_eq_ptl {A} {F : A → Type} (Xs : list A) (X : A) (xs : plist F (X :: Xs)) (xs' : plist F Xs)   :
  SimplBothRel (eq) (xs') (ptl xs) (∃ c : F X, xs = pcons c xs').
Proof.
  split.
  - intros ->. destruct xs as [? ?]. eauto.
  - intros (c & ->). done.
Qed.

Global Instance simpl_hmap_nil {A} {F G : A → Type} (f : ∀ x : A, F x → G x) (l : hlist F []) (l2 : hlist G []) :
  SimplBothRel eq (f +<$> l) l2 (l = +[] ∧ l2 = +[]).
Proof.
  split.
  - inv_hlist l; done.
  - intros [-> ->]; done.
Qed.
Global Instance simpl_hmap_cons_impl {A} {F G : A → Type} (f : ∀ x : A, F x → G x) (X : A) (Xs : list A) (x : G X) (l2 : hlist G Xs) (l : hlist F (X :: Xs)) :
  SimplImplRel eq true (f +<$> l) (x +:: l2) (λ T : Prop,
    ∀ (x' : F X) (l2' : hlist F Xs), l = x' +:: l2' → f _ x' = x → f +<$> l2'  = l2 → T).
Proof.
  intros T. split.
  - inv_hlist l => x0 xl0 Hf /=.
    injection 1 => Heq1 Heq2.
    apply existT_inj in Heq1. apply existT_inj in Heq2. subst.
    eapply Hf; reflexivity.
  - intros Hf x' l2' -> <- <-. apply Hf. done.
Qed.
Global Instance simpl_hmap_cons_and {A} {F G : A → Type} (f : ∀ x : A, F x → G x) (X : A) (Xs : list A) (x : G X) (l2 : hlist G Xs) (l : hlist F (X :: Xs)) :
  SimplAndRel eq (f +<$> l) (x +:: l2) (λ T : Prop,
    ∃ (x' : F X) (l2' : hlist F Xs), l = x' +:: l2' ∧ f _ x' = x ∧ f +<$> l2'  = l2 ∧ T).
Proof.
  intros T. split.
  - intros (x' & l2' & -> & <- & <- & HT). done.
  - intros (Ha & HT). inv_hlist l => x0 xl0 Ha.
    injection Ha => Heq1 Heq2. apply existT_inj in Heq1. apply existT_inj in Heq2. subst.
    eexists _, _. done.
Qed.

Global Instance simpl_and_list_lookup_total_unsafe {A} `{!Inhabited A} (l : list A) i (x : A) :
  SimplAndUnsafe (l !!! i = x) (λ T, l !! i = Some x ∧ T).
Proof.
  intros T [Hlook HT]. split; last done. by apply list_lookup_total_correct.
Qed.

Global Instance simpl_exist_hlist_nil {X} (F : X → Type) Q :
  SimplExist (hlist F []) Q (Q +[]).
Proof.
  rewrite /SimplExist. naive_solver.
Qed.
Global Instance simpl_exist_hlist_cons {X} (F : X → Type) (x : X) xs (Q : hlist F (x :: xs) → Prop) :
  SimplExist (hlist F (x :: xs)) Q (∃ p : F x, ∃ ps : hlist F xs, Q (p +:: ps)).
Proof.
  intros (p & ps & Hx). exists (p +:: ps). done.
Qed.
(* The instance for plist _ [] is built into Lithium's liExist *)
Global Instance simpl_exist_plist_cons {X} (F : X → Type) (x : X) xs (Q : plist F (x :: xs) → Prop) :
  SimplExist (plist F (x :: xs)) Q (∃ p : F x, ∃ ps : plist F xs, Q (p -:: ps)).
Proof.
  intros (p & ps & Hx). exists (p -:: ps). done.
Qed.

(* Instance that fires in case the product is hidden behind a definition, which the built-in Lithium support for pairs cannot see through. *)
Global Instance simpl_exist_prod {A B} (Q : A * B → Prop) :
  SimplExist (A * B) Q (∃ (a : A) (b : B), Q (a, b)).
Proof.
  intros (a & b & HQ). eauto.
Qed.

Global Instance simpl_forall_plist_cons {X} (F : X → Type) x xs T :
  SimplForall (plist F (x :: xs)) 1 T (∀ (a : F x) (s : plist F xs), T (a -:: s)).
Proof. intros Q [? ?]. apply Q. Qed.
Global Instance simpl_forall_plist_nil {X} (F : X → Type) T :
  SimplForall (plist F []) 0 T (T -[]).
Proof. intros Q []. apply Q. Qed.
Global Instance simpl_forall_hlist_cons {X} (F : X → Type) x xs T :
  SimplForall (hlist F (x :: xs)) 1 T (∀ (a : F x) (s : hlist F xs), T (a +:: s)).
Proof. intros Q a. inv_hlist a. intros. apply Q. Qed.
Global Instance simpl_forall_hlist_nil {X} (F : X → Type) T :
  SimplForall (hlist F []) 0 T (T +[]).
Proof. intros Q a. inv_hlist a. apply Q. Qed.


(** Try to find a lookup proof with some abstract condition [P] *)
Lemma simpl_list_lookup_assum {A} {P : nat → Prop} {E : nat → A} (l : list A) j x :
  (∀ i, P i → l !! i = Some (E i)) →
  CanSolve (P j) →
  SimplBothRel (=) (l !! j) (Some x) (x = E j).
Proof.
  unfold SimplBothRel, CanSolve, TCDone in *; subst.
  intros HL HP.
  apply HL in HP. rewrite HP. naive_solver.
Qed.
Global Hint Extern 50 (SimplBothRel (=) (?l !! ?j) (Some ?x) (_)) =>
  (* Important: we backtrack in case there are multiple matching facts in the context. *)
  match goal with
  | H : ∀ i, _ → l !! i = Some _ |- _ =>
      notypeclasses refine (simpl_list_lookup_assum l j x H _);
      apply _
  end : typeclass_instances.

Global Instance simpl_eq_PlaceIn {rt : RT} (n m : rt) : SimplBothRel (=) (A := place_rfn rt) (#n) (#m) (n = m).
Proof. split; naive_solver. Qed.
Global Instance simpl_eq_PlaceGhost {rt} (γ1 γ2 : gname) : SimplBothRel (=) (A := place_rfn rt) (PlaceGhost γ1) (PlaceGhost γ2) (γ1 = γ2).
Proof. split; naive_solver. Qed.

Global Instance simpl_replicate_eq' {A} (x x' : A) n n' :
  SimplAndUnsafe (replicate n x = replicate n' x') (λ b, n = n' ∧ x = x' ∧ b).
Proof.
  intros ? (-> & -> & ?). done.
Qed.

(*
Global Instance simpl_eq_OffsetSt `{!LayoutAlg} st i i' x : SimplAndUnsafe (x offsetst{st}ₗ i = x offsetst{st}ₗ i') (λ T, i = i' ∧ T).
Proof.
  intros T [-> ?]. done.
Qed.
 *)



Global Instance simpl_and_unsafe_apply_evar_right {A B} (f g : A → B) (a y : A) `{!IsProtected y} :
  SimplAndUnsafe (f a = g y) (λ T, a = y ∧ f = g ∧ T) | 1000.
Proof.
  rewrite /SimplAndUnsafe.
  intros T (<- & <- & HT).
  done.
Qed.
Global Instance simpl_and_unsafe_apply_evar_left {A B} (f g : A → B) (a y : A) `{!IsProtected y} :
  SimplAndUnsafe (f y = g a) (λ T, a = y ∧ f = g ∧ T) | 1000.
Proof.
  rewrite /SimplAndUnsafe.
  intros T (<- & <- & HT).
  done.
Qed.

Global Instance simpl_inj {A B} (f : A → B) x y :
  Inj (=) (=) f →
  SimplBothRel (=) (f x) (f y) (x = y).
Proof.
  intros ?. rewrite /SimplBothRel. naive_solver.
Qed.

(** Things for fallible ops *)
Global Typeclasses Opaque if_None if_Ok if_Some if_Err.
Global Instance simpl_both_if_ok_inl {A B} (x : A) P :
  SimplBoth (if_Ok (A:=A)(B:=B) (inl x) P) (P x).
Proof.
  rewrite /SimplBoth. naive_solver.
Qed.
Global Instance simpl_both_if_err_inr {A B} (x : B) P :
  SimplBoth (if_Err (A:=A)(B:=B) (inr x) P) (P x).
Proof.
  rewrite /SimplBoth. naive_solver.
Qed.
Global Instance simpl_both_if_some_some {A} (x : A) P :
  SimplBoth (if_Some (A:=A) (Some x) P) (P x).
Proof.
  rewrite /SimplBoth. naive_solver.
Qed.
Global Instance simpl_both_if_none_none {A} P :
  SimplBoth (if_None (A:=A) (None) P) (P).
Proof.
  rewrite /SimplBoth. naive_solver.
Qed.

Global Instance simplify_all_xtype `{!typeGS Σ} Q :
  SimplForall xtype 3 Q (∀ (rt : RT) (ty : type rt) (r : RT_xt rt), Q (mk_xtype (xtype_rt:=rt) ty r)).
Proof.
  intros ? []. done.
Qed.

(** ** Additional normalization instances *)
#[export] Hint Rewrite Nat.add_sub : lithium_rewrite.
#[export] Hint Rewrite Z.mul_1_l Z.mul_1_r Nat.mul_1_l Nat.mul_1_r : lithium_rewrite.

(** More automation for sets *)
Lemma difference_union_subseteq (E F H H': coPset):
  E ⊆ F →
  F ∖ H ∪ H' = F →
  (F ∖ H ∖ E) ∪ H' ∪ E = F.
Proof.
  set_unfold.
  intros ? Hcond x.
  specialize Hcond with x.
  split; first intuition.
  destruct (decide (x ∈ E)); intuition.
Qed.

Lemma difference_union_subseteq' (E F: coPset):
  E ⊆ F →
  F ∖ E ∪ E = F.
Proof.
  set_unfold.
  intros ? x.
  split; first intuition.
  destruct (decide (x ∈ E)); intuition.
Qed.

Lemma difference_union_comm (E E' A B: coPset):
  A ∪ E' ∪ E = B →
  A ∪ E ∪ E' = B.
Proof.
  set_solver.
Qed.

Global Hint Resolve difference_union_subseteq' | 30 : ndisj.
Global Hint Resolve difference_union_subseteq | 50 : ndisj.
Global Hint Resolve difference_union_comm | 80 : ndisj.


(* TODO move *)
Lemma eqdec_bool_eqb b1 b2 :
  bool_decide (b1 = b2) = eqb b1 b2.
Proof.
  destruct b1, b2; done.
Qed.
Hint Rewrite -> eqdec_bool_eqb : lithium_rewrite.

(* TODO move *)
Global Instance simpl_both_iff P1 P1' P2 :
  SimplBoth P1 P1' →
  SimplBothRel (iff) P1 P2 (P1' ↔ P2).
Proof.
  unfold SimplBoth, SimplBothRel.
  intros ->. done.
Qed.

Global Instance simpl_both_bool_decide_eq P `{Decision P} b :
  SimplBothRel (=) (bool_decide P) b (P ↔ b = true).
Proof.
  unfold SimplBothRel.
  case_bool_decide; destruct b; naive_solver.
Qed.

Global Instance simpl_both_orb_eq_true b1 b2 :
  SimplBothRel (=) (orb b1 b2) true (b1 = true ∨ b2 = true).
Proof.
  unfold SimplBothRel.
  destruct b1, b2; simpl; naive_solver.
Qed.

Global Instance simpl_both_or_l P1 P1' P2 :
  SimplBoth P1 P1' →
  SimplBoth (P1 ∨ P2) (P1' ∨ P2).
Proof.
  unfold SimplBoth. naive_solver.
Qed.
Global Instance simpl_both_or_r P1 P2 P2' :
  SimplBoth P2 P2' →
  SimplBoth (P1 ∨ P2) (P1 ∨ P2').
Proof.
  unfold SimplBoth. naive_solver.
Qed.

Global Instance simpl_both_and_l P1 P1' P2 :
  SimplBoth P1 P1' →
  SimplBoth (P1 ∧ P2) (P1' ∧ P2).
Proof.
  unfold SimplBoth. naive_solver.
Qed.
Global Instance simpl_both_and_r P1 P2 P2' :
  SimplBoth P2 P2' →
  SimplBoth (P1 ∧ P2) (P1 ∧ P2').
Proof.
  unfold SimplBoth. naive_solver.
Qed.

Global Instance simpl_both_eqrefl {A} (a : A) :
  SimplBothRel (=) a a True.
Proof.
  unfold SimplBothRel. naive_solver.
Qed.
Global Instance simpl_both_iff_true (P : Prop) :
  SimplBothRel (iff) True P P.
Proof.
  unfold SimplBothRel. naive_solver.
Qed.
