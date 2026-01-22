From lithium Require Export base.
Set Default Proof Using "Type".

Global Unset Program Cases.
Global Set Keyed Unification.
Global Open Scope Z_scope.

Section induction.
  (* unary parametricity translation of lists to derive induction principles for rose-tree inductives *)
  Inductive list_is_list (A : Type) (PA : A → Type) : list A → Type :=
    | list_is_nil : list_is_list A PA []
    | list_is_cons : ∀ a : A, PA a → ∀ l : list A, list_is_list A PA l → list_is_list A PA (a :: l).

  Lemma list_is_list_full {A} (PA : A → Type) (l : list A) :
    (∀ a, PA a) → list_is_list A PA l.
  Proof.
    intros Hf. induction l; constructor; eauto.
  Defined.
End induction.

(* TODO move *)
Definition flip3 {A B C D} (f : A → B → C → D) : C → A → B → D :=
  λ c a b, f a b c.
Lemma Forall3_flip3 {A B C} (P : A → B → C → Prop) l1 l2 l3 :
  Forall3 P l1 l2 l3 ↔ Forall3 (flip3 P) l3 l1 l2.
Proof.
  induction l1 as [ | x l1 IH] in l2, l3 |-*; destruct l2 as [ | y l2]; destruct l3 as [ | z l3]; simpl;
    split; inversion 1; subst; econstructor; naive_solver.
Qed.
Lemma Forall3_Forall2_impl {A B C} (P : A → B → C → Prop) (Q : B → C → Prop) l1 l2 l3 :
  (∀ x y z, P x y z → Q y z) →
  Forall3 P l1 l2 l3 →
  Forall2 Q l2 l3.
Proof.
  intros Hi. induction l1 as [ | x l1 IH] in l2, l3 |-*; destruct l2 as [ | y l2]; destruct l3 as [ | z l3]; simpl;
    inversion 1; econstructor; naive_solver.
Qed.
Lemma Forall2_Forall_impl {A B} (P : A → B → Prop) (Q : B → Prop) l1 l2 :
  (∀ x y, P x y → Q y) →
  Forall2 P l1 l2 →
  Forall Q l2.
Proof.
  intros Hi. induction l1 as [ | x l1 IH] in l2 |-*; destruct l2 as [ | y l2]; simpl;
    inversion 1; econstructor; naive_solver.
Qed.

Lemma Forall2_cons_inv {A B} (P : A → B → Prop) l r x y :
  Forall2 P (x :: l) (y :: r) →
  P x y ∧ Forall2 P l r.
Proof.
  inversion 1; subst. done.
Qed.
Lemma Forall2_Forall {A B} P (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 → Forall (uncurry P) (zip l1 l2).
Proof. induction 1; constructor; auto. Qed.

(* Computable version of Forall2_cb that
  works well with the guardedness checker in the first argument list *)
Definition Forall2_cb {X Y : Type} (f : X → Y → Prop) :=
  fix rec (l1 : list X) (l2 : list Y) :=
    match l1, l2 with
    | [], [] => True
    | x :: l1, y :: l2 => f x y ∧ rec l1 l2
    | _, _ => False
    end.
Lemma Forall2_Forall2_cb {X Y} (f : X → Y → Prop) l1 l2 :
  Forall2 f l1 l2 ↔ Forall2_cb f l1 l2.
Proof.
  induction l1 as [ | x l1 IH] in l2 |-*; simpl; destruct l2 as [ | y l2].
  - apply Forall2_nil.
  - split; last done. apply Forall2_nil_cons_inv.
  - split; last done. apply Forall2_cons_nil_inv.
  - rewrite Forall2_cons. by rewrite IH.
Qed.

Lemma drop_app_length' {A} (l k : list A) n :
  length l = n → drop n (l ++ k) = k.
Proof. intros <-. apply drop_app_length. Qed.
Lemma take_app_length' {A} (l k : list A) n :
  length l = n → take n (l ++ k) = l.
Proof. intros <-. apply take_app_length. Qed.


(* TODO move *)
Lemma list_to_map_lookup_fst {A B} `{Countable A} (l : list (A * B)) k :
  k ∈ l.*1 →
  NoDup (l.*1) →
  ∃ v, list_to_map (M := gmap A B) l !! k = Some v.
Proof.
  induction l as [ | [k1 v1] l IH]; simpl.
  { intros []%elem_of_nil. }
  intros [-> | Ha]%elem_of_cons Hnodup.
  { exists v1. apply lookup_insert_eq. }
  inversion Hnodup as [ | ? ? Hnel Hnodup']; subst.
  opose proof* IH as Hb; [done | done | ].
  destruct Hb as (v & Hlook). exists v.
  rewrite lookup_insert_ne; first done.
  intros ->. apply Hnel. done.
Qed.

Lemma list_lookup_omap_inv {A B} (f : A → option B) (l : list A) i x :
  omap f l !! i = Some x → ∃ j y, l !! j = Some y ∧ f y = Some x.
Proof.
  induction l as [ | a l IH] in i, x |-*; simpl; first done.
  destruct (f a) as [y | ] eqn:Heq; first last.
  { intros (j & y & ? & ?)%IH. exists (S j), y. eauto. }
  rewrite lookup_cons. destruct i as [ | i].
  - intros [= ->]. exists 0%nat, a. rewrite lookup_cons. done.
  - intros (j & z & ? & ?)%IH. exists (S j), z. eauto.
Qed.




(* TODO move *)
Definition list_map_option {X Y} (f : X → option Y) (l : list X) : option (list Y) :=
  foldr (λ (x : X) (y : option (list Y)),
    y ← y;
    h ← f x;
    Some (h :: y)) (Some ([] : list Y)) l.
Lemma list_map_option_Some_length {X Y} (f : X → option Y) l l2 :
  list_map_option f l = Some l2 →
  length l = length l2.
Proof.
  induction l in l2 |-*; simpl; intros Heq; simplify_option_eq; naive_solver.
Qed.
Lemma list_map_option_alt {X Y} (f : X → option Y) xs ys :
  list_map_option f xs = Some ys ↔ Forall2 (λ x y, f x = Some y) xs ys.
Proof.
  induction xs as [ | x xs IH] in ys |-*; simpl.
  - split.
    + intros [= <-]. constructor.
    + inversion 1; done.
  - split.
    + intros (ys' & Hrec & Ha)%bind_Some.
      eapply bind_Some in Ha as (y & ? & [= <-]).
      constructor; first done. by eapply IH.
    + intros(y & ys' & Ha & Hrec & ->)%Forall2_cons_inv_l.
      erewrite (proj2 (IH _)); last done. rewrite Ha; done.
Qed.
Lemma list_map_option_lookup {X Y} (f : X → option Y) l l2 i x :
  list_map_option f l = Some l2 →
  l !! i = Some x →
  ∃ y, l2 !! i = Some y ∧ Some y = f x.
Proof.
  induction l as [ | a l IH] in l2, i |-*; simpl.
  - intros [= <-]. done.
  - intros Heq. apply bind_Some in Heq as (acc & Ha & Hx).
    apply bind_Some in Hx as (y & Hx & [= <-]).
    destruct i as [ | i]; simpl. { intros. simplify_option_eq. eauto. }
    intros Hb. eapply IH in Hb; last done. done.
Qed.
Lemma list_map_option_nil_inv_r {X Y} (f : X → option Y) l :
  list_map_option f l = Some [] → l = [].
Proof.
  destruct l as [ | x l]; first done.
  simpl. destruct (list_map_option f l); last done.
  simpl. destruct (f x); done.
Qed.
Lemma list_map_option_nil_inv_l {X Y} (f : X → option Y) l :
  list_map_option f [] = Some l → l = [].
Proof.
  simpl. injection 1 as [= <-]. done.
Qed.
Lemma list_map_option_cons_inv_r {X Y} (f : X → option Y) xs ys y :
  list_map_option f xs = Some (y :: ys) →
  ∃ x xs', xs = x :: xs' ∧ f x = Some y ∧ list_map_option f xs' = Some ys.
Proof.
  destruct xs as [ | x xs']; first done.
  simpl.
  destruct (list_map_option f xs') eqn:Heq; last done.
  simpl. destruct (f x) eqn:Heq2; last done.
  simpl. injection 1 as [= -> ->]. eauto.
Qed.
Lemma list_map_option_cons_inv_l {X Y} (f : X → option Y) x xs ys :
  list_map_option f (x :: xs) = Some ys →
  ∃ y ys', ys = y :: ys' ∧ f x = Some y ∧ list_map_option f xs = Some ys'.
Proof.
  simpl. destruct (list_map_option f xs) eqn:Heq; last done.
  simpl. destruct (f x) eqn:Heq2; last done.
  simpl. intros [= <-]. eauto.
Qed.

(* TODO: move *)
Lemma list_difference_nil_r {A} `{!EqDecision A} (x : list A) :
  list_difference x [] = x.
Proof.
  induction x as [ | x xs IH]; simpl; try done.
  rewrite IH. done.
Qed.
Lemma list_difference_app_r {A} `{!EqDecision A}  (x y1 y2 : list A) :
  list_difference x (y1 ++ y2) = list_difference (list_difference x y1) y2.
Proof.
  induction x as [ | x xs IH] in y1, y2 |-*; simpl; first done.
  destruct (decide_rel elem_of x (y1 ++ y2)) as [Hel | Hnel].
  - rewrite IH. apply elem_of_app in Hel.
    destruct (decide_rel elem_of x y1) as [Hel1 | Hel2]; first done.
    simpl. destruct Hel as [? | Hel]; first done.
    rewrite decide_True; done.
  - apply not_elem_of_app in Hnel as [Hnel1 Hnel2].
    rewrite decide_False; last done.
    simpl. rewrite decide_False; last done.
    by rewrite IH.
Qed.
Lemma list_difference_proper_r {A} `{!EqDecision A}  (x y1 y2 : list A) :
  y1 ≡ y2 →
  list_difference x y1 = list_difference x y2.
Proof.
  unfold equiv, set_equiv_instance.
  induction x as [ | x xs IH] in y1, y2 |-*; simpl; first done.
  intros Heq.
  destruct (decide_rel elem_of x y1) as [Hel1 | Hnel1].
  - rewrite decide_True; last naive_solver. by eapply IH.
  - rewrite decide_False; last naive_solver. f_equiv. by eapply IH.
Qed.
Lemma list_difference_diag {A} `{!EqDecision A} (x y : list A) :
  x ⊆ y → list_difference x y = [].
Proof.
  induction x as [ | x xs IH] in y |-*; first done.
  intros Hincl. simpl.
  destruct (decide_rel elem_of x y) as [Hel | Hnel].
  - apply IH. intros z Hel'. apply Hincl. set_solver.
  - exfalso; apply Hnel. apply Hincl. set_solver.
Qed.
Lemma list_difference_id {A} `{!EqDecision A} (x y : list A) :
  (∀ a, a ∈ x → a ∉ y) →
  list_difference x y = x.
Proof.
  induction x as [ | b x IH] in y |-*; simpl; first done.
  intros Hel.
  rewrite decide_False.
  - f_equiv. apply IH.
    intros ??. apply Hel. set_solver.
  - apply Hel. set_solver.
Qed.
Lemma list_difference_cons_elem {A} `{!EqDecision A} (l : list A) x :
  x ∈ l →
  NoDup l →
  x :: list_difference l [x] ≡ₚ l.
Proof.
  induction l as [ | y l IH] in x |-*; simpl; first set_solver.
  rewrite elem_of_cons NoDup_cons.
  intros [<- | Hel] [Hnel Hnd].
  - rewrite decide_True; last set_solver.
    f_equiv. rewrite list_difference_id; first done.
    intros ??. rewrite list_elem_of_singleton.
    intros <-. done.
  - rewrite decide_False.
    + rewrite Permutation_swap IH; done.
    + rewrite list_elem_of_singleton. set_solver.
Qed.
