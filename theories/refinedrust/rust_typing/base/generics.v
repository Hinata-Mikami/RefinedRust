From refinedrust Require Import type.
From refinedrust Require Import options.

Definition prod_vec (A : Type) (n : nat) := plist id (replicate n A).
Definition list_to_tup {A} (l : list A) : prod_vec A (length l) := list_to_plist A l.

Fixpoint tup_to_list {A} n : prod_vec A n → list A :=
  match n with
  | 0 => λ _, []
  | S n =>
      λ '(hd *:: tl), hd :: tup_to_list n tl
  end.

(** ** Operations for partially instantiating the type parameters of a spec and introducing new lifetime/type parameters *)
(** We carefully setup these lemmas and definitions such that the equality rewrites reduce to eq_refl for any concrete application *)
Definition list_insert_shift {A} (l : list A) (n : nat) (x : A) :=
  take n l ++ [x] ++ drop n l.
Lemma list_insert_shift_delete_insert {A} (l : list A) (n : nat) (x : A) :
  Nat.leb (S n) (length l) = true →
  list_insert_shift (delete n l) n x = <[n := x]> l.
Proof.
  intros Hlen.
  rewrite /list_insert_shift.
  induction n as [ | n IH] in l, Hlen |-*; simpl; destruct l; simpl.
  - done.
  - done.
  - done.
  - by rewrite IH.
Defined.
Lemma list_insert_lookup_total {A} `{Inhabited A} (xs : list A) i :
  <[i := xs !!! i ]> xs = xs.
Proof.
  induction i as [ | i IH] in xs |-*; destruct xs; simpl; [done.. | ].
  by rewrite IH.
Defined.

Definition plist_insert_shift {X : Type} {F : X → Type} (Xl : list X) (pl : plist F Xl) (i : nat) (x : X) (fx : F x) : plist F (list_insert_shift Xl i x) :=
  papp (ptake _ pl i) (pcons fx (pdrop _ pl i)).
Import EqNotations.
Definition plist_replace {X : Type} {F : X → Type} (Xl : list X) (i : nat) (Hi : Nat.ltb i (length Xl) = true)
  (pl : plist F (delete i Xl)) (x : X) (fx : F x) : plist F (<[i := x]> Xl) :=
  rew (list_insert_shift_delete_insert _ _ _ Hi) in plist_insert_shift _ pl i x fx.
Definition plist_replace_here {X : Type} `{!Inhabited X} {F : X → Type} (Xl : list X) (i : nat) (Hi : Nat.ltb i (length Xl) = true)
  (pl : plist F (delete i Xl)) (fx : F (Xl !!! i)) : plist F Xl :=
  rew (list_insert_lookup_total _ _) in plist_replace Xl i Hi pl _ fx.

Local Instance inh_RT : Inhabited RT.
Proof.
  refine (populate _). refine (mk_RT (nat : Type) (nat : Type) id).
Qed.

(** Specifications *)
Class ScopeBindable `{!typeGS Σ} (S : Type) := mkScopeBindable {
  scope_add_typarams :
    ∀ rts : list RT, plist type rts → S → S;
  scope_add_elctx :
    (lft → elctx) → S → S;
}.

Definition spec_with `{!typeGS Σ} (lfts : nat) (rts : list RT) (SPEC : Type) :=
  prod_vec lft lfts → plist type rts → SPEC.
Arguments spec_with {_ _} / _ _ .

(*Notation "'spec!' κs ':' n '|' tys ':' rts ',' S" :=*)
  (*((fun κs tys => scope_add_typarams _ tys S) : spec_with n rts _) (at level 99, S at level 180, κs pattern, tys pattern) : stdpp_scope.*)
Notation "'spec!' κs ':' n '|' tys ':' rts ',' S" :=
  ((fun κs tys => S) : spec_with n rts _) (at level 99, S at level 180, κs pattern, tys pattern) : stdpp_scope.

Global Instance scope_bindable_nest `{!typeGS Σ} {S} `{!ScopeBindable S} lfts rts :
  ScopeBindable (spec_with lfts rts S) := {|
    scope_add_typarams rts' tys' s :=
      λ κs tys, (scope_add_typarams _ tys' (s κs tys));
    (*scope_add_lfts κs' s :=*)
      (*λ κs tys, (scope_add_lfts κs' (s κs tys));*)
    scope_add_elctx cstr s :=
      λ κs tys, (scope_add_elctx cstr (s κs tys));
  |}.

(** Instantiate a given type parameter *)
Definition spec_instantiate_typaram `{!typeGS Σ} {SPEC : Type} {lfts : nat} (rts : list RT)
  (n : nat)
  (Hn : Nat.ltb n (length rts) = true)
  (ty : type (rts !!! n))
  (F : spec_with lfts rts SPEC) :
  spec_with lfts (delete n rts) SPEC :=
  λ κs tys,
  F κs (plist_replace_here rts n Hn tys ty).

Definition spec_instantiate_typaram_fst `{!typeGS Σ} {SPEC : Type} {lfts : nat} (rt : RT) (rts : list RT)
  (ty : type rt)
  (F : spec_with lfts (rt :: rts) SPEC) :
  spec_with lfts rts SPEC :=
  λ κs tys,
  F κs (plist_replace_here (rt :: rts) 0 eq_refl tys ty).

(** Instantiate a given lifetime *)
Lemma replicate_length_transparent {A} (x : A) n :
  length (replicate n x) = n.
Proof.
  induction n as [ | n IH]; simpl; first done.
  by rewrite IH.
Defined.

Definition spec_instantiate_lft_fst `{!typeGS Σ} {SPEC : Type} {lfts : nat} (rts : list RT)
  (κ : lft)
  (F : spec_with (S lfts) rts SPEC) :
  spec_with lfts rts SPEC :=
  λ κs tys,
  F (κ -:: κs) tys.

(** Add a new type parameter *)
Definition spec_add_typaram `{!typeGS Σ} {SPEC : Type} {lfts : nat} (rts : list RT)
  (rt : RT) (st : syn_type)
  (F : type rt → spec_with lfts rts SPEC) :
  spec_with lfts (rt :: rts) SPEC :=
  λ κs '(ty *:: tys),
  F ty κs tys.


(** Collapse two levels of specification parameters *)
Lemma take_replicate_add_transparent {A} (x : A) n1 n2 :
  take n1 (replicate (n1 + n2) x) = replicate n1 x.
Proof.
  induction n1 as [ | n1 IH]; simpl; first done.
  by rewrite IH.
Defined.
Lemma take_app_transparent {A} (xs ys : list A) :
  take (length xs) (xs ++ ys) = xs.
Proof.
  induction xs as [ | x xs IH]; simpl; first done.
  by rewrite IH.
Defined.
Lemma drop_replicate_add_transparent {A} (x : A) n1 n2 :
  drop n1 (replicate (n1 + n2) x) = replicate n2 x.
Proof.
  induction n1 as [ | n1 IH]; simpl; first done.
  by rewrite IH.
Defined.
Lemma drop_app_transparent {A} (xs ys : list A) :
  drop (length xs) (xs ++ ys) = ys.
Proof.
  induction xs as [ | x xs IH]; simpl; first done.
  by rewrite IH.
Defined.

Definition spec_collapse_params `{!typeGS Σ} {SPEC : Type} {lfts1 lfts2 : nat} (rts1 rts2 : list RT)
  (F : spec_with lfts1 rts1 (spec_with lfts2 rts2 SPEC)) :
  spec_with (lfts1 + lfts2) (rts1 ++ rts2) SPEC :=
  λ κs tys,
  F
    (rew (take_replicate_add_transparent _ lfts1 lfts2) in ptake _ κs lfts1)
    (rew (take_app_transparent rts1 rts2) in ptake _ tys (length rts1))
    (rew (drop_replicate_add_transparent _ lfts1 lfts2) in pdrop _ κs lfts1 )
    (rew (drop_app_transparent rts1 rts2) in pdrop _ tys (length rts1)).


Definition spec_instantiated `{!typeGS Σ} {SPEC : Type} (F : spec_with 0 [] SPEC) : SPEC :=
  F -[] -[].

Notation "x '<TY>' T" := (spec_instantiate_typaram_fst _ _ T x) (left associativity, at level 81, only printing) : stdpp_scope.
Notation "x '<TY>@{' n '}' T" := (spec_instantiate_typaram _ n _ T x) (left associativity, at level 81, only printing) : stdpp_scope.
Notation "x '<LFT>' T" := (spec_instantiate_lft_fst _ T x) (left associativity, at level 81, only printing) : stdpp_scope.
#[warnings="-postfix-notation-not-level-1"]
Notation "x '<INST!>'" := (spec_instantiated x) (left associativity, at level 81, only printing) : stdpp_scope.
#[warnings="-postfix-notation-not-level-1"]
Notation "x '<MERGE!>'" := (spec_collapse_params _ _ x) (left associativity, at level 181, only printing) : stdpp_scope.


(* NOTE: these tactics also deal with the unfolded [spec_with] type, in order to deal well with [instantiate_spec_rec] in solvers.v *)
Notation "x '<TY>' T" := (
  ltac:(
    match type of x with
    | prod_vec _ _ → plist type ?rt → _ =>
        let rts := eval simpl in rt in
        match rts with
        | (?rt :: ?rts) =>
          refine (spec_instantiate_typaram_fst rt rts T x)
        end
    | spec_with _ ?rt _ =>
        let rts := eval simpl in rt in
        match rts with
        | (?rt :: ?rts) =>
          refine (@spec_instantiate_typaram_fst _ ltac:(apply _) _ _ rt rts T x)
        end
    | ?ty => idtac "<TY> failed with " ty
    end))
     (left associativity, at level 81, T constr at next level, only parsing) : stdpp_scope.

Notation "x '<TY>@{' n '}' T" := (
  ltac:(
    match type of x with
    | prod_vec _ _ → plist type ?rt → _ =>
        refine (spec_instantiate_typaram rt n eq_refl T x)
    | spec_with _ ?rt _ =>
        refine (@spec_instantiate_typaram _ ltac:(apply _) _ _ rt n eq_refl T x)
    | ?ty => idtac "<TY> failed with " ty
    end))
     (left associativity, at level 81, T constr at next level, only parsing) : stdpp_scope.

Notation "x '<LFT>' T" := (
  ltac:(
    match type of x with
    | prod_vec _ _ → plist type ?rts → _ =>
        refine (spec_instantiate_lft_fst rts T x)
    | spec_with _ ?rts _ =>
        refine (@spec_instantiate_lft_fst _ ltac:(apply _) _ _ rts T x)
    end))
     (left associativity, at level 81, T constr at next level, only parsing) : stdpp_scope.

#[warnings="-postfix-notation-not-level-1"]
Notation "x '<MERGE!>'" := (
  ltac:(
    match type of x with
    | prod_vec _ _ → plist type ?rts1 → prod_vec _ _ → plist type ?rts2 → _ =>
        refine (spec_collapse_params rts1 rts2 x)
    | spec_with _ ?rts1 (prod_vec _ _ → plist type ?rts2 → _) =>
        refine (spec_collapse_params rts1 rts2 x)
    | prod_vec _ _ → plist type ?rts1 → (spec_with _ ?rts2 _) =>
        refine (spec_collapse_params rts1 rts2 x)
    | spec_with _ ?rts1 (spec_with _ ?rts2 _) =>
        refine (spec_collapse_params rts1 rts2 x)
    end))
     (left associativity, at level 181, only parsing) : stdpp_scope.

Notation "<SIMPL> x" := (ltac:(let __x := eval simpl in (x) in refine __x)) (right associativity, at level 180, only parsing) : stdpp_scope.

#[warnings="-postfix-notation-not-level-1"]
Notation "x '<INST!>'" := (@spec_instantiated _ ltac:(apply _) _ x) (left associativity, at level 81, only parsing) : stdpp_scope.
#[warnings="-postfix-notation-not-level-1"]
Notation "x '<MERGE!>'" := (@spec_collapse_params _ ltac:(apply _) _ _ _ _ _ x) (left associativity, at level 181, only parsing) : stdpp_scope.

Lemma replicate_add_transparent {A} (n m : nat) (x : A) :
  replicate (n + m) x = replicate n x ++ replicate m x.
Proof.
  induction n as [ | ? IH]; simpl; first done.
  f_equiv. apply IH.
Defined.

Lemma rew_pcons {A : Type} {F : A → Type} {x : A} {xs ys : list A}
    (H : xs = ys) (fx : F x) (xl : plist F xs) :
  rew [plist F] f_equal (cons x) H in (fx -:: xl) =
    fx -:: (rew [plist F] H in xl).
Proof. destruct H. reflexivity. Qed.
Lemma rew_pcons_rev {A : Type} {F : A → Type} {x : A} {xs ys : list A}
    (H : xs = ys) (fx : F x) (xl : plist F ys) :
  rew <-[plist F] f_equal (cons x) H in (fx -:: xl) =
    fx -:: (rew <-[plist F] H in xl).
Proof. destruct H. reflexivity. Qed.

Lemma ptake_papp {A : Type} {F : A → Type} {xs ys : list A}
    (xl : plist F xs) (yl : plist F ys) :
  rew (take_app_transparent xs ys) in
    ptake _ (papp xl yl) (length xs) = xl.
Proof.
  induction xs as [ | x xs IH] in xl |-*; destruct xl.
  - destruct ys; destruct yl; cbn [ptake papp].
    all: match goal with
         | |- context[rew ?H in _] => rewrite (UIP_refl _ _ H)
         end; reflexivity.
  - rewrite (proof_irrelevance _ (take_app_transparent (x :: xs) ys)
      (f_equal (cons x) (take_app_transparent xs ys))).
    cbn [ptake papp]. rewrite rew_pcons. f_equal. apply IH.
Defined.
Lemma pdrop_papp {A : Type} {F : A → Type} {xs ys : list A}
    (xl : plist F xs) (yl : plist F ys) :
  rew (drop_app_transparent xs ys) in
    pdrop _ (papp xl yl) (length xs) = yl.
Proof.
  induction xs as [ | x xs IH] in xl |-*; destruct xl.
  - destruct ys; destruct yl; cbn [pdrop papp].
    all: match goal with
         | |- context[rew ?H in _] => rewrite (UIP_refl _ _ H)
         end; reflexivity.
  - rewrite (proof_irrelevance _ (drop_app_transparent (x :: xs) ys)
      (drop_app_transparent xs ys)).
    cbn [pdrop papp]. apply IH.
Defined.
Lemma ptake_replicate_papp {A : Type} n m
    (xl : prod_vec A n) (yl : prod_vec A m) :
  rew (take_replicate_add_transparent A n m) in
    ptake _
      (rew <-[plist id] (replicate_add_transparent n m A) in papp xl yl) n = xl.
Proof.
  induction n as [ | n IH] in xl |-*; destruct xl.
  - destruct m; destruct yl; cbn [ptake papp].
    all: repeat match goal with
         | |- context[rew ?H in _] => rewrite (UIP_refl _ _ H)
         end; reflexivity.
  - rewrite (proof_irrelevance _ (replicate_add_transparent (S n) m A)
      (f_equal (cons A) (replicate_add_transparent n m A))).
    rewrite rew_pcons_rev. cbn [ptake papp].
    rewrite (proof_irrelevance _ (take_replicate_add_transparent A (S n) m)
      (f_equal (cons A) (take_replicate_add_transparent A n m))).
    rewrite rew_pcons. f_equal. apply IH.
Defined.
Lemma pdrop_replicate_papp {A : Type} n m
    (xl : prod_vec A n) (yl : prod_vec A m) :
  rew (drop_replicate_add_transparent A n m) in
    pdrop _
      (rew <-[plist id] (replicate_add_transparent n m A) in papp xl yl) n = yl.
Proof.
  induction n as [ | n IH] in xl |-*; destruct xl.
  - destruct m; destruct yl; cbn [pdrop papp].
    all: repeat match goal with
         | |- context[rew ?H in _] => rewrite (UIP_refl _ _ H)
         end; reflexivity.
  - rewrite (proof_irrelevance _ (replicate_add_transparent (S n) m A)
      (f_equal (cons A) (replicate_add_transparent n m A))).
    rewrite rew_pcons_rev. cbn [pdrop papp].
    rewrite (proof_irrelevance _ (drop_replicate_add_transparent A (S n) m)
      (drop_replicate_add_transparent A n m)).
    apply IH.
Defined.


Record trait_spec_realization `{!typeGS Σ} (SPEC : Type) := mk_trait_spec_realization {
  trait_ctx_lfts : nat;
  trait_ctx_tys : list RT;

  trait_ctx_wf :
    prod_vec lft trait_ctx_lfts →
    plist type trait_ctx_tys →
    thread_id →
    iProp Σ;

  trait_ctx_wf_persistent :
    ∀ κs tys π, Persistent (trait_ctx_wf κs tys π);

  trait_ctx_spec :
    spec_with trait_ctx_lfts trait_ctx_tys SPEC;
}.
Global Arguments trait_ctx_lfts {_ _ _}.
Global Arguments trait_ctx_tys {_ _ _}.
Global Arguments trait_ctx_wf {_ _ _}.
Global Arguments trait_ctx_spec {_ _ _}.
Global Existing Instance trait_ctx_wf_persistent.

(* We don't want this to be simplify but stay symbolic *)
Global Arguments trait_ctx_wf : simpl never.


Program Definition trait_spec_realization_instantiate
    `{!typeGS Σ} {SPEC}
    (R : trait_spec_realization SPEC)
    (κs : prod_vec lft R.(trait_ctx_lfts))
    (tys : plist type R.(trait_ctx_tys)) :
    trait_spec_realization SPEC :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [];

    trait_ctx_wf :=
      λ _ _ π, R.(trait_ctx_wf) κs tys π;

    trait_ctx_spec :=
      λ _ _, R.(trait_ctx_spec) κs tys;
  |}.


Class TCInContext (T : Type) : Type := tc_in_context_witness : T.
Global Hint Mode TCInContext + : typeclass_instances.
Hint Extern 1 (TCInContext ?T) =>
  simpl;
  match goal with
  | H : ?T |- TCInContext ?T => exact H
  end : typeclass_instances.

(** These are singletons, so we can instantiate it *)
Global Instance simpl_exist_trait_spec_realization_lfts `{!typeGS Σ} SPEC (R : trait_spec_realization SPEC) `{Hlfts : !TCInContext (prod_vec lft R.(trait_ctx_lfts))}:
  SimplExist (prod_vec lft (trait_ctx_lfts R)) (λ T, T Hlfts).
Proof.
  intros e He. eauto.
Qed.
Global Instance simpl_exist_trait_spec_realization_tys `{!typeGS Σ} SPEC (R : trait_spec_realization SPEC) `{Hlfts : !TCInContext (plist type R.(trait_ctx_tys))}:
  SimplExist (plist type (trait_ctx_tys R)) (λ T, T Hlfts).
Proof.
  intros e He. eauto.
Qed.

(* Abstract over P for better unification *)
Global Instance trait_ctx_wf_intro_persistent' `{!typeGS Σ} SPEC (R : trait_spec_realization SPEC) κs tys π P :
  TCFastDone (P = (R.(trait_ctx_wf) κs tys π)) →
  IntroPersistent (R.(trait_ctx_wf) κs tys π) P.
Proof.
  intros ->.
  econstructor.
  iIntros "#Ha". done.
Qed.



Global Instance intro_persistent_all `{!typeGS Σ} {A} (Φ Ψ : A → iProp Σ) :
  (∀ x : A, IntroPersistent (Φ x) (Ψ x)) →
  IntroPersistent (∀ x : A, Φ x) (∀ x : A, Ψ x).
Proof.
  intros Ha.
  econstructor. iIntros "Ha" (x).
  destruct (Ha x) as [Hb].
  by iApply Hb.
Qed.
