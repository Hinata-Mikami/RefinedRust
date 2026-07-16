From Equations Require Import Equations.
From iris.bi Require Export fractional.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants na_invariants.
From radium Require Export proofmode notation.
From radium Require Import derived.
From lrust.lifetime Require Export frac_borrow.
From refinedrust Require Import int.
From refinedrust Require Export hlist.
From refinedrust Require Export base lft_contexts gvar_refinement type uninit_def.
From refinedrust Require Import options.

(* TODO move *)
Import EqNotations.
Lemma rew_UIP_RT {X : RT} (F : RT → Type) (Heq : X = X) (z : F X) :
  rew [F] Heq in z = z.
Proof. rewrite (UIP_refl _ _ Heq). done. Qed.
Lemma rew_UIP_RT' {X : RT} (F : RT → Type) (Heq : X = X) (z : F X) :
  rew <-[F] Heq in z = z.
Proof. rewrite (UIP_refl _ _ Heq). done. Qed.

(** * Place types *)

Section array.
  Context `{!typeGS Σ}.
  Section list_map.
    Context {K : Type} `{!EqDecision K}.
    Fixpoint lookup_iml {X} (iml: list (K * X)) (i : K) : option X :=
      match iml with
      | [] => None
      | (j, x) :: iml => if decide (i = j) then Some x else lookup_iml iml i
      end.

    Lemma lookup_iml_Some_iff {X} (iml : list (K * X)) i x :
      (∃ a, iml !! a = Some (i, x) ∧ (∀ b j y, b < a → iml !! b = Some (j, y) → j ≠ i)) ↔ lookup_iml iml i = Some x.
    Proof.
      induction iml as [ | [j y] iml IH] in i |-*; simpl.
      - split.
        + intros (? & Ha & _). rewrite lookup_nil in Ha. done.
        + intros [=].
      - split.
        + intros (a & Hlook & Hle). destruct a as [ | a].
          * simpl in *. injection Hlook as -> ->. rewrite decide_True; done.
          * simpl in *. destruct (decide(i = j)) as [<- | Hneq].
            { by opose proof* (Hle 0); [lia | done | done | ]. }
            eapply IH. eexists. split; first done. intros. eapply (Hle (S b)); last done. lia.
        + destruct (decide (i = j)) as [<- | Hneq].
          * intros [= ->]. exists 0. simpl. split; first done. intros. lia.
          * intros (a & Ha & Hleq)%IH. exists (S a).
            split; first done. intros ???? Hlook.
            destruct b; simpl in *. { congruence. }
            eapply Hleq; last done. lia.
    Qed.
    Lemma lookup_iml_None {X} (iml : list (K * X)) i :
      (∀ b j y, iml !! b = Some (j, y) → j ≠ i) ↔ lookup_iml iml i = None.
    Proof.
      induction iml as [ | [j y] iml IH] in i |-*; simpl.
      { split; first done. naive_solver. }
      split.
      - intros Ha. destruct (decide (i = j)) as [<- | ]; first last.
        { eapply IH. intros. eapply (Ha (S b)); done. }
        by opose proof* (Ha 0); [done | done | ].
      - destruct (decide (i = j)) as [<- | ]; first done.
        intros Ha b ??. destruct b as [ | b]; first (simpl; congruence).
        simpl. intros Hlook. eapply IH; done.
    Qed.

    Lemma lookup_iml_list_to_map {X} `{!Countable K} (l : list (K * X)) x y :
      NoDup l.*1 →
      lookup_iml l x = Some y ↔ (list_to_map l : gmap _ _) !! x = Some y.
    Proof.
      intros Hnd.
      rewrite -lookup_iml_Some_iff. split.
      - intros (a & Hlook & Hb).
        apply elem_of_list_to_map_1; first done.
        by eapply list_elem_of_lookup_2.
      - intros Ha%elem_of_list_to_map_2.
        apply list_elem_of_lookup_1 in Ha as (i & Hlook).
        exists i. split; first done.
        intros i' ?? ? Hlook'.
        intros ->.
        enough (i = i') by lia.
        eapply NoDup_lookup; first apply Hnd.
        + rewrite list_lookup_fmap Hlook//.
        + rewrite list_lookup_fmap Hlook'//.
    Qed.
    Lemma lookup_iml_list_to_map_eq {X} `{!Countable K} (l : list (K * X)) x :
      NoDup l.*1 →
      lookup_iml l x = (list_to_map l : gmap _ _) !! x.
    Proof.
      intros Hnd. destruct (lookup_iml l x) eqn:Heq.
      - apply lookup_iml_list_to_map in Heq; done.
      - rewrite -lookup_iml_None in Heq.
        symmetry. apply not_elem_of_list_to_map_1.
        intros Hel. apply list_elem_of_fmap_1 in Hel as ([] & -> & Hel).
        apply list_elem_of_lookup_1 in Hel as [i Hlook].
        apply Heq in Hlook. done.
    Qed.
  End list_map.

  (* Interpretation of an insertion list: from front to back. The same index may appear multiple times,
      then the first occurrence is what is relevant. *)
  Definition interpret_inserts {X} (iml : list (nat * X)) (ls : list X) : list X :=
    foldr (λ '(i, x) acc, <[i := x]> acc) ls iml.
  Definition interpret_iml {X} (def : X) (len : nat) (iml : list (nat * X)) : list X :=
    interpret_inserts iml (replicate len def).

  Lemma length_interpret_inserts {X} (iml : list (nat * X)) (ls : list X) :
    length (interpret_inserts iml ls) = length ls.
  Proof.
    induction iml as [ | [i x] iml IH]; simpl; first done.
    rewrite length_insert //.
  Qed.
  Lemma length_interpret_iml {X} (def : X) (len : nat) (iml : list (nat * X)) :
    length (interpret_iml def len iml) = len.
  Proof.
    rewrite /interpret_iml length_interpret_inserts length_replicate //.
  Qed.

  Lemma lookup_interpret_inserts_Some_inv {X} (iml : list (nat * X)) (ls : list X) i x :
    interpret_inserts iml ls !! i = Some x →
    ((i, x) ∈ iml) ∨ ls !! i = Some x.
  Proof.
    intros Ha. specialize (lookup_lt_Some _ _ _ Ha) as Hlen.
    induction iml as [ | [j y] iml IH] in i, Hlen, Ha |-*; simpl; first by eauto.
    move: Ha. simpl in *.
    rewrite length_insert in Hlen.
    destruct (decide (i = j)) as [ <- | Hneq].
    - rewrite list_lookup_insert_eq; last done.
      intros [= ->]. left. apply elem_of_cons. by left.
    - rewrite list_lookup_insert_ne; last done.
      intros Ha%IH; last done.
      destruct Ha as [ Ha| Ha].
      + left. rewrite elem_of_cons. by right.
      + right. done.
  Qed.
  Lemma lookup_interpret_iml_Some_inv {X} (iml : list (nat * X)) def len i x :
    interpret_iml def len iml !! i = Some x →
    i < len ∧ (x = def ∨ (i, x) ∈ iml).
  Proof.
    rewrite /interpret_iml. intros Ha.
    specialize (lookup_lt_Some _ _ _ Ha) as Hlen.
    rewrite length_interpret_inserts length_replicate in Hlen.
    split; first done.
    apply lookup_interpret_inserts_Some_inv in Ha as [ | Ha]; first by eauto.
    apply lookup_replicate_1 in Ha as [ ]. by left.
  Qed.

  Lemma lookup_interpret_inserts_1 {X} (iml : list (nat * X)) (ls : list X) i :
    lookup_iml iml i = None →
    interpret_inserts iml ls !! i = ls !! i.
  Proof.
    intros Ha. induction iml as [ | [j x] iml IH]; simpl in *; first done.
    destruct (decide (i = j)) as [<- | Hneq]; first done.
    rewrite list_lookup_insert_ne; last done. by eapply IH.
  Qed.
  Lemma lookup_interpret_inserts_Some_2 {X} (iml : list (nat * X)) (ls : list X) i x :
    i < length ls →
    lookup_iml iml i = Some x →
    interpret_inserts iml ls !! i = Some x.
  Proof.
    induction iml as [ | [j y] iml IH]; simpl; first done.
    intros Hlen Ha. destruct (decide (i = j)) as [<- | Hneq].
    - injection Ha as ->. rewrite list_lookup_insert_eq; first done.
      rewrite length_interpret_inserts //.
    - rewrite list_lookup_insert_ne; last done. by eapply IH.
  Qed.

  Lemma lookup_interpret_iml_Some_1 {X} (iml : list (nat * X)) (def : X) len i :
    lookup_iml iml i = None →
    i < len →
    interpret_iml def len iml !! i = Some def.
  Proof.
    intros Ha Hlen. rewrite lookup_interpret_inserts_1; last done.
    rewrite lookup_replicate; done.
  Qed.
  Lemma lookup_interpret_iml_None_1 {X} (iml : list (nat * X)) (def : X) len i :
    lookup_iml iml i = None →
    len ≤ i →
    interpret_iml def len iml !! i = None.
  Proof.
    intros Ha Hlen. rewrite lookup_interpret_inserts_1; last done.
    apply lookup_replicate_None; done.
  Qed.
  Lemma lookup_interpret_iml_Some_2 {X} (iml : list (nat * X)) (def : X) len i x :
    lookup_iml iml i = Some x →
    i < len →
    interpret_iml def len iml !! i = Some x.
  Proof.
    intros Ha Hlen. induction iml as [ | [j y] iml IH]; simpl; first done.
    simpl in *. destruct (decide (i = j)) as [<- | Hneq].
    - injection Ha as ->. rewrite list_lookup_insert_eq; first done.
      rewrite length_interpret_iml//.
    - rewrite list_lookup_insert_ne; last done. by apply IH.
  Qed.

  Lemma elem_of_interpret_iml_inv {X} (def : X) iml len x :
    x ∈ interpret_iml def len iml → x = def ∨ ∃ i, (i, x) ∈ iml.
  Proof.
    intros (i & Hel)%list_elem_of_lookup_1.
    apply lookup_interpret_iml_Some_inv in Hel as (? & [? | ?]); eauto.
  Qed.


  Lemma interpret_inserts_fmap {X Y} (f : X → Y) iml ls :
    interpret_inserts ((λ '(a, b), (a, f b)) <$> iml) (f <$> ls) =
    f <$> interpret_inserts iml ls.
  Proof.
    induction iml as [ | [i x] iml IH]; simpl; first done.
    rewrite list_fmap_insert. f_equiv. by apply IH.
  Qed.
  Lemma interpret_iml_fmap {X Y} (f : X → Y) (def : X) len iml :
    interpret_iml (f def) len ((λ '(a, b), (a, f b)) <$> iml) =
    f <$> interpret_iml def len iml.
  Proof.
    rewrite /interpret_iml -interpret_inserts_fmap.
    rewrite fmap_replicate. done.
  Qed.

  Lemma interpret_inserts_nil {X} (iml : list (nat * X)) :
    interpret_inserts iml [] = [].
  Proof.
    induction iml as [ | [] iml IH]; simpl; first done.
    rewrite IH. done.
  Qed.
  Lemma interpret_iml_0 {X} (def : X) (iml : list (nat * X)) :
    interpret_iml def 0 iml = [].
  Proof.
    rewrite /interpret_iml. rewrite interpret_inserts_nil//.
  Qed.

  Fixpoint cut_iml {X} (iml : list (nat * X)) : list (nat * X) :=
    match iml  with
    | [] => []
    | (0, x) :: iml => cut_iml iml
    | (S i, x) :: iml => (i, x) :: cut_iml iml
    end.

  Lemma interpret_inserts_cons {X} (iml : list (nat * X)) h (l : list _) :
    interpret_inserts iml (h :: l) =
    (match lookup_iml iml 0 with | Some a => a | _ => h end) :: interpret_inserts (cut_iml iml) l.
  Proof.
    induction iml as [ | [i x] iml IH] in h, l |-*; simpl; first done.
    rewrite IH. destruct i as [ | i]; simpl; done.
  Qed.
  Lemma interpret_iml_succ {X} len (def : X) (iml : list (nat * X)) :
    interpret_iml def (S len) iml =
    (match lookup_iml iml 0 with | Some a => a | _ => def end) :: interpret_iml def len (cut_iml iml).
  Proof.
    rewrite /interpret_iml/=. rewrite interpret_inserts_cons//.
  Qed.

  Lemma insert_interpret_iml {X} (def : X) (len : nat) (iml : list (nat * X)) i x :
    <[i := x]> (interpret_iml def len iml) = interpret_iml def len ((i, x) :: iml).
  Proof. done. Qed.
End array.

(** ** Place types *)

(** bor_kind *)
Section ltype.
Context `{typeGS Σ}.

(**
  A [bor_kind] determines which ownership we have of an ltype.
  [Owned] says that we fully own it.
  [Shared κ] says that we have shared ownership at lifetime κ.
  [Uniq κ γ] says that we own it under a mutable borrow at lifetime κ, where γ is the ghost variable for the mutable reference. This is needed for properly nesting the refinements of mutable references.
 *)
Inductive bor_kind :=
 | Owned | Shared (κ : lft) | Uniq (κ : lft) (γ : gname).
Global Instance bor_kind_inhabited : Inhabited bor_kind := populate (Owned).

Definition lctx_bor_kind_alive (E : elctx) (L : llctx) (b : bor_kind) :=
  match b with
  | Owned => True
  | Shared κ | Uniq κ _ => lctx_lft_alive E L κ
  end.

(** ** Inclusion of bor_kinds *)
Definition bor_kind_direct_incl (b1 b2 : bor_kind) : iProp Σ :=
  match b1, b2 with
  | Owned, Owned => True
  | Uniq κ1 γ1, Uniq κ2 γ2 => κ1 ⊑ κ2 ∗ ⌜γ1 = γ2⌝
  | Shared κ1, Shared κ2 => κ1 ⊑ κ2
  | _, _ => False
  end.
Arguments bor_kind_direct_incl : simpl nomatch.
Infix "⊑ₛₖ" := bor_kind_direct_incl (at level 70) : bi_scope.

Definition bor_kind_outlives_elctx (b : bor_kind) (κ : lft) : elctx :=
  match b with
  | Owned => []
  | Uniq κ' _ => [κ ⊑ₑ κ']
  | Shared κ' => [κ ⊑ₑ κ']
  end.

(** Direct inclusion *)
Global Instance bor_kind_direct_incl_pers b1 b2 : Persistent (b1 ⊑ₛₖ b2).
Proof. destruct b1, b2; apply _. Qed.

Lemma bor_kind_direct_incl_refl b:
  ⊢ (b ⊑ₛₖ b)%I.
Proof.
  destruct b; simpl.
  - eauto.
  - iApply lft_incl_refl.
  - iSplit; last done. iApply lft_incl_refl.
Qed.
Lemma bor_kind_direct_incl_trans b1 b2 b3 :
  ⊢ (b1 ⊑ₛₖ b2 -∗ b2 ⊑ₛₖ b3 -∗ b1 ⊑ₛₖ b3)%I.
Proof.
  destruct b1, b2, b3; simpl; first [iIntros "-> ->" | iIntros "[#? ->] [#? ->]" | iIntros "#?? //"].
  - by iApply lft_incl_trans.
  - iSplit; last done. by iApply lft_incl_trans.
Qed.

Definition lctx_bor_kind_direct_incl (E : elctx) (L : llctx) b b' : Prop :=
  ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ b ⊑ₛₖ b').

Lemma lctx_bor_kind_direct_incl_use E L b1 b2 :
  lctx_bor_kind_direct_incl E L b1 b2 →
  elctx_interp E -∗
  llctx_interp L -∗
  b1 ⊑ₛₖ b2.
Proof.
  iIntros (Hincl) "HE HL".
  iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
  by iPoseProof (Hincl with "HL HE") as "Ha".
Qed.

End ltype.
Infix "⊑ₛₖ" := bor_kind_direct_incl (at level 70) : bi_scope.
Global Arguments bor_kind_direct_incl : simpl never.

Section ltype_def.
  Context `{typeGS Σ}.
  Implicit Type (rt : RT).

  Implicit Types
    (κ : lft)
    (k : bor_kind)
    (l : loc)
    (π : thread_id)
  .

  (** ** Definition *)
  (** ltypes are Type-indexed by their refinement type.
    However, defining this directly makes it hard to define an induction principle on them,
    so we first define a separate version [lty] that is not indexed, but rather Type-equalities when using them,
     and later on define [ltype], which exposes [lty_rt] as in index, on top. *)
  Record enum_lty_variant_pre (L : Type) := mk_enum_lty_variant {
    elv_tag : var_name;
    elv_rt : RT;
    elv_lty : L;
    elv_rfn : elv_rt;
  }.
  Global Arguments mk_enum_lty_variant {_} _ _ _ _.
  Global Arguments elv_tag {_} _.
  Global Arguments elv_rt {_} _.
  Global Arguments elv_lty {_} _.
  Global Arguments elv_rfn {_} _.

  Inductive lty : Type :=
    | BlockedLty {rt} (t : type rt) (κ : lft)
    | ShrBlockedLty {rt} (t : type rt) (κ : lft)
    | OfTyLty {rt} (t : type rt)
    (* AliasLty is polymorphic in the refinement type -- it accepts any refinement *)
    | AliasLty (rt : RT) (st : syn_type) (l : loc)
    | MutLty (lt : lty) (κ : lft)
    | ShrLty (lt : lty) (κ : lft)
    | StructLty (lts : list lty) (sls : struct_layout_spec)
    (* [def] is the default element type; [lts] masks this for certain indices *)
    | ArrayLty {rt} (def : type rt) (len : nat) (lts : list (nat * lty))
    (* [en] is the enum spec. [variant] optionally overrides one variant's data
       type/refinement; other variants use their canonical payload. *)
    | EnumLty {rt : RT} (en : enum rt) (variant : option (enum_lty_variant_pre lty))
    | OpenedLty
        (* NOTE: we parameterize over the refinement types here,
           as we don't have support for induction-recursion in Coq to define [lty_rfn] mutually.
           The ownership predicate will require that they are equal to the actual refinement types. *)
        (** [lt_cur] is the currently owned ltype here.
            [lt_inner] is the condition on when we can fold again: the core of [lt_cur] needs to be equivalent to [lt_inner].
            [ty_full] is the type describing the original ownership. It needs to be a type to formulate the Uniq case.
           (we might be able to lift this restriction by having equations that unfold applicable ltypes from Uniq to Owned, exposing the borrow in the process) *)
        {rt_inner rt_full : RT}
        (lt_cur : lty) (lt_inner : lty) (lt_full : lty)
        (Cpre : rt_inner → rt_full → iProp Σ)
        (Cpost : rt_inner → rt_full → iProp Σ)
    | CoreableLty
        (** gives us [lt_full] after all [κs] are dead; with no currently accessible ownership *)
        (* TODO think about how we can unify this with BlockedLtype *)
        (κs : list lft)
        (lt_full : lty)
    | ShadowedLty {rt : RT} (lt_cur : lty) (r_cur : place_rfn rt) (lt_full : lty)
    | OpenedNaLty
        {rt_inner : RT}
        (lt_cur : lty) (lt_inner : lty)
        (Cpre : rt_inner → iProp Σ)
        (Cpost : rt_inner → iProp Σ)
  .

  Definition enum_lty_variant := enum_lty_variant_pre lty.

  Definition enum_lty_variant_forall (P : lty → Type)
      (ov : option enum_lty_variant) : Type :=
    match ov with
    | Some v => P v.(elv_lty)
    | None => unit
    end.

  Definition enum_lty_variant_forall_prop (P : lty → Prop)
      (ov : option enum_lty_variant) : Prop :=
    match ov with
    | Some v => P v.(elv_lty)
    | None => True
    end.

  Global Instance into_ih_enum_lty_variant_forall_prop {PROP : bi}
      (φ : lty → Prop) ov (Δ : envs PROP) (Φ : lty → PROP) :
    (∀ lt, IntoIH (φ lt) Δ (Φ lt)) →
    IntoIH (enum_lty_variant_forall_prop φ ov) Δ
      (match ov with
       | Some v => □ Φ v.(elv_lty)
       | None => True
       end)%I | 2.
  Proof.
    rewrite /IntoIH=> HΔ. destruct ov as [v | ]; simpl.
    - intros Hφ. apply bi.intuitionistically_intro'. by apply HΔ.
    - intros _. apply bi.True_intro.
  Qed.

  Definition canonical_enum_lty_variant {rt : RT} (en : enum rt) (r : rt) :
      enum_lty_variant :=
    mk_enum_lty_variant
      (enum_tag' en r)
      (enum_rt en r)
      (OfTyLty (enum_ty en r))
      (enum_r en r).

  Definition interp_enum_lty_variant {rt : RT} (en : enum rt)
      (ov : option enum_lty_variant) (r : rt) : enum_lty_variant :=
    match ov with
    | Some v => if decide (enum_tag en r = Some v.(elv_tag)) then v
        else canonical_enum_lty_variant en r
    | None => canonical_enum_lty_variant en r
    end.

  Lemma interp_enum_lty_variant_None {rt : RT} (en : enum rt) r :
    interp_enum_lty_variant en None r = canonical_enum_lty_variant en r.
  Proof. done. Qed.
  Lemma interp_enum_lty_variant_Some_match {rt : RT} (en : enum rt) r v :
    enum_tag en r = Some v.(elv_tag) →
    interp_enum_lty_variant en (Some v) r = v.
  Proof. intros Htag. rewrite /interp_enum_lty_variant decide_True //. Qed.
  Lemma interp_enum_lty_variant_Some_mismatch {rt : RT} (en : enum rt) r v :
    enum_tag en r ≠ Some v.(elv_tag) →
    interp_enum_lty_variant en (Some v) r = canonical_enum_lty_variant en r.
  Proof. intros Htag. rewrite /interp_enum_lty_variant decide_False //. Qed.

  Definition enum_lty_variant_tag_compat {rt : RT} (en : enum rt)
      (r : rt) (v : enum_lty_variant) : Prop :=
    enum_tag en r = Some v.(elv_tag).

  Definition enum_lty_variant_payload_compat {rt : RT} (en : enum rt)
      (r : rt) (v : enum_lty_variant) : Prop :=
    ∃ Heq : RT_rt (enum_rt en r) = RT_rt v.(elv_rt),
      rew [id] Heq in enum_r en r = v.(elv_rfn).

  Definition enum_lty_variant_compat {rt : RT} (en : enum rt)
      (r : rt) (v : enum_lty_variant) : Prop :=
    enum_lty_variant_tag_compat en r v ∧
    enum_lty_variant_payload_compat en r v.

  Lemma canonical_enum_lty_variant_tag_compat {rt : RT} (en : enum rt) r tag :
    enum_tag en r = Some tag →
    enum_lty_variant_tag_compat en r (canonical_enum_lty_variant en r).
  Proof.
    rewrite /enum_lty_variant_tag_compat /canonical_enum_lty_variant /enum_tag'.
    intros ->. done.
  Qed.
  Lemma canonical_enum_lty_variant_payload_compat {rt : RT} (en : enum rt) r :
    enum_lty_variant_payload_compat en r (canonical_enum_lty_variant en r).
  Proof. exists eq_refl. done. Qed.

  (*
  Basic setup for augmenting these with place_rfns:
      - since we move down the interpretation of ownership by one level anyways,
        we also handle the interpretation of place_rfn for a particular place there,
        one level down (for the respective place)
      - this enables us to state ownership of the gvar_obs of the outer mut ref (one above) depending on the state of the place owned by the reference.
        i.e.:
          - for blocked this is quite clear, we want to link up the outer reference with the inner reference.
          - for other places, this controls the presence of the gvar_obs fragment/what we know about the inner refinement
   *)

  Fixpoint lty_rt (lt : lty) {struct lt} : RT :=
    match lt with
    | @BlockedLty rt _ _ => rt
    | @ShrBlockedLty rt _ _ => rt
    | @OfTyLty rt _ => rt
    | AliasLty rt st l => rt
    | MutLty lt _ => (place_rfnRT (lty_rt lt) * gname)%type
    | ShrLty lt _ => place_rfnRT (lty_rt lt)
    | StructLty lts _ =>
        plistRT (fmap lty_rt lts)
    | @ArrayLty rt def len lts => list (place_rfnRT rt)
    | @EnumLty rt en variant => rt
    | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
        lty_rt lt_cur
    | CoreableLty κ lt_full =>
        lty_rt lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        lty_rt lt_full
    | OpenedNaLty lt_cur _ _ _ =>
        lty_rt lt_cur
    end.

  Fixpoint lty_st (lt : lty) : syn_type :=
    match lt with
    | BlockedLty ty _ => ty.(ty_syn_type) MetaNone
    | ShrBlockedLty ty _ => ty.(ty_syn_type) MetaNone
    | OfTyLty ty => ty.(ty_syn_type) MetaNone
    | AliasLty _ st l => st
    | MutLty _ _ => PtrSynType
    | ShrLty _ _ => PtrSynType
    | StructLty _ sls => sls
    | ArrayLty def len lts => ArraySynType (ty_syn_type def MetaNone) len
    | EnumLty en variant => en.(enum_els)
    | OpenedLty lt_cur _ _ _ _ => lty_st lt_cur
    | CoreableLty _ lt_full =>
        lty_st lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        lty_st lt_full
    | OpenedNaLty lt_cur _ _ _ =>
        lty_st lt_cur
    end.

  Fixpoint lty_wf (lt : lty) : Prop :=
    match lt with
    | BlockedLty _ _ => True
    | ShrBlockedLty _ _ => True
    | OfTyLty _ => True
    | AliasLty _ st l => True
    | MutLty lt κ => lty_wf lt
    | ShrLty lt _ => lty_wf lt
    | StructLty lts _ => Forall_cb lty_wf lts
    | @ArrayLty rt def len lts =>
        Forall_cb (λ '(i, lt), lty_wf lt ∧ lty_rt lt = rt(*∧ i < len *)) lts
    | @EnumLty rt en variant =>
        match variant with
        | Some v => lty_wf v.(elv_lty) ∧ lty_rt v.(elv_lty) = v.(elv_rt)
        | None => True
        end
    | @OpenedLty rt_inner rt_full lt_cur lt_inner lt_full _ _ =>
        (* require that the refinements actually match *)
        rt_inner = lty_rt lt_inner ∧ rt_full = lty_rt lt_full ∧ lty_wf lt_cur ∧ lty_wf lt_inner ∧ lty_wf lt_full
        (*∧ lty_st lt_inner = lty_st lt_full ∧ lty_st lt_cur = lty_st lt_full*)
    | CoreableLty _ lt =>
        lty_wf lt
    | @ShadowedLty rt_cur lt_cur r_cur lt_full =>
        lty_wf lt_cur ∧ lty_wf lt_full ∧ lty_rt lt_cur = rt_cur
    | @OpenedNaLty rt_inner lt_cur lt_inner _ _ =>
        rt_inner = lty_rt lt_inner ∧ lty_wf lt_cur ∧ lty_wf lt_inner
    end.


  (* induction principle loosely based on unary parametricity *)
  Lemma lty_recursor :
    ∀ P : lty → Type,
      (∀ (rt : RT) (t : type rt), ∀ κ : lft, P (BlockedLty t κ)) →
      (∀ (rt : RT) (t : type rt), ∀ κ : lft, P (ShrBlockedLty t κ)) →
      (∀ (rt : RT) (t : type rt), P (OfTyLty t)) →
      (∀ (rt : RT) (st : syn_type) (l : loc), P (AliasLty rt st l)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (MutLty lt κ)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (ShrLty lt κ)) →
      (∀ lts : list lty, list_is_list lty P lts → ∀ sls : struct_layout_spec, P (StructLty lts sls)) →
      (∀ (rt : RT) (def : type rt) (len : nat) (lts : list (nat * lty)),
        list_is_list _ (λ '(_, lt), P lt) lts → P (ArrayLty def len lts)) →
      (∀ (rt : RT) (en : enum rt) (variant : option enum_lty_variant),
        enum_lty_variant_forall P variant → P (EnumLty en variant)) →
      (∀ (rt_inner rt_full : RT) (lt_cur lt_inner lt_full : lty)
        (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ),
          P lt_cur → P lt_inner → P lt_full → P (OpenedLty lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ κs (lt_full : lty), P lt_full → P (CoreableLty κs lt_full)) →
      (∀ (rt_cur : RT) (lt_cur : lty) (r_cur : place_rfn rt_cur) (lt_full : lty), P lt_cur → P lt_full → P (ShadowedLty lt_cur r_cur lt_full)) →
      (∀ (rt_inner : RT) (lt_cur lt_inner : lty)
        (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ),
          P lt_cur → P lt_inner → P (OpenedNaLty lt_cur lt_inner Cpre Cpost)) →
      ∀ lt : lty, P lt.
  Proof.
    intros P Hblocked Hshrblocked Hofty Halias Hmut Hshr Hstruct Harr Henum Hopened Hcoreable Hshadow Hopened_na.
    (* doing induction does not give us the IH *)
    refine (fix IH (lt : lty) {struct lt} : P lt :=
      match lt return (P lt) with
      | BlockedLty t κ => Hblocked _ t κ
      | ShrBlockedLty t κ => Hshrblocked _ t κ
      | OfTyLty t => Hofty _ t
      | AliasLty rt st l => Halias rt st l
      | MutLty lt κ => Hmut lt _ κ
      | ShrLty lt κ => Hshr lt _ κ
      | StructLty lts sls =>
          _
      | @ArrayLty rt def len lts =>
          _
      | EnumLty en variant =>
          _
      | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
          _
      | CoreableLty κ lt_full =>
          _
      | ShadowedLty lt_cur r_cur lt_full =>
          _
      | OpenedNaLty _ _ _ _ =>
          _
      end); [apply IH.. | | | | | | | ].
      - apply Hstruct.
        apply list_is_list_full.
        apply IH.
      - apply Harr. apply list_is_list_full. intros []. apply IH.
      - apply Henum. destruct variant as [v | ]; simpl; [apply IH | exact tt].
      - apply Hopened; apply IH.
      - apply Hcoreable; apply IH.
      - apply Hshadow; apply IH.
      - apply Hopened_na; apply IH.
  Defined.

  Lemma lty_induction :
    ∀ P : lty → Prop,
      (∀ (rt : RT) (t : type rt), ∀ κ : lft, P (BlockedLty t κ)) →
      (∀ (rt : RT) (t : type rt), ∀ κ : lft, P (ShrBlockedLty t κ)) →
      (∀ (rt : RT) (t : type rt), P (OfTyLty t)) →
      (∀ (rt : RT) (st : syn_type) (l : loc), P (AliasLty rt st l)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (MutLty lt κ)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (ShrLty lt κ)) →
      (∀ lts : list lty, (∀ lt, lt ∈ lts → P lt) → ∀ sls : struct_layout_spec, P (StructLty lts sls)) →
      (∀ (rt : RT) (def : type rt) (len : nat) (lts : list (nat * lty)), (∀ i lt, (i, lt) ∈ lts → P lt) → P (ArrayLty def len lts)) →
      (∀ (rt : RT) (en : enum rt) (variant : option enum_lty_variant), enum_lty_variant_forall_prop P variant → P (EnumLty en variant)) →
      (∀ (rt_inner rt_full : RT) (lt_cur lt_inner lt_full : lty)
        (Cpre : rt_inner → rt_full → iProp Σ) (Cpost : rt_inner → rt_full → iProp Σ),
          P lt_cur → P lt_inner → P lt_full → P (OpenedLty lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ κs (lt_full : lty), P lt_full → P (CoreableLty κs lt_full)) →
      (∀ (rt_cur : RT) (lt_cur : lty) (r_cur : place_rfn rt_cur) (lt_full : lty), P lt_cur → P lt_full → P (ShadowedLty lt_cur r_cur lt_full)) →
      (∀ (rt_inner : RT) (lt_cur lt_inner : lty)
        (Cpre : rt_inner → iProp Σ) (Cpost : rt_inner → iProp Σ),
          P lt_cur → P lt_inner → P (OpenedNaLty lt_cur lt_inner Cpre Cpost)) →
      ∀ lt : lty, P lt.
  Proof.
    intros P ? ? ? ? ? ? Hstruct Harr Henum Hopened Hcoreable Hshadow Hopened_na lt.
    induction lt as [ | | | | | | lts IH sls | rt def len lts IH | | | | | ] using lty_recursor; [by eauto.. | | | | | | | ].
    - eapply Hstruct. intros lt Hin. induction lts as [ | lt' lts IH'].
      + apply elem_of_nil in Hin. done.
      + inversion IH; subst. apply elem_of_cons in Hin as [<- | Hin]; first done.
        by apply IH'.
    - eapply Harr.
      intros i lt Hin. induction lts as [ | [j lt'] lts IH'].
      + apply elem_of_nil in Hin. done.
      + inversion IH; subst. apply elem_of_cons in Hin as [ [= <- <-] | Hin]; first done.
        by apply IH'.
    - eapply Henum. destruct variant as [v | ]; simpl in *; done.
    - eapply Hopened; eauto.
    - eapply Hcoreable; eauto.
    - eapply Hshadow; eauto.
    - eapply Hopened_na; eauto.
  Qed.

  (** Stronger induction principle for the OpenedLtype case, but requires well-formedness. *)
  Lemma lty_induction_wf :
    ∀ P : lty → Prop,
      (∀ (rt : RT) (t : type rt), ∀ κ : lft, P (BlockedLty t κ)) →
      (∀ (rt : RT) (t : type rt), ∀ κ : lft, P (ShrBlockedLty t κ)) →
      (∀ (rt : RT) (t : type rt), P (OfTyLty t)) →
      (∀ (rt : RT) (st : syn_type) (l : loc), P (AliasLty rt st l)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (MutLty lt κ)) →
      (∀ lt : lty, P lt → ∀ κ : lft, P (ShrLty lt κ)) →
      (∀ lts : list lty, (∀ lt, lt ∈ lts → P lt) → ∀ sls : struct_layout_spec, P (StructLty lts sls)) →
      (∀ (rt : RT) (def : type rt) (len : nat) (lts : list (nat * lty)),
        (∀ i lt, (i, lt) ∈ lts → P lt ∧ lty_rt lt = rt) → P (ArrayLty def len lts)) →
      (∀ (rt : RT) (en : enum rt) (variant : option enum_lty_variant),
        match variant with
        | Some v => P v.(elv_lty) ∧ lty_rt v.(elv_lty) = v.(elv_rt)
        | None => True
        end → P (EnumLty en variant)) →
      (∀ (lt_cur lt_inner lt_full : lty) (Cpre : (lty_rt lt_inner) → lty_rt lt_full → iProp Σ)
        (Cpost : (lty_rt lt_inner) → (lty_rt lt_full) → iProp Σ),
          P lt_cur → P lt_inner → P lt_full → P (OpenedLty lt_cur lt_inner lt_full Cpre Cpost)) →
      (∀ κs (lt_full : lty), P lt_full → P (CoreableLty κs lt_full)) →
      (∀ (lt_cur : lty) (r_cur : place_rfn (lty_rt lt_cur)) (lt_full : lty),
        P lt_cur → P lt_full → P (ShadowedLty lt_cur r_cur lt_full)) →
      (∀ (lt_cur lt_inner : lty) (Cpre : lty_rt lt_inner → iProp Σ) (Cpost : lty_rt lt_inner → iProp Σ),
        P lt_cur → P lt_inner → P (OpenedNaLty lt_cur lt_inner Cpre Cpost)) →
      ∀ lt : lty, lty_wf lt → P lt.
  Proof.
    intros P ?????? Hstruct Harr Henum Hopened Hcoreable Hshadow Hopened_na lt Hwf.
    induction lt as [ | | | | | | lts IH sls | rt def len lts IH | rt en variant IH | rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost IH1 IH2 IH3 | κ lt_full IH | | ] using lty_induction; [by eauto.. | | | | | | | ].
    - eapply Hstruct. intros lt Hlt. eapply IH; first done.
      simpl in Hwf. apply Forall_Forall_cb in Hwf.
      eapply Forall_forall; done.
    - simpl in Hwf. eapply Harr.
      intros i lt Hin.
      simpl in Hwf. apply Forall_Forall_cb in Hwf.
      eapply Forall_forall in Hwf; last apply Hin.
      destruct Hwf as (? & ?). split_and!; [ | done..].
      eapply IH; done.
    - simpl in Hwf. eapply Henum.
      destruct variant as [v | ]; simpl in *; last done.
      destruct Hwf as (Hwf & Hrt). split; last done.
      apply IH. apply Hwf.
    - destruct Hwf as (Heq1 & Heq2 & Hcur & Hinner & Hfull ). subst.
      eapply Hopened; eauto.
    - eapply Hcoreable; eauto.
    - destruct Hwf as (? & ? & <-).
      eapply Hshadow; eauto.
    - destruct Hwf as (Heq1 & Hcur & Hinner). subst.
      eapply Hopened_na; eauto.
  Qed.

  Fixpoint lty_size (lt : lty) : nat :=
    match lt with
    | OfTyLty _ => 0
    | AliasLty rt st l => 0
    | BlockedLty _ _ => 0
    | ShrBlockedLty _ _ => 0
    | MutLty lt _ => 1 + lty_size lt
    | ShrLty lt _ => 1 + lty_size lt
    | StructLty lts _ => 1 + list_max (fmap lty_size lts)
    | ArrayLty def len lts => 1 + (list_max (fmap (λ '(_, lt), lty_size lt) lts))
    | EnumLty en variant =>
        1 + match variant with Some v => lty_size v.(elv_lty) | None => 0 end
    | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
        (* we will be using both [lt_cur] and [lt_inner] and [lt_full] recursively *)
        1 + max (lty_size lt_cur) (max (lty_size lt_inner) (lty_size lt_full))
    | CoreableLty _ lt_full =>
        1 + lty_size lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        1 + lty_size lt_cur + lty_size lt_full
    | OpenedNaLty lt_cur lt_inner Cpre Cpost =>
        1 + max (lty_size lt_cur) (lty_size lt_inner)
    end.
  Definition lty_size_rel : lty → lty → Prop :=
    ltof _ lty_size.
  Global Instance lty_size_rel_wf : WellFounded lty_size_rel.
  Proof. apply well_founded_ltof. Qed.

  (** Derived, stronger well-founded induction principle *)
  Lemma lty_size_recursor (P : lty → Type) :
    (∀ lt, (∀ lt', lty_size lt' < lty_size lt → P lt') → P lt) →
    ∀ lt, P lt.
  Proof.
    apply induction_ltof1.
  Defined.
  Lemma lty_size_induction (P : lty → Prop) :
    (∀ lt, (∀ lt', lty_size lt' < lty_size lt → P lt') → P lt) →
    ∀ lt, P lt.
  Proof.
    apply lty_size_recursor.
  Qed.


  (** The "core" of an ltype that we need to fold it to a type *)
  Fixpoint lty_core (lt : lty) : lty :=
    match lt with
    | BlockedLty t _ => OfTyLty t
    | ShrBlockedLty t _ => OfTyLty t
    | OfTyLty t => OfTyLty t
    | AliasLty rt st l => AliasLty rt st l
    | MutLty lt κ => MutLty (lty_core lt) κ
    | ShrLty lt κ => ShrLty (lty_core lt) κ
    | StructLty lts sls => StructLty (fmap lty_core lts) sls
    | ArrayLty def len lts => ArrayLty def len (fmap (λ '(i, lt), (i, lty_core lt)) lts)
    | EnumLty en variant =>
        EnumLty en ((λ v, mk_enum_lty_variant v.(elv_tag) v.(elv_rt) (lty_core v.(elv_lty)) v.(elv_rfn)) <$> variant)
    | OpenedLty lt_cur lt_inner lt_full Cpre Cpost =>
        (** Rationale: below unfolded stuff, the core just doesn't matter, because we have currently
           anyways broken all contracts and invariants.
            This is also important to get the [lty_core_rt_eq] law, which we use heavily (and is intrinsic to the definition of ltype ownership!).
           Otherwise, we would like to define it as [lt_full], but that breaks this law. *)
        OpenedLty lt_cur lt_inner lt_full Cpre Cpost
    | CoreableLty κ lt_full =>
        lty_core lt_full
    | ShadowedLty lt_cur r_cur lt_full =>
        (** Important: in contrast to [OpenedLty], this core is meaningful. [ShadowedLty] can be used below Uniq if there is a shared reference below, and in order to then allow updates, [typed_place_cond] for [Uniq] needs to be satisfiable. *)
        lty_core lt_full
    | OpenedNaLty lt_cur lt_inner Cpre Cpost =>
        OpenedNaLty lt_cur lt_inner Cpre Cpost
    end.

  Definition enum_lty_variant_core (v : enum_lty_variant) : enum_lty_variant :=
    mk_enum_lty_variant
      v.(elv_tag)
      v.(elv_rt)
      (lty_core v.(elv_lty))
      v.(elv_rfn).

  Lemma canonical_enum_lty_variant_core {rt : RT} (en : enum rt) r :
    enum_lty_variant_core (canonical_enum_lty_variant en r) =
      canonical_enum_lty_variant en r.
  Proof. done. Qed.
  Lemma interp_enum_lty_variant_core {rt : RT} (en : enum rt) variant r :
    interp_enum_lty_variant en (enum_lty_variant_core <$> variant) r =
      enum_lty_variant_core (interp_enum_lty_variant en variant r).
  Proof.
    destruct variant as [v | ]; simpl; first last.
    - apply canonical_enum_lty_variant_core.
    - destruct (decide (enum_tag en r = Some v.(elv_tag))); simpl; first done.
      apply canonical_enum_lty_variant_core.
  Qed.

  Lemma lty_core_syn_type_eq (lt : lty) :
    lty_st (lty_core lt) = lty_st lt.
  Proof.
    induction lt as [ | | | | | | | ? IH | | | | | ]; by eauto.
  Qed.

  Lemma RT_eq_iff (a b : RT) :
    a = b ↔
      (∃ (Heq1 : (RT_rt a) = (RT_rt b)) (Heq2 : (RT_xt a) = (RT_xt b)),
      ∀ r : RT_xt a, (RT_xrt a r) = rew <-[id] Heq1 in (RT_xrt b (rew [id] Heq2 in r))).
  Proof.
    destruct a as [?? xrta], b as [?? xrtb]. simpl in *.
    split.
    - intros Ha. injection Ha.
      intros Hx1 <- <-.
      apply existT_inj in Hx1. apply existT_inj in Hx1 as <-.
      exists eq_refl, eq_refl.
      intros r. simpl. done.
    - intros (Heq1 & Heq2 & Heqf).
      subst. enough (xrta = xrtb) as <- by done.
      apply functional_extensionality.
      done.
  Qed.

  Lemma lty_core_rt_eq lt :
    lty_rt (lty_core lt) = lty_rt lt.
  Proof.
    induction lt as [ | | | | ? IH ? | ? IH ? | lts IH ? | ? ? ? lts IH | | | | | ] using lty_induction; simpl; [done | done | done | done | | | | done.. ].
    - by rewrite IH.
    - by rewrite IH.
    - f_equiv.
      unfold fmap.
      induction lts as [ | lt lts IH']; simpl.
      { done. }
      opose proof (IH lt _) as IH2.
      { apply elem_of_cons; eauto. }
      opose proof (IH' _) as IH1.
      { intros. eapply IH. apply elem_of_cons; eauto. }
      rewrite IH2.
      rewrite IH1.
      done.
  Qed.
  Lemma OfTyLty_core_id {rt} (ty : type rt) :
    lty_core (OfTyLty ty) = OfTyLty ty.
  Proof. done. Qed.

  Lemma lty_core_rt_list_eq (lts : list lty) :
    lty_rt <$> (lty_core <$> lts) = lty_rt <$> lts.
  Proof.
    unfold fmap.
    induction lts as [ | ? ? IH]; simpl; first done.
    rewrite lty_core_rt_eq.
    rewrite IH//.
  Qed.
  Lemma lty_core_plist_rt_eq lts :
    plist (λ lt, place_rfn (lty_rt lt)) (fmap lty_core lts) = plist (λ lt, place_rfn (lty_rt lt)) lts.
  Proof.
    induction lts as [ | lt lts IH]; simpl; first done.
    rewrite /plist. rewrite lty_core_rt_eq. f_equiv. apply IH.
  Qed.
  Lemma lty_core_rt_eq' (lt : lty) : RT_rt (lty_rt (lty_core lt)) = RT_rt (lty_rt lt).
  Proof.
    specialize (lty_core_rt_eq lt) as Heq.
    apply RT_eq_iff in Heq as (Heq & _).
    done.
  Qed.

  (* We cannot get the other direction because of CoreableLty *)
  Lemma lty_core_wf lt :
    lty_wf lt → lty_wf (lty_core lt).
  Proof.
    induction lt as [ | | | | | | lts IH sls | rt def len lts IH | rt en variant IH | | rt lt IH | | ] using lty_induction; simpl; [done.. | | | | done | | | done ].
    - rewrite -!Forall_Forall_cb.
      rewrite Forall_fmap.
      apply Forall_impl_strong.
      intros; by apply IH.
    - rewrite -!Forall_Forall_cb.
      rewrite Forall_fmap.
      intros Hwf.
      eapply Forall_impl_strong; last done.
      intros [i lt] Hlt (? & Hrt). simpl.
      rewrite lty_core_rt_eq.
      split; last done. eapply IH; done.
    - destruct variant as [v | ]; simpl in *; last done.
      intros [Hwf Hrt]. split; first by apply IH.
      rewrite lty_core_rt_eq. done.
    - done.
    - intros (? & ? & <-). eauto.
  Qed.

  Lemma lty_size_core (lt : lty) :
    lty_size (lty_core lt) ≤ lty_size lt.
  Proof.
    induction lt as [ | | | | | | lts IH sls | rt def len lts IH | rt en variant IH | | | | ] using lty_induction; simpl; try lia.
    - induction lts as [ | lt lts IH']; simpl; first done.
      opose proof* (IH lt) as IH0. { apply elem_of_cons. by left. }
      ospecialize* IH'. { intros. apply IH. apply elem_of_cons. by right. }
      unfold fmap in IH'. lia.
    - induction lts as [ | [i lt] lts IH2]; simpl; first lia.
      opose proof* (IH i lt) as IH0. { apply elem_of_cons. by left. }
      ospecialize* IH2. { intros. eapply IH. apply elem_of_cons. by right. }
      unfold fmap in IH2. lia.
    - destruct variant as [v | ]; simpl in *; lia.
  Qed.

  (*
    Notes on the placement of laters and fancy updates in the interpretations:

    For sharing:
      What are the constraints here/design space?
       - we are forced to have a later over recursive calls to the sharing predicate, due to contractiveness
       - we should not put laters over the fractured borrow (that would require us to take two steps when reading/unable to use timelessness over pointsto)

      So: need to put a later in each of the sharing cases, directly over the recursive call.

      Q: should we also put a later in the ofty case?
        Pro: makes the equation _1 for mut ref unfolding go through easily
        Con: Now I need to put a later above the fractional borrow in MutLty to get the equation _2, which I don't want to do.
      So: just put an update there for timeless stripping

      Approach: put an update in ltype_eq also for the shared borrow case. Does this have drawbacks?
        => Problem: this kills the compatibility with e.g. mut_lty, due to later fupd commuting problems. So this does not seem like the right approach.

      Approach: I need to put an update over the whole MutLty (because all interesting stuff is under the update)
        What is the downside? we anyways need to be able to eliminate an update when accessing the fractional borrow.
        the same trick also seems to work just fine for mutable borrows, where we have an update over the full borrow.
        => This seems to work fine.

      Approach: try to modify the definition of the sharing case of ofty in order to get more useful stuff directly.
        (fundamental problem in this equation here: MutLty has a lot of info upfront, while the def of ofty can't really provide a lot directly) one idea for that: give sharing a "with_later" parameter that allows pushing laters down a bit. still doesn't answer how to get the fractured borrow here without a later though.
   *)


  Definition lty_own_type (lt : lty) := bor_kind → thread_id → place_rfn (lty_rt lt) → loc → iProp Σ.

  Definition lty_own_type_rec (lt0 : lty) := ∀ lt : lty, bor_kind → thread_id → place_rfn (lty_rt lt) → loc → lty_size_rel lt lt0 → iProp Σ.

  Definition UninitLty st := OfTyLty (uninit st).

  Definition lty_of_ty_own {rt} (ty : type rt) k π (r : place_rfn rt) l :=
    (∃ ly : layout,
      ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      ty.(ty_sidecond) ∗ loc_in_bounds l 0 (ly.(ly_size)) ∗
    match k with
    | Owned =>
        ∃ r' : rt,
        place_rfn_interp_owned r r' ∗
        (* Have a later here according to wl, which is imposed by e.g. a Box directly above it.
          As such, this is really needed for contractiveness/making working with rec types possible. *)
        |={lftE}=>  ∃ v, l ↦ v ∗ ty.(ty_own_val) π r' MetaNone v
    | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        (* Note: need an update inside the borrow over the recursive thing to get the unfolding equation for products
          (as products need an update there)
          This is really annoying, as this propagates to the other ltypes as well.
          And there, it means that we actually have an update over the pointsto (e.g. in Box and Mutref) in the Uniq case,
            which breaks timelessness after opening the borrow..
         *)
        |={lftE}=> &pin{κ} (∃ r', gvar_auth γ r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r' MetaNone)
    | Shared κ =>
        (* we need an update for timelessness in the unfolding equations (eg for mut_ref) *)
        ∃ r' : rt, place_rfn_interp_shared r r' ∗ □ |={lftE}=> ty.(ty_shr) κ π r' MetaNone l
    end)%I.

  Definition alias_lty_own (rt : RT) (st : syn_type) (p : loc) k π (r : place_rfn rt) l :=
    match k with
    | Owned =>
      ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜p = l⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗ loc_in_bounds l 0 (ly_size ly)
    | Shared _ =>
      ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ ⌜p = l⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗ loc_in_bounds l 0 (ly_size ly)
    | _ => False
    end%I.

  Definition blocked_lty_own {rt} (ty : type rt) κ k π (r : place_rfn rt) l :=
    (∃ ly, ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      ty.(ty_sidecond) ∗ loc_in_bounds l 0 ly.(ly_size) ∗
    match k with
    | Owned =>
        ([† κ] ={lftE}=∗
          ∃ (r' : rt), place_rfn_interp_owned r r' ∗ |={lftE}=> l ↦: (ty.(ty_own_val) π r' MetaNone))
    | Shared κ' =>
        (* sharing of inheritances is weird, they are of no use like that,
          and there's no reason to create inheritances directly below
          shared borrows in the first place *)
        False
    | Uniq κ' γ' =>
        (* borrow needs to be synced up with OfTy *)
        ([† κ] ={lftE}=∗
          place_rfn_interp_mut r γ' ∗
          &pin{κ'} (∃ r' : rt, gvar_auth γ' r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r' MetaNone)) ∗
        (* and the original credits *)
        have_creds
    end)%I.

  Definition shr_blocked_lty_own {rt} (ty : type rt) κ k π (r : place_rfn rt) l :=
    (∃ ly : layout, ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗ ty.(ty_sidecond) ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
    ∃ r': rt, place_rfn_interp_shared r r' ∗
    match k with
    | Owned =>
        (* also have the sharing predicate *)
        ty.(ty_shr) κ π r' MetaNone l ∗
        ([† κ] ={lftE}=∗ l ↦: ty.(ty_own_val) π r' MetaNone)
    | Shared κ' =>
        (* already shared -- no need to do something special *)
        (*ty.(ty_shr) κ' π r' l*)
        False
    | Uniq κ' γ' =>
        place_rfn_interp_mut r γ' ∗
        ty.(ty_shr) κ π r' MetaNone l ∗
        ([† κ] ={lftE}=∗
          (* this needs to be synced up with [OfTy] *)
          &pin{κ'} (∃ r'': rt, gvar_auth γ' r'' ∗ |={lftE}=> l ↦: ty.(ty_own_val) π r'' MetaNone)) ∗
        (* original credits *)
        have_creds
    end)%I.

  (** Shows that the recursive struct case is well-formed. Crucially uses the information we obtain from [big_sepL_P]. *)
  Lemma struct_lts_size_decreasing sl sls (lts : list lty) (r' : plist (λ lt, place_rfn (lty_rt lt)) lts) ty :
    ty ∈  pad_struct (sl_members sl) (pzipl lts r') (λ ly : layout, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())) →
    lty_size_rel (projT1 ty) (StructLty lts sls).
  Proof.
    intros HP.
    destruct ty as (lt & rlt).
    apply list_elem_of_lookup_1 in HP as (j & HP).
    apply pad_struct_lookup_Some_1 in HP as (n & ly & Hlook1 & Hlook2).
    destruct Hlook2 as [ Hlook2 | [_ [= -> ->]]]; first last.
    { unfold lty_size_rel, ltof. simpl. lia. }
    move: Hlook2. generalize (field_idx_of_idx (sl_members sl) j) as m. clear.
    unfold lty_size_rel, ltof; simpl. intros m.
    induction lts as [ | lt0 lts IH] in m, r' |-*; intros [ ? Heq ]; simpl; first done.
    destruct m as [ | m]; simpl.
    - injection Heq as [= <- Heq]. apply existT_inj in Heq. subst rlt. lia.
    - eapply Nat.lt_le_trans; first eapply IH. { split; first done. apply Heq. }
      unfold fmap. lia.
  Qed.

  Lemma array_lts_size_decreasing {rt} (def : type rt) len (lts : list (nat * lty)) {A} (r : list A) (lt : lty * A)  :
    lt ∈ (zip (interpret_iml (OfTyLty def) len lts) r) → lty_size_rel (lt.1) (ArrayLty def len lts).
  Proof.
    intros HP.
    apply list_elem_of_lookup_1 in HP as (j & HP).
    unfold lty_size_rel, ltof; simpl.
    apply lookup_zip in HP as [Hlook1 Hlook2].
    apply lookup_interpret_iml_Some_inv in Hlook1 as (Hlen & Hlook1).
    destruct lt as [lt a].
    destruct Hlook1 as [-> | Hlook1]; simpl; first lia.
    assert (lty_size lt ≤ list_max ((λ '(_, lt), lty_size lt) <$> lts)) as ?; last lia.
    apply list_elem_of_lookup_1 in Hlook1 as (k & Hlook).
    eapply (list_max_le_lookup _ k).
    { rewrite list_lookup_fmap. rewrite Hlook. done. }
    done.
  Qed.

  Lemma enum_lty_variant_size_decreasing {rt} (en : enum rt) variant r :
    lty_size_rel (elv_lty (interp_enum_lty_variant en variant r)) (EnumLty en variant).
  Proof.
    destruct variant as [v | ]; unfold lty_size_rel, ltof; simpl.
    - destruct (decide (enum_tag en r = Some v.(elv_tag))); simpl; lia.
    - lia.
  Qed.

  Lemma struct_rfn_eq (lts : list lty) :
    plist (place_rfn ∘ RT_rt ∘ lty_rt) lts = plist (RT_rt ∘ place_rfnRT) (lty_rt <$> lts).
  Proof.
    rewrite -plist_fmap_shift. simpl. done.
  Qed.


  Import EqNotations.

  Definition ptr_loc_own (l li : loc) : iProp Σ :=
    (∃ vi : val, l ↦ vi ∗ ⌜val_decodes_to_loc vi li⌝)%I.

  Definition ptr_loc_own_frac (l : loc) (q : Qp) (li : loc) : iProp Σ :=
    (∃ vi : val, l ↦{q} vi ∗ ⌜val_decodes_to_loc vi li⌝)%I.

  Equations lty_own_pre (core : bool) (ltp : lty) (k : bor_kind) (π : thread_id) (r : place_rfn (lty_rt ltp)) (l : loc) : iProp Σ by wf ltp lty_size_rel :=
    lty_own_pre core (OfTyLty ty) k π r l :=
      (* OfTy *)
      lty_of_ty_own ty k π r l;
    lty_own_pre core (AliasLty rt st p) k π r l :=
      alias_lty_own rt st p k π r l;
    lty_own_pre core (BlockedLty ty κ) k π r l :=
      (** Blocked *)
      if core then lty_of_ty_own ty k π r l else blocked_lty_own ty κ k π r l ;
    lty_own_pre core (ShrBlockedLty ty κ) k π r l :=
      (** ShrBlocked *)
      if core then lty_of_ty_own ty k π r l else shr_blocked_lty_own ty κ k π r l;

    lty_own_pre core (MutLty lt κ) k π r l :=
      (** Mut *)
      (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
       loc_in_bounds l 0 ly.(ly_size) ∗
      match k with
      | Owned =>
          (* it's fine to existentially quantify here over the gvar_obs, since
            the outer can actually tell us about it. Keep in mind that the gvar here can actually
            change if we write under nested places. *)
          ∃ (γ : gname) (r' : place_rfn (lty_rt lt)) ,
          place_rfn_interp_owned r (r', γ) ∗
          (* TODO layout requirements on l' here? *)
          |={lftE}=> ∃ l' : loc, ptr_loc_own l l' ∗ (lty_own_pre core lt (Uniq κ γ) π r' l')
      | Uniq κ' γ' =>
            have_creds ∗
            place_rfn_interp_mut r γ' ∗
            |={lftE}=> &pin{κ'}
              [∃ (r' : (place_rfn (lty_rt lt)) * gname),
                gvar_auth γ' r' ∗
                (* update here to be compatible with ofty *)
                |={lftE}=>
                ∃ (l' : loc), ptr_loc_own l l' ∗
                lty_own_pre true lt (Uniq κ r'.2) π r'.1 l'
              ]
              (∃ (r' : (place_rfn (lty_rt lt)) * gname),
                gvar_auth γ' r' ∗
                (* update here to be compatible with ofty *)
                |={lftE}=>
                ∃ (l' : loc), ptr_loc_own l l' ∗
                lty_own_pre core lt (Uniq κ r'.2) π r'.1 l')
      | Shared κ' =>
        (∃ r' γ, place_rfn_interp_shared r (r', γ) ∗
        (* the update is also over the fractional borrow to deal with timelessness *)
        □ |={lftE}=> ∃ (vi : val) (li : loc),
          &frac{κ'}(λ q', l ↦{q'} vi) ∗
          ⌜val_decodes_to_loc vi li⌝ ∗
          (* later is for contractiveness, the update for timelessness *)
          ▷ lty_own_pre core lt (Shared (κ⊓κ')) π r' li)%I
      end)%I;

    lty_own_pre core (ShrLty lt κ) k π r l :=
      (** Shr *)
      (∃ ly : layout, ⌜syn_type_has_layout PtrSynType ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
         loc_in_bounds l 0 ly.(ly_size) ∗
        match k with
        | Owned =>
            ∃ (r' : place_rfn (lty_rt lt)), place_rfn_interp_owned r r' ∗
            |={lftE}=> ∃ (l' : loc), ptr_loc_own l l' ∗
            lty_own_pre core lt (Shared κ) π r' l'
        | Uniq κ' γ' =>
            have_creds ∗
            place_rfn_interp_mut r γ' ∗
            |={lftE}=> &pin{κ'}
              [∃ (r' : place_rfn (lty_rt lt)), gvar_auth γ' r' ∗
                |={lftE}=> ∃ (l' : loc), ptr_loc_own l l' ∗ lty_own_pre true lt (Shared κ) π r' l']
              (∃ (r' : place_rfn (lty_rt lt)), gvar_auth γ' r' ∗
                |={lftE}=> ∃ (l' : loc), ptr_loc_own l l' ∗ lty_own_pre core lt (Shared κ) π r' l')
        | Shared κ' =>
            ∃ (r' : place_rfn (lty_rt lt)),
            place_rfn_interp_shared r r' ∗
            (* the update is also over the fractional borrow to deal with timelessness *)
            □ |={lftE}=> ∃ (vi : val) (li : loc),
            &frac{κ'} (λ q, l ↦{q} vi) ∗
            ⌜val_decodes_to_loc vi li⌝ ∗
            (* no intersection here, as we also don't do that for the type interpretation *)
            ▷ lty_own_pre core lt (Shared κ) π r' li
        end)%I;

    lty_own_pre core (StructLty lts sls) k π r l :=
      (** Struct *)
      ∃ sl : struct_layout,
      ⌜use_struct_layout_alg sls = Some sl⌝ ∗
      ⌜length (sls_fields sls) = length lts⌝ ∗
      ⌜l `has_layout_loc` sl⌝ ∗
      loc_in_bounds l 0 (sl.(ly_size)) ∗
      match k with
      | Owned =>
          (* We change the interpretation to Owned false and interpret the later here, because we cannot push down/split up the credits for each of the components *)
          ∃ r' : plist (place_rfn ∘ lty_rt) lts,
          place_rfn_interp_owned r (rew [id] (struct_rfn_eq lts) in r') ∗
          |={lftE}=>
          big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))
            (λ i ty HP,
              ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
              lty_own_pre core (projT1 ty) Owned π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))
      | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        (* We change the ownership to Owned false, because we can't push the borrow down in this formulation of products.
          The cost of this is that we need an update here (to get congruence rules for ltype_eq),
          which propagates to all the other Uniq cases of other ltypes. *)
        |={lftE}=> &pin{κ}
          [∃ (r' : plist (λ lt, place_rfn (lty_rt lt)) lts),
            gvar_auth γ r' ∗ |={lftE}=>
            big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))
              (λ i ty HP,
                  ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
                  lty_own_pre true (projT1 ty) Owned π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))
          ]
          (∃ (r' : plist (λ lt, place_rfn (lty_rt lt)) lts),
            gvar_auth γ r' ∗ |={lftE}=>
            big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))
              (λ i ty HP,
                ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
                lty_own_pre core (projT1 ty) Owned π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)))
          )
      | Shared κ =>
          (∃ r' : plist (place_rfn ∘ lty_rt) lts,
            place_rfn_interp_shared r (rew [id] (struct_rfn_eq lts) in r') ∗
            (* update needed to make the unfolding equation work *)
            □ |={lftE}=>
              big_sepL_P (pad_struct sl.(sl_members) (pzipl lts r') (λ ly, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))
                (λ i ty HP,
                  ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
                  lty_own_pre core (projT1 ty) (Shared κ) π (projT2 ty) (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i))))
      end;

    lty_own_pre core (@ArrayLty rt def len lts) k π r l :=
      (** ArrayLty *)
      ∃ ly,
        ⌜syn_type_has_layout (ty_syn_type def MetaNone) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly.(ly_size) * len) ∗
        (*⌜Forall (λ '(i, lts), i < len) lts⌝ ∗*)
      match k with
      | Owned =>
        ∃ r' : list (place_rfn rt), place_rfn_interp_owned r r' ∗
        |={lftE}=>
        (⌜length r' = len⌝ ∗
        big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
          (λ i ty HP,
            ∃ (Heq : RT_rt (lty_rt ty.1) = RT_rt rt),
              ⌜lty_st ty.1 = ty_syn_type def MetaNone⌝ ∗
              lty_own_pre core ty.1 Owned π (rew <- [place_rfn] Heq in ty.2) (offset_loc l ly i)))
      | Uniq κ γ =>
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        |={lftE}=> &pin{κ}
          [∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
              (λ i ty HP,
                ∃ (Heq : RT_rt (lty_rt ty.1) = RT_rt rt),
                  ⌜lty_st ty.1 = ty_syn_type def MetaNone⌝ ∗
                  lty_own_pre true ty.1 Owned π (rew <- [place_rfn] Heq in ty.2) (offset_loc l ly i)
              ))]
          (∃ r' : list (place_rfn rt), gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗
              big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
              (λ i ty HP,
                ∃ (Heq : RT_rt (lty_rt ty.1) = RT_rt rt),
                  ⌜lty_st ty.1 = ty_syn_type def MetaNone⌝ ∗
                  lty_own_pre core ty.1 Owned π (rew <- [place_rfn] Heq in ty.2) (offset_loc l ly i))))

      | Shared κ =>
          ∃ r', place_rfn_interp_shared r r' ∗
            □ |={lftE}=> ⌜length r' = len⌝ ∗
            big_sepL_P (zip (interpret_iml (OfTyLty def) len lts) r')
              (λ i ty HP,
                ∃ (Heq : RT_rt (lty_rt ty.1) = RT_rt rt),
                  ⌜lty_st ty.1 = ty_syn_type def MetaNone⌝ ∗
                  lty_own_pre core ty.1 (Shared κ) π (rew <- [place_rfn] Heq in ty.2) (offset_loc l ly i))
      end;

    lty_own_pre core (@EnumLty rt en variant) k π r l :=
    (** EnumLty *)
      ∃ el,
      ⌜use_enum_layout_alg en.(enum_els) = Some el⌝ ∗
      ⌜l `has_layout_loc` el⌝ ∗
      loc_in_bounds l 0 el.(el_size) ∗
      let tag_ly := it_layout el.(el_tag_it) in
      let tag_size := ly_size tag_ly in
      let data_offset := el.(el_data_offset) in

      match k with
      | Owned =>
        ∃ r' : rt, place_rfn_interp_owned r r' ∗
        let v := interp_enum_lty_variant en variant r' in
        |={lftE}=> ∃ variant_ly,
          ⌜enum_lty_variant_tag_compat en r' v⌝ ∗
          ⌜enum_variant_lookup el.(el_variants) v.(elv_tag) = Some variant_ly⌝ ∗
          ⌜syn_type_has_layout (lty_st v.(elv_lty)) variant_ly⌝ ∗
          (* ownership of the discriminant *)
          lty_of_ty_own (int el.(el_tag_it)) Owned π (PlaceIn (els_lookup_tag en.(enum_els) v.(elv_tag))) l ∗
          (* ownership of the padding between the discriminant and the payload *)
          lty_of_ty_own (uninit (LiteralSynType (Layout (data_offset - tag_size) 0))) Owned π (PlaceIn ()) (l +ₗ tag_size) ∗
          (* ownership of the data *)
          (∃ Heq : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt),
            lty_own_pre core v.(elv_lty) Owned π (PlaceIn (rew <-[id] Heq in v.(elv_rfn))) (l +ₗ data_offset)) ∗
          (* ownership of the remaining padding after the payload *)
          lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - data_offset - ly_size variant_ly) 0))) Owned π (PlaceIn ())
            (l +ₗ data_offset +ₗ ly_size variant_ly)
      | Shared κ =>
        ∃ r' : rt, place_rfn_interp_shared r r' ∗
        let v := interp_enum_lty_variant en variant r' in
        □ |={lftE}=> ∃ variant_ly,
          ⌜enum_lty_variant_tag_compat en r' v⌝ ∗
          ⌜enum_variant_lookup el.(el_variants) v.(elv_tag) = Some variant_ly⌝ ∗
          ⌜syn_type_has_layout (lty_st v.(elv_lty)) variant_ly⌝ ∗
          (* shared ownership of the discriminant *)
          lty_of_ty_own (int el.(el_tag_it)) (Shared κ) π (PlaceIn (els_lookup_tag en.(enum_els) v.(elv_tag))) l ∗
          (* shared ownership of the padding between the discriminant and the payload *)
          lty_of_ty_own (uninit (LiteralSynType (Layout (data_offset - tag_size) 0))) (Shared κ) π (PlaceIn ()) (l +ₗ tag_size) ∗
          (* shared ownership of the data *)
          (∃ Heq : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt),
            lty_own_pre core v.(elv_lty) (Shared κ) π (PlaceIn (rew <-[id] Heq in v.(elv_rfn))) (l +ₗ data_offset)) ∗
          (* shared ownership of the remaining padding after the payload *)
          lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - data_offset - ly_size variant_ly) 0))) (Shared κ) π (PlaceIn ())
            (l +ₗ data_offset +ₗ ly_size variant_ly)
      | Uniq κ γ =>
        let enum_uniq_body core' :=
          (∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=> (∃ variant_ly,
          let v := interp_enum_lty_variant en variant r' in
          ⌜enum_lty_variant_compat en r' v⌝ ∗
          ⌜enum_variant_lookup el.(el_variants) v.(elv_tag) = Some variant_ly⌝ ∗
          ⌜syn_type_has_layout (lty_st v.(elv_lty)) variant_ly⌝ ∗
          (* ownership of the discriminant *)
          lty_of_ty_own (int el.(el_tag_it)) Owned π (PlaceIn (els_lookup_tag en.(enum_els) v.(elv_tag))) l ∗
          (* ownership of the padding between the discriminant and the payload *)
          lty_of_ty_own (uninit (LiteralSynType (Layout (data_offset - tag_size) 0))) Owned π (PlaceIn ()) (l +ₗ tag_size) ∗
          (* ownership of the data *)
          (∃ Heq : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt),
            lty_own_pre core' v.(elv_lty) Owned π (PlaceIn (rew <-[id] Heq in v.(elv_rfn))) (l +ₗ data_offset)) ∗
          (* ownership of the remaining padding after the payload *)
          lty_of_ty_own (uninit (LiteralSynType (Layout (el.(el_size) - data_offset - ly_size variant_ly) 0))) Owned π (PlaceIn ())
            (l +ₗ data_offset +ₗ ly_size variant_ly)))%I in
        have_creds ∗
        place_rfn_interp_mut r γ ∗
        |={lftE}=> (pinned_bor κ (enum_uniq_body true) (enum_uniq_body core))
      end;

    lty_own_pre core (@OpenedLty rt_inner rt_full lt_cur lt_inner lt_full Cpre Cpost) k π r l :=
      (** OpenedLty *)
      ∃ ly, ⌜use_layout_alg (lty_st lt_cur) = Some ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly_size ly) ∗
        ⌜lty_st lt_cur = lty_st lt_inner⌝ ∗
        ⌜lty_st lt_inner = lty_st lt_full⌝ ∗

      match k with
      | Owned =>
          lty_own_pre false lt_cur Owned π r l ∗
          logical_step lftE
          (∃ (Heq_inner : rt_inner = lty_rt lt_inner) (Heq_full : rt_full = lty_rt lt_full),
            (* once we have restored to [lt_inner], we can fold to [lt_full] again *)
            ∀ (r : rt_inner) (r' : rt_full) (κs : list lft),
              (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
              (* directly hand out Cpost. We don't need to wait to get tokens from closing borrows etc. *)
              Cpost r r' ∗
              (lft_dead_list κs -∗
               lty_own_pre false lt_inner Owned π (PlaceIn (rew [RT_rt] Heq_inner in r)) l ={lftE}=∗
               lty_own_pre true lt_full Owned π (PlaceIn (rew [RT_rt] Heq_full in r')) l
              ))
      | Uniq κ γ =>
        lty_own_pre false lt_cur Owned π r l ∗
        (* Note: we are not interpreting γ here - it is currently completely unconstrained, and the
           ownership of the ghost variable fragments lies with the closing viewshift *)

        (* Main points important for this VS:
            - we close the pinned borrow again, so that we can get lifetime tokens back in Cpost
            - we cannot restore lt_full directly, because we want to be able to execute this while subplaces are still borrowed;
              instead we require that we can shift to lt_inner once [κ] is dead (has a flavor of [imp_unblockable]). *)
        (* to prove when unfolding in the first place:
            if I assume Cpre r r' and lty_own_pre true lt_inner(Owned false) π r l, then I can restore lt_full again and produce Cpost r r' *)
        logical_step lftE
        (∃ (Heq : rt_inner = lty_rt lt_inner) (Heq_full : rt_full = lty_rt lt_full),
          (* we will execute this VS when closing the invariant, after having already stratified [lt_cur].
             At that point, we will know [lt_cur] is unblockable to [lt_inner] after some set of lifetimes [κs] is dead *)
          ∀ (own_lt_cur' : thread_id → rt_inner → loc → iProp Σ) (κs : list lft)
            (r : rt_inner) (r' : rt_full),
            (lft_dead_list κs ={lftE}=∗ Cpre r r') -∗
            ([∗ list] κ' ∈ κs, κ' ⊑ κ) -∗
            own_lt_cur' π r l -∗

            (* the ownership of [lt_cur'] needs to be shiftable to the _core_ of [lt_inner];
              this is required for closing the borrow and for proving that it can be unblocked to lt_full
                (which is needed for showing the shift to Coreable) *)
            (□ (lft_dead_list κs -∗ own_lt_cur' π r l ={lftE}=∗
              lty_own_pre true lt_inner Owned π (rew [place_rfnRT] Heq in PlaceIn r) l)) ={lftE}=∗

            Cpost r r' ∗
            gvar_obs γ (rew [RT_rt] Heq_full in r') ∗
            (lft_dead_list κs -∗ gvar_obs γ (rew [RT_rt] Heq_full in r') ={lftE}=∗
              lty_own_pre true lt_full (Uniq κ γ) π (rew [place_rfnRT] Heq_full in PlaceIn r') l)
        )

      | Shared κ =>
        (* TODO: how do we deal with fractional ownership of the pointsto we get from ofty?
           And how does it interact with the types we want to unfold in practice?
        *)
        (*lty_own_pre false lt_cur (Shared κ) π r l*)
        False
      end;
    lty_own_pre core (@CoreableLty κs lt_full) k π r l :=
      (if core then
        lty_own_pre true lt_full k π r l
      else
        ∃ ly, ⌜syn_type_has_layout (lty_st lt_full) ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly_size ly) ∗
        match k with
        | Owned =>
            lft_dead_list κs ={lftE}=∗ lty_own_pre true lt_full Owned π r l
        | Uniq κ' γ =>
            place_rfn_interp_mut r γ ∗
            (lft_dead_list κs -∗ place_rfn_interp_mut r γ ={lftE}=∗ lty_own_pre true lt_full (Uniq κ' γ) π r l)
        | Shared κ =>
            (*False*)
            lty_own_pre true lt_full (Shared κ) π r l
        end)%I;
    lty_own_pre core (@ShadowedLty rt_cur lt_cur r_cur lt_full) k π r l :=
      (if core then lty_own_pre true lt_full k π r l
       else
        ∃ (Heq_cur : rt_cur = lty_rt lt_cur),
        lty_own_pre core lt_cur k π ((rew [place_rfnRT] Heq_cur in r_cur)) l ∗
        lty_own_pre core lt_full k π r l)%I;
    lty_own_pre core (@OpenedNaLty rt_inner lt_cur lt_inner Cpre Cpost) k π r l :=
      (** OpenedNaLty *)
      ∃ ly, ⌜use_layout_alg (lty_st lt_cur) = Some ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 (ly_size ly) ∗
        ⌜lty_st lt_cur = lty_st lt_inner⌝ ∗

      match k with
      | Owned =>
          lty_own_pre false lt_cur Owned π r l ∗
          logical_step lftE
          (∃ (Heq_inner : rt_inner = lty_rt lt_inner),
            ∀ (r : rt_inner),
              Cpre r -∗
              lty_own_pre false lt_inner Owned π (PlaceIn (rew [RT_rt] Heq_inner in r)) l ={lftE ∪ shrE}=∗ Cpost r)
      | _ => False
      end
  .
  Solve Obligations with first [unfold lty_size_rel, ltof; simpl; lia | intros; eauto using struct_lts_size_decreasing, array_lts_size_decreasing, enum_lty_variant_size_decreasing].
  Definition lty_own := @lty_own_pre false.
  Definition lty_own_core := @lty_own_pre true.

  (** Basic laws of ltypes *)

  Lemma lty_own_pre_shr_pers core (lt : lty) κ π r l :
    Persistent (lty_own_pre core lt (Shared κ) π r l).
  Proof.
    induction lt using lty_induction in κ, π, r, l, core |-*; simp lty_own_pre;
    destruct core; simpl; try done; apply _.
  Qed.
  Global Instance lty_own_shr_pers (lt : lty) κ π r l :
    (*TCDone (match lt with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (lty_own lt (Shared κ) π r l).
  Proof. apply lty_own_pre_shr_pers. Qed.
  Global Instance lty_own_core_shr_pers (lt : lty) κ π r l :
    (*TCDone (match lt with OpenedLty _ _ _ _ _ => False | _ => True end) →*)
    Persistent (lty_own_core lt (Shared κ) π r l).
  Proof. apply lty_own_pre_shr_pers. Qed.

  Lemma lty_core_idemp (lt : lty) :
    lty_core (lty_core lt) = lty_core lt.
  Proof.
    induction lt as [ | | | | | | lts IH ? | rt def len lts IH | rt en variant IH | | | | ] using lty_induction;
      simpl; try done; try (f_equiv; eauto).
    - induction lts as [ | lt lts IH']; first done.
      simpl. rewrite IH; first last. { apply elem_of_cons; eauto. }
      f_equiv. apply IH'.
      intros. apply IH. apply elem_of_cons; eauto.
    - induction lts as [ | [j lt] lts IH2]; first done.
      simpl. erewrite IH; first last. { apply elem_of_cons; eauto. }
      f_equiv. apply IH2.
      intros. eapply (IH (i)). apply elem_of_cons; eauto.
    - destruct variant as [v | ]; simpl in *; last done.
      destruct v as [tag rt_v lt r]. simpl in *. rewrite IH. done.
  Qed.

  Lemma lty_own_has_layout (lt : lty) k π r l :
    lty_own lt k π r l -∗ ∃ ly : layout, ⌜syn_type_has_layout (lty_st lt) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝.
  Proof.
    iIntros "Hown". rewrite /lty_own.
    iInduction lt as [ | | | | | | | rt def len lts IH | | ?? lt_cur lt_inner lt_full Cpre Cpost | | | ] "IH" using lty_induction forall (k); simp lty_own_pre.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - destruct k; last done.
      + iDestruct "Hown" as "(%ly & ? & ? & ? & ?)"; eauto.
      + iDestruct "Hown" as "(%ly & ? & ? & ? & ?)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)"; eauto.
    - iDestruct "Hown" as "(%sl & % & % & % & _)".
      iExists sl. simpl. iPureIntro. split; last done. by apply use_struct_layout_alg_Some_inv.
    - iDestruct "Hown" as "(%ly & % & %Hsz & % & _)".
      iExists (mk_array_layout ly len). iSplitR; last done.
      iPureIntro. simpl.
      eapply syn_type_has_layout_array; done.
    - iDestruct "Hown" as (el) "(%Hen & %Hly & Hown)".
      iExists _. iL.
      iPureIntro. by eapply use_enum_layout_alg_Some_inv in Hen.
    - simpl. iDestruct "Hown" as "(%ly & ? & ? & ? & ? & _)".
      eauto.
    - iDestruct "Hown" as "(%ly & ? & ? & _)". eauto.
    - iDestruct ("Hown") as (->) "(Ha & Hb)".
      simpl.
      iApply "IH1". done.
      (*rewrite -Hst. iApply ("IH" with "Ha").*)
    - simpl. iDestruct "Hown" as "(%ly & ? & ? & ? & ? & _)".
      eauto.
  Qed.

  Lemma lty_own_loc_in_bounds (lt : lty) k π r l ly :
    syn_type_has_layout (lty_st lt) ly →
    lty_own lt k π r l -∗ loc_in_bounds l 0 ly.(ly_size).
  Proof.
    iIntros (Ha) "Hown". rewrite /lty_own.
    iInduction lt as [ | | | | | | | | | ? ??? | | | ] "IH" using lty_induction forall (k); simp lty_own_pre.
    - iDestruct "Hown" as "(%ly' & %Halg' & ? & ? & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - destruct k; last done.
      { iDestruct "Hown" as "(%ly' & % & ? & ? & ?)".
        have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst. }
      { iDestruct "Hown" as "(%ly' & % & ? & ? & ?)".
        have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst. }
    - iDestruct "Hown" as "(%ly' & % & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & % & _ & ? & _)".
      have ?: ly' = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%sl & %Hsl & _ & _ & ? & _)".
      apply use_struct_layout_alg_Some_inv in Hsl.
      have ?: layout_of sl = ly by eapply syn_type_has_layout_inj. by subst.
    - iDestruct "Hown" as "(%ly' & %Halg & _ & _ & ? & _)".
      apply syn_type_has_layout_array_inv in Ha as (ly0 & Halg' & -> & ?).
      assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
      done.
    - (* enum *)
      iDestruct "Hown" as (el) "(%Hen & %Hly & Hlb & _)".
      eapply use_enum_layout_alg_Some_inv in Hen.
      have ?: radium.enum.layout_of_enum el = ly by eapply syn_type_has_layout_inj.
      subst. done.
    - iDestruct "Hown" as "(%ly' & %Halg & ? & ? & ? & ? & _)".
      simpl in *. assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      iFrame.
    - iDestruct "Hown" as "(%ly' & %Halg & ? & ? & _)".
      simpl in *. assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      iFrame.
    - iDestruct "Hown" as (->) "( Ha & Hb)".
      simpl in Ha.
      iApply "IH1"; done.
    - iDestruct "Hown" as "(%ly' & %Halg & ? & ? & ? & ?)".
      simpl in *. assert (ly' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      iFrame.
  Qed.

  Import EqNotations.
  Definition transport_rfn {rt1 rt2 : Type} (Heq : rt1 = rt2) (r1 : place_rfn rt1) : place_rfn rt2 :=
    rew [place_rfn] Heq in r1.
  Arguments transport_rfn : simpl never.

  Lemma lty_own_pre_rfn_eq (lt : lty) π (r1 r2 : place_rfn (lty_rt lt)) core (b : bor_kind) (l : loc) :
    r1 = r2 → lty_own_pre core lt b π r1 l -∗ lty_own_pre core lt b π r2 l.
  Proof.
    intros ->. auto.
  Qed.
  Lemma lty_own_pre_rfn_eq' (lt : lty) π (r1 r2 : place_rfn (lty_rt lt)) core (b : bor_kind) (l : loc) :
    r1 = r2 → lty_own_pre core lt b π r1 l ⊣⊢ lty_own_pre core lt b π r2 l.
  Proof.
    intros ->. auto.
  Qed.

  (** Tactic automation to help solve the commonly occurring dependent equalities.
     Does not automate the [generalize] trick yet, so we have to do that manually below. *)
  Ltac normalize_dep_rt_goal_prepare :=
      simpl in *;
      repeat match goal with
             | H : place_rfn _ |- _ => revert H
             | H : plist _ _ |- _ => revert H
      end;
      repeat match goal with
      | |- context[rew [_] ?Heq in _] =>
          assert_fails (is_var Heq);
          generalize Heq
      | |- context[rew <-[_] ?Heq in _] =>
          assert_fails (is_var Heq);
          generalize Heq
      end;
      simpl in *;
      repeat match goal with
             | H : _ = _ |- _ => revert H
      end.
  Ltac normalize_dep_rt_goal_pass :=
      clear;
      normalize_dep_rt_goal_prepare;
      repeat match goal with
      | |- context[plist (?a ∘ ?b) _] => rewrite (plist_fmap_shift a b)
      end;
      repeat lazymatch goal with
             | |- ∀ (_ : ?A = ?B), _ =>
                 first [
                    intros [] |
                    unify A B;
                    let H := fresh "H" in
                    intros H;
                    rewrite (UIP_refl _ _ H);
                    clear H |
                    intros -> |
                    intros <- |
                    intros ?

                    ]
             | |- _ => intros ?
            end;
      try done
    .
  Ltac normalize_dep_rt_goal :=
    repeat normalize_dep_rt_goal_pass.


  Local Definition pzipl_core_map_fun := λ (p : sigT (λ lt, place_rfn (lty_rt lt))),
    (existT (lty_core (projT1 p)) (rew <-[place_rfn] (lty_core_rt_eq' (projT1 p)) in (projT2 p)) :
    sigT (λ lt, place_rfn (lty_rt lt))).
  Local Lemma pzipl_core_map_eq (lts : list lty) (r : plist (λ lt, place_rfn (lty_rt lt)) (map lty_core lts)) (Heq : plist (λ lt : lty, place_rfn (lty_rt lt)) (map lty_core lts) =
      plist (λ lt : lty, place_rfn (lty_rt lt)) lts) :
    pzipl (fmap lty_core lts) r = fmap pzipl_core_map_fun (pzipl lts (rew [id] Heq in r)).
  Proof.
    rewrite (pzipl_fmap_eqcast lty_core pzipl_core_map_fun _ _ lty_core_plist_rt_eq).
    - rewrite (UIP_t _ _ _ (lty_core_plist_rt_eq lts) Heq). done.
    - intros. rewrite lty_core_rt_eq'. done.
    - intros lt ? Heq1. unfold pzipl_core_map_fun. f_equiv; simpl.
      generalize (lty_core_rt_eq' lt) as Heq'.
      move : Heq1.
      generalize (RT_rt (lty_rt lt)) => T.
      intros Heq1 <-. normalize_dep_rt_goal.
  Qed.
  (* Follows the same structure as the proof for the struct ltype unfolding.
     Essentially the relevant part of the proof of [lty_own_core_core] below. *)
  Local Lemma StructLty_own_core_core_lift (sl : struct_layout) (lts : list lty)
    (r' : plist (λ lt, place_rfn (lty_rt lt)) (map lty_core lts))
    (Heq : plist (λ lt : lty, place_rfn (lty_rt lt)) (map lty_core lts) = plist (λ lt : lty, place_rfn (lty_rt lt)) lts) π l k :
    (∀ lt : lty, lt ∈ lts → ∀ k π r (Heq : RT_rt (lty_rt (lty_core lt)) = RT_rt (lty_rt lt)) l,
      lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π (transport_rfn Heq r) l) →
    ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl (map lty_core lts) r') (λ ly : layout, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre true (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i)) ⊣⊢
    [∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl lts (rew [id] Heq in r')) (λ ly : layout, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre true (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i).
  Proof.
    intros IH.
    rewrite pzipl_core_map_eq.
    set (ps' := (λ ly : layout, pzipl_core_map_fun (existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))).
    rewrite (pad_struct_ext _ _ _ ps'); first last.
    { intros. unfold ps', pzipl_core_map_fun. simpl. f_equiv.
      generalize (lty_core_rt_eq' (UninitLty (LiteralSynType ly))) => Heq2.
      normalize_dep_rt_goal. }
    rewrite pad_struct_fmap.
    rewrite big_sepL_fmap.
    iApply big_sepL_proper.
    iIntros (? [lt r0] Hlook).
    specialize (lty_core_rt_eq' lt) as Heq2.
    apply pad_struct_lookup_Some_1 in Hlook as (n & ly & ? & [[_ Hlook] | [_ Huninit]]).
    + eapply pzipl_lookup_inv in Hlook.
      f_equiv => Hly. f_equiv. f_equiv.
      { simpl. f_equiv. f_equiv. rewrite lty_core_syn_type_eq. done. }
      unshelve rewrite IH; first last. { by eapply list_elem_of_lookup_2. }
      2: apply Heq2.
      iApply lty_own_pre_rfn_eq'.
      normalize_dep_rt_goal.
    + injection Huninit as -> ->.
      simpl. clear. f_equiv => Hly. f_equiv. f_equiv.
      iApply lty_own_pre_rfn_eq'.
      normalize_dep_rt_goal.
  Qed.

  Local Lemma ArrayLty_own_core_core_lift {rt} st ly (lts : list lty) (r' : list (place_rfn rt)) π l k :
    (∀ lt : lty, lt ∈ lts → ∀ k π r (Heq : RT_rt (lty_rt (lty_core lt)) = RT_rt (lty_rt lt)) l,
      lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π (transport_rfn Heq r) l) →
    ([∗ list] i ↦ ty ∈ zip (fmap lty_core lts) r', ∃ Heq : RT_rt (lty_rt ty.1) = RT_rt rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre true ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)) ⊣⊢
    ([∗ list] i ↦ ty ∈ zip lts r', ∃ Heq : RT_rt (lty_rt ty.1) = RT_rt rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre true ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)).
  Proof.
    Set Printing Coercions.
    intros IH.
    rewrite zip_fmap_l big_sepL_fmap.
    apply big_sepL_proper.
    intros ? [lt r] Hlook.
    apply lookup_zip in Hlook as [Hlook1 Hlook2].
    assert (RT_rt (lty_rt (lty_core lt)) = RT_rt (lty_rt lt)) as Heq3. { rewrite lty_core_rt_eq'. done. }
    simpl in *. iSplit.
    - iIntros "(%Heq & %Hst & Hb)".
      assert (Heq2 : RT_rt (lty_rt lt) = RT_rt (rt)). { rewrite -lty_core_rt_eq'. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq in Hst. iSplitR; first done.
      apply list_elem_of_lookup_2 in Hlook1.
      unshelve rewrite IH; [done | | done].
      normalize_dep_rt_goal.
    - iIntros "(%Heq & %Hst & Hb)".
      assert (Heq2 : RT_rt (lty_rt (lty_core lt)) = RT_rt rt).
      { rewrite lty_core_rt_eq'. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq. iSplitR; first done.
      apply list_elem_of_lookup_2 in Hlook1. unshelve rewrite IH; [done | | done].
      normalize_dep_rt_goal.
  Qed.

  Local Lemma struct_core_rt_eq (lts : list lty) :
    plist (place_rfn ∘ RT_rt ∘ lty_rt) (lty_core <$> lts) =
    plist (place_rfn ∘ RT_rt ∘ lty_rt ) (lts).
  Proof.
    rewrite (struct_rfn_eq (lty_core <$> lts)).
    rewrite (struct_rfn_eq lts).
    rewrite lty_core_rt_list_eq.
    done.
  Qed.

  Lemma lty_own_core_core (lt : lty) k π (r : place_rfn (RT_rt (lty_rt (lty_core lt)))) r' Heq l :
    r' = (transport_rfn Heq r) →
    lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π r' l.
  Proof.
    Set Printing Coercions.
    intros ->. rewrite /lty_own_core.
    induction lt as [ | | | | lt IH κ | lt IH κ | lts IH sls | rt def len lts IH | rt en variant IH | | | | ] using lty_induction in k, π, r, l, Heq |-*; simpl in *.
    - simp lty_own_pre. normalize_dep_rt_goal.
    - simp lty_own_pre. normalize_dep_rt_goal.
    - normalize_dep_rt_goal.
    - normalize_dep_rt_goal.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq' lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      move: r Heq Heq2 IH.
      generalize (lty_core lt) as lt' => lt'.
      intros r Heq Heq2 IH.
      f_equiv.
      all: unshelve setoid_rewrite IH; [done.. | ].
      all: normalize_dep_rt_goal_prepare.
      all: generalize (RT_rt (lty_rt lt')) => ?.
      all: normalize_dep_rt_goal.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq' lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      move: r Heq Heq2 IH.
      generalize (lty_core lt) as lt' => lt'.
      intros r Heq Heq2 IH.
      f_equiv.
      all: unshelve setoid_rewrite IH; [done.. | ].
      all: normalize_dep_rt_goal_prepare.
      all: generalize (RT_rt (lty_rt lt')) => ?.
      all: normalize_dep_rt_goal.
    - simp lty_own_pre. fold lty_rt.
      do 5 f_equiv.
      { rewrite length_map. done. }

      normalize_dep_rt_goal_prepare. intros.
      do 2 f_equiv.
      all: setoid_rewrite big_sepL_P_eq.
      all: simpl.
      3: do 2 f_equiv; [ normalize_dep_rt_goal | do 2 f_equiv].
      all: iSplit.
      all: iIntros "(%r' & Hrfn & Hb)".

      all: specialize (struct_core_rt_eq lts) as Heq2.
      all: first [iExists (rew [id] Heq2 in r') | iExists (rew <-[id] Heq2 in r')].
      all: iSplitL "Hrfn"; first normalize_dep_rt_goal.
      all: unshelve rewrite StructLty_own_core_core_lift;
        [ apply Heq2 | | done].
      all: rewrite ?rew_invert'; done.
    - simp lty_own_pre.
      do 6 f_equiv.
      (*{ rewrite Forall_fmap. simpl.*)
        (*iPureIntro. eapply Forall_iff. intros []; done. }*)
      fold lty_rt. simpl.
      rewrite (UIP_refl _ _ Heq). clear Heq.
      f_equiv.
      all: repeat f_equiv; try done.
      all: rewrite !big_sepL_P_eq.
      all: rewrite -OfTyLty_core_id.
      all: rewrite interpret_iml_fmap.
      all: eapply ArrayLty_own_core_core_lift.
      all: intros ? [-> | []]%elem_of_interpret_iml_inv; simpl.
      all: intros ??? Heq; try rewrite (UIP_refl _ _ Heq); eauto.
    - (* enum *)
      simp lty_own_pre.
      fold lty_rt. simpl.
      rewrite (UIP_refl _ _ Heq). clear Heq.
      destruct variant as [v | ]; simpl in *; last done.
      rewrite /enum_lty_variant_tag_compat /enum_lty_variant_compat /enum_lty_variant_payload_compat /=.
      destruct k; simpl; try done.
      + rewrite /transport_rfn /=.
        do 12 f_equiv.
        all: destruct (decide (enum_tag en a0 = Some v.(elv_tag))); simpl in *; try done.
        all: try rewrite lty_core_syn_type_eq.
        do 5 f_equiv.
        iSplit.
        * iIntros "(%Heq & Ha)".
          assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
        * iIntros "(%Heq & Ha)".
          match goal with a : RT_rt rt |- _ => rename a into r1 end.
          assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite -Heq lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
      + rewrite /transport_rfn /=.
        do 13 f_equiv.
        all: destruct (decide (enum_tag en a0 = Some v.(elv_tag))); simpl in *; try done.
        all: try rewrite lty_core_syn_type_eq.
        do 5 f_equiv.
        iSplit.
        * iIntros "(%Heq & Ha)".
          assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
        * iIntros "(%Heq & Ha)".
          match goal with a : RT_rt rt |- _ => rename a into r1 end.
          assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite -Heq lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
      + rewrite /transport_rfn /=.
        rewrite /enum_lty_variant_tag_compat /enum_lty_variant_compat /enum_lty_variant_payload_compat /=.
        do 16 f_equiv.
        all: destruct (decide (enum_tag en a0 = Some v.(elv_tag))); simpl in *; try done.
        all: rewrite lty_core_syn_type_eq.
        all: do 5 f_equiv.
        all: iSplit.
        all: iIntros "(%Heq_lty & Ha)".
        * assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq_lty lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
        * assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
        * assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq_lty lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
        * assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite -Heq_lty lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite IH. { apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          generalize (lty_core_rt_eq' v.(elv_lty)) as Heq3.
          normalize_dep_rt_goal.
    - simp lty_own_pre. normalize_dep_rt_goal.
    - simp lty_own_pre.
    - simp lty_own_pre.
    - simp lty_own_pre. normalize_dep_rt_goal.
  Qed.
  Lemma lty_own_core_core' (lt : lty) k π r Heq l :
    lty_own_pre true (lty_core lt) k π r l ≡ lty_own_pre true lt k π (transport_rfn Heq r) l.
  Proof.
    rewrite lty_own_core_core; first done. done.
  Qed.

  Local Lemma StructLty_own_core_equiv_lift (sl : struct_layout) (lts : list lty) r (r' : plist (λ lt, place_rfn (lty_rt lt)) (fmap lty_core lts)) (Heq : plist (λ lt : lty, place_rfn (lty_rt lt)) (fmap lty_core lts) = plist (λ lt : lty, place_rfn (lty_rt lt)) lts) π l k (core : bool) :
    (∀ (lt : lty), lt ∈ lts → ∀ k π r (Heq : RT_rt (lty_rt lt) = RT_rt (lty_rt (lty_core lt))) l, lty_own_pre true lt k π r l ≡ lty_own_pre core (lty_core lt) k π (transport_rfn Heq r) l) →
    r = rew [id] Heq in r' →
    ([∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl lts r) (λ ly : layout, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre true (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i)) ⊣⊢
    [∗ list] i ↦ ty ∈ pad_struct (sl_members sl) (pzipl (fmap lty_core lts) r') (λ ly : layout, existT (UninitLty (LiteralSynType ly)) (PlaceIn ())),
      ∃ ly, ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (lty_st (projT1 ty)) ly⌝ ∗
      lty_own_pre core (projT1 ty) k π (projT2 ty) (l +ₗ offset_of_idx (sl_members sl) i).
  Proof.
    intros IH.
    rewrite pzipl_core_map_eq.
    set (ps' := (λ ly : layout, pzipl_core_map_fun (existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))).
    rewrite (pad_struct_ext _ (pzipl_core_map_fun <$> _) _ ps'); first last.
    { intros. unfold ps', pzipl_core_map_fun. simpl. f_equiv.
      normalize_dep_rt_goal. }
    intros ->.
    rewrite pad_struct_fmap.
    rewrite big_sepL_fmap.
    iApply big_sepL_proper.
    iIntros (? [lt r0] Hlook).
    specialize (lty_core_rt_eq' lt) as Heq2.
    apply pad_struct_lookup_Some_1 in Hlook as (n & ly & ? & [[_ Hlook] | [_ Huninit]]).
    + eapply pzipl_lookup_inv in Hlook.
      f_equiv => ly'. f_equiv. f_equiv. { simpl. f_equiv. f_equiv. rewrite lty_core_syn_type_eq //. }
      unshelve rewrite IH; first last. { by eapply list_elem_of_lookup_2. }
      2: { simpl. apply (eq_sym Heq2). }
      simpl.
      apply list_elem_of_lookup_2 in Hlook.
      rewrite -!IH; done.
    + injection Huninit as -> ->.
      normalize_dep_rt_goal.
      do 4 f_equiv.
      destruct core.
      * by iApply lty_own_pre_rfn_eq'.
      * simp lty_own_pre; done.
  Qed.

  Local Lemma ArrayLty_own_core_equiv_lift {rt} core st ly (lts : list lty) (r' : list (place_rfn rt)) π l k :
    (∀ lt : lty, lt ∈ lts → ∀ k π r (Heq : RT_rt (lty_rt lt) = RT_rt (lty_rt (lty_core lt))) l,
      lty_own_pre true lt k π (r) l ≡ lty_own_pre core (lty_core lt) k π (transport_rfn Heq r) l) →
    ([∗ list] i ↦ ty ∈ zip (fmap lty_core lts) r', ∃ Heq : RT_rt (lty_rt ty.1) = RT_rt rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre core ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)) ⊣⊢
    ([∗ list] i ↦ ty ∈ zip lts r', ∃ Heq : RT_rt (lty_rt ty.1) = RT_rt rt, ⌜lty_st ty.1 = st⌝ ∗ lty_own_pre true ty.1 k π (rew <- [place_rfn] Heq in ty.2) (l offset{ly}ₗ i)).
  Proof.
    intros IH.
    rewrite zip_fmap_l big_sepL_fmap.
    apply big_sepL_proper.
    intros ? [lt r] Hlook.
    apply lookup_zip in Hlook as [Hlook1 Hlook2].
    assert (RT_rt (lty_rt (lty_core lt)) = RT_rt (lty_rt lt)) as Heq3. { rewrite lty_core_rt_eq'. done. }
    simpl in *. iSplit.
    - iIntros "(%Heq & %Hst & Hb)". assert (Heq2 : RT_rt (lty_rt lt) = RT_rt rt). { rewrite -lty_core_rt_eq'. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq in Hst. iSplitR; first done.
      apply list_elem_of_lookup_2 in Hlook1.
      unshelve rewrite IH; [ done | | done].
      normalize_dep_rt_goal.
    - iIntros "(%Heq & %Hst & Hb)". assert (Heq2 : RT_rt (lty_rt (lty_core lt)) = RT_rt rt).
      { rewrite lty_core_rt_eq'. done. }
      iExists Heq2. rewrite lty_core_syn_type_eq. iSplitR; first done.
      apply list_elem_of_lookup_2 in Hlook1. unshelve rewrite IH; [done | | done].
      normalize_dep_rt_goal.
  Qed.

  Lemma lty_own_core_equiv (lt : lty) core k π r l Heq :
    lty_own_pre true lt k π r l ≡ lty_own_pre core (lty_core lt) k π (transport_rfn Heq r) l.
  Proof.
    rewrite /lty_own_core /lty_own.
    induction lt as [ | | | | lt IH κ | lt IH κ | lts IH sls | def len lts IH IH' | rt en variant IH | | | | ] using lty_induction in k, π, r, l, Heq, core |-*; simpl in *.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - simp lty_own_pre. rewrite (UIP_refl _ _ Heq). done.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq' lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      f_equiv.
      3: unshelve setoid_rewrite (lty_own_core_core' lt); [ done | ].
      all: unshelve setoid_rewrite (IH core); [done.. | ].
      all: normalize_dep_rt_goal_prepare.
      all: generalize (RT_rt (lty_rt lt)) => ?.
      all: normalize_dep_rt_goal.
    - simp lty_own_pre. fold lty_rt.
      specialize (lty_core_rt_eq' lt) as Heq2.
      do 5 f_equiv.
      simpl. clear -IH Heq2.
      f_equiv.
      3: unshelve setoid_rewrite (lty_own_core_core' lt); [ done | ].
      all: unshelve setoid_rewrite (IH core); [done.. | ].
      all: normalize_dep_rt_goal_prepare.
      all: generalize (RT_rt (lty_rt lt)) => ?.
      all: normalize_dep_rt_goal.
    - simp lty_own_pre. fold lty_rt.
      do 5 f_equiv.
      { rewrite length_map. done. }
      normalize_dep_rt_goal_prepare. intros.
      do 2 f_equiv.
      all: simpl.
      all: setoid_rewrite big_sepL_P_eq.
      3: do 2 f_equiv; [normalize_dep_rt_goal | do 2 f_equiv].
      all: iSplit.
      all: iIntros "(%r' & Hrfn & Hb)".

      all: specialize (struct_core_rt_eq lts) as Heq2.
      all: first [iExists (rew [id] Heq2 in r') | iExists (rew <-[id] Heq2 in r')].

      all: iSplitL "Hrfn"; [ by normalize_dep_rt_goal | ].
      all: rewrite -(StructLty_own_core_equiv_lift _ _ _ _ ltac:(done)); [done | intros; apply IH; done | ].
      all: normalize_dep_rt_goal.
    - simp lty_own_pre. fold lty_rt.
      do 6 f_equiv.
      (*{ iPureIntro. rewrite Forall_fmap. eapply Forall_iff. intros []; done. }*)
      simpl.
      move: IH'.
      normalize_dep_rt_goal_pass.
      f_equiv.
      all: repeat f_equiv; try done.
      all: rewrite !big_sepL_P_eq.
      all: rewrite -OfTyLty_core_id.
      all: rewrite interpret_iml_fmap ArrayLty_own_core_equiv_lift; first done.
      all: intros ? [-> | []]%elem_of_interpret_iml_inv; simpl; intros ??? Heq ?.
      all: simp lty_own_pre.
      all: normalize_dep_rt_goal.
    - (* enum *)
      simp lty_own_pre. fold lty_rt.
      rewrite (UIP_refl _ _ Heq). clear Heq. simpl.
       destruct variant as [v | ]; simpl in *; last first.
      { rewrite /transport_rfn /=.
        destruct k; simpl; try done;
         repeat f_equiv; destruct core; simp lty_own_pre; done. }
       rewrite /enum_lty_variant_tag_compat /enum_lty_variant_compat /enum_lty_variant_payload_compat /=.
      destruct k; simpl; try done.
      + rewrite /transport_rfn /=.
        do 12 f_equiv.
        all: destruct (decide (enum_tag en a0 = Some v.(elv_tag))); simpl in *; try done.
        2: repeat f_equiv; destruct core; simp lty_own_pre; done.
        all: try rewrite lty_core_syn_type_eq.
        all: do 5 f_equiv.
        iSplit.
        * iIntros "(%Heq & Ha)".
          assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
        * iIntros "(%Heq & Ha)".
          assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq. rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
      + rewrite /transport_rfn /=.
        do 13 f_equiv.
        all: destruct (decide (enum_tag en a0 = Some v.(elv_tag))); simpl in *; try done.
        2: repeat f_equiv; destruct core; simp lty_own_pre; done.
        all: try rewrite lty_core_syn_type_eq.
        all: do 5 f_equiv.
        iSplit.
        * iIntros "(%Heq & Ha)".
          assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
        * iIntros "(%Heq & Ha)".
          assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq. rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
      + rewrite /transport_rfn /=.
        rewrite /enum_lty_variant_tag_compat /enum_lty_variant_compat /enum_lty_variant_payload_compat /=.
        do 16 f_equiv.
        all: destruct (decide (enum_tag en a0 = Some v.(elv_tag))); simpl in *; try done.
        3: repeat f_equiv; destruct core; simp lty_own_pre; done.
        all: try rewrite lty_core_syn_type_eq.
        all: do 5 f_equiv.
        all: iSplit.
        all: iIntros "(%Heq_lty & Ha)".
        * assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH true). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
        * assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq_lty lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH true). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
        * assert (Heq2 : RT_rt (lty_rt (lty_core v.(elv_lty))) = RT_rt v.(elv_rt)).
          { rewrite lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
        * assert (Heq2 : RT_rt (lty_rt v.(elv_lty)) = RT_rt v.(elv_rt)).
          { rewrite -Heq_lty lty_core_rt_eq'//. }
          iExists Heq2.
          unshelve rewrite (IH core). { symmetry. apply lty_core_rt_eq'. }
          iApply (lty_own_pre_rfn_eq with "Ha").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
    - simp lty_own_pre.
    - simp lty_own_pre.
    - rewrite (UIP_refl _ _ Heq). simp lty_own_pre. done.
  Qed.

  Local Lemma lty_own_to_core_ofty {rt} (def : type rt) (r1 : place_rfn rt) (lt1 : lty) k π Heq l (Heq2 : RT_rt (lty_rt lt1) = RT_rt rt) :
    lt1 = OfTyLty def →
    lty_own_pre false lt1 k π (rew <- [place_rfn] Heq2 in r1) l -∗
    lty_own_pre false (lty_core lt1) k π (rew <-[place_rfn] Heq in r1) l.
  Proof.
    intros Ha. subst lt1. simpl.
    iApply lty_own_pre_rfn_eq.
    normalize_dep_rt_goal.
  Qed.

  Lemma lty_own_shared_to_core lt κ0 π r l Heq :
    lty_own lt (Shared κ0) π r l -∗ lty_own (lty_core lt) (Shared κ0) π (transport_rfn Heq r) l.
  Proof.
    rewrite /lty_own_core /lty_own.
    induction lt as [ | | | | lt IH κ | lt IH κ | lts IH sls | rt def len lts IH  | rt en variant IH | | | ???? IH1 IH2 | ] using lty_induction in κ0, π, r, l, Heq |-*; simpl in *.
    - simp lty_own_pre. iIntros "(% & _ & _ & _ & _ & [])".
    - simp lty_own_pre. iIntros "(% & _ & _ & _ & _ & % & _ & [])".
    - rewrite (UIP_refl _ _ Heq). auto.
    - rewrite (UIP_refl _ _ Heq). auto.
    - simp lty_own_pre. fold lty_rt.
      iIntros "(%ly & %Halg & %Hly & Hlb & %r' & %γ & Ha & #Hl)".
      iExists ly. iR. iR. iFrame.
      specialize (lty_core_rt_eq' lt) as Heq'.
      iExists (rew <-[place_rfn] Heq' in r'), γ.
      iSplitL "Ha".
      { iClear "Hl".
        normalize_dep_rt_goal_prepare.
        generalize (RT_rt (lty_rt lt)).
        normalize_dep_rt_goal. }
      iModIntro. iMod "Hl" as "(%vi & %li & Hf & %Hdec & Hl)". iModIntro. iExists vi, li. iFrame.
      iSplitR; first done.
      iNext. iApply IH. done.
    - simp lty_own_pre. fold lty_rt.
      iIntros "(%ly & %Halg & %Hly & Hlb & %r' & Ha & #Hl)".
      iExists ly. iR. iR. iFrame.
      specialize (lty_core_rt_eq' lt) as Heq'.
      iExists (rew <-[place_rfn] Heq' in r').
      iSplitL "Ha".
      { iClear "Hl". clear -Heq'.
        normalize_dep_rt_goal_prepare.
        generalize (RT_rt (lty_rt lt)).
        normalize_dep_rt_goal. }
      iModIntro. iMod "Hl" as "(%vi & %li & Hf & %Hdec & Hl)". iModIntro. iExists vi, li. iFrame.
      iSplitR; first done.
      iApply IH. done.
    - (* struct *)
      simp lty_own_pre. fold lty_rt.
      iIntros "(%sl & %Halg & %Hlen & %Hly & Hlb & %r' & Ha & #Hl)".
      rewrite big_sepL_P_eq.
      iExists sl. iR.
      rewrite length_fmap. iR. iR. iFrame.
      (*set (Heq' := lty_core_rt_eq ).*)
      simpl in r'.
      simpl.

      all: specialize (struct_core_rt_eq lts) as Heq2.
      all: first [iExists (rew [id] Heq2 in r') | iExists (rew <-[id] Heq2 in r')].
      all: iSplitL "Ha"; first normalize_dep_rt_goal.
      iModIntro. iMod "Hl". iModIntro.
      rewrite big_sepL_P_eq.
      rewrite pzipl_core_map_eq.
      rewrite rew_compose rew_UIP.
      rewrite (pad_struct_ext _ (_ <$> _) _ (λ ly, pzipl_core_map_fun (existT (UninitLty (LiteralSynType ly)) (PlaceIn ())))); first last.
      { intros ly; rewrite /pzipl_core_map_fun. f_equiv. rewrite rew_UIP'//. }
      rewrite pad_struct_fmap big_sepL_fmap.
      iApply (big_sepL_wand with "Hl").
      iApply big_sepL_intro. iModIntro.
      iIntros (? [? ] Hlook) "(%ly & % & % & Ha)".
      iExists ly. iR. simpl. rewrite lty_core_syn_type_eq. iR.
      apply pad_struct_lookup_Some in Hlook; first last.
      { rewrite length_pzipl. rewrite -Hlen.
        erewrite struct_layout_spec_has_layout_fields_length; done. }
      destruct Hlook as (n & ly' & Hlook & [(? & Hlook2) | (-> & Hlook2)]).
      + apply pzipl_lookup_inv in Hlook2.
        iApply (IH with "Ha"). by eapply list_elem_of_lookup_2.
      + injection Hlook2. intros _ ->.
        apply existT_inj in Hlook2 as ->.
        simpl. rewrite rew_UIP'. done.
    - (* array *)
      simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hsz & %Hly & Hlb & %r' & Ha & #Hl)".
      rewrite big_sepL_P_eq.
      iExists ly. iR. iR. iR. iFrame.
      (*set (Heq' := lty_core_rt_eq ).*)
      iExists (rew [id]Heq in r').
      iSplitL "Ha". { normalize_dep_rt_goal. }
      iModIntro. iMod "Hl" as "(%Hlen & Hl)". iModIntro.
      iSplitR. { rewrite -Hlen. iPureIntro. clear. rewrite (UIP_refl _ _ Heq). done. }
      rewrite big_sepL_P_eq.
      assert (OfTyLty def = lty_core $ OfTyLty def) as Hcore_eq. { done. }
      iEval (rewrite Hcore_eq).
      rewrite interpret_iml_fmap.
      rewrite zip_fmap_l big_sepL_fmap.
      rewrite (UIP_refl _ _ Heq).
      iApply (big_sepL_wand with "Hl"). iApply big_sepL_intro.
      iModIntro. iIntros (k [lt1 r1] Hlook) "(%Heq1 & %Hst & Hl)".
      simpl in Heq1, Hst.

      Set Printing Coercions.
      unshelve iExists _. { simpl. rewrite lty_core_rt_eq'. done. }
      rewrite lty_core_syn_type_eq. iR.
      apply lookup_zip in Hlook as (Hlook & _). apply lookup_interpret_iml_Some_inv in Hlook as [? [Ha | Ha]].
      + unshelve iApply lty_own_to_core_ofty; [ | done | done | ]. done.
      + unshelve iPoseProof (IH with "Hl") as "Hl"; [ | | done | ].
        { by rewrite lty_core_rt_eq'. }
        iApply (lty_own_pre_rfn_eq with "Hl").
        simpl.
        unfold transport_rfn.
        normalize_dep_rt_goal.
    - (* enum *)
      simp lty_own_pre.
      rewrite (UIP_refl _ _ Heq). clear Heq.
      iIntros "(%el & %Hel & %Hly & Hlb & %r' & Hrfn & #Hown)".
      iExists el.
      do 2 (iSplitR; first done).
      iSplitL "Hlb"; [iFrame | ].
      iExists r'. iSplitL "Hrfn"; [done | ].
      destruct variant as [v | ]; simpl in *.
      + destruct (decide (enum_tag en r' = Some v.(elv_tag))); simpl in *.
        * iModIntro. iMod "Hown" as "(%variant_ly & %Htag & %Hvariant & %Hst & Hdisc & Hpad1 & Hdata & Hpad2)". iModIntro.
          iExists variant_ly. iR. rewrite lty_core_syn_type_eq. iR. iR.
          iFrame "Hdisc Hpad1 Hpad2".
          iDestruct "Hdata" as "(%Heq1 & Hdata)".
          unshelve iExists _. { rewrite lty_core_rt_eq'. done. }
          iPoseProof (IH κ0 π _ _ (eq_sym (lty_core_rt_eq' v.(elv_lty))) with "Hdata") as "Hdata".
          iApply (lty_own_pre_rfn_eq with "Hdata").
          rewrite /transport_rfn.
          normalize_dep_rt_goal.
        * iModIntro. iMod "Hown" as "(%variant_ly & %Htag & %Hvariant & %Hst & Hdisc & Hpad1 & Hdata & Hpad2)". iModIntro.
          iExists variant_ly. iR. iR. iR.
          iFrame "Hdisc Hpad1 Hpad2".
          iDestruct "Hdata" as "(%Heq1 & Hdata)".
          iExists Heq1. iExact "Hdata".
      + iModIntro. iMod "Hown" as "(%variant_ly & %Htag & %Hvariant & %Hst & Hdisc & Hpad1 & Hdata & Hpad2)". iModIntro.
        iExists variant_ly. iR. iR. iR.
        iFrame "Hdisc Hpad1 Hpad2".
        iDestruct "Hdata" as "(%Heq1 & Hdata)".
        iExists Heq1. iExact "Hdata".
    - simp lty_own_pre.
      iIntros "(%ly & % & % & ? & % & % & [])".
    - simp lty_own_pre.
      iIntros "(%ly & %Halg & %Hly & Hlb & Hown)".
      clear. rewrite -lty_own_core_equiv. done.
    - simp lty_own_pre.
      iIntros "(%Heq_cur & Ha & Hb)".
      iApply (IH2 with "Hb").
    - simp lty_own_pre.
      iIntros "(%ly & % & % & ? & % & [])".
  Qed.
  (* NOTE: The reverse does not hold because the core of [BlockedLty] is [OfTy], which has a sharing predicate, but [BlockedLty] doesn't *)
End ltype_def.

(** Export the dependent-equality automation for downstream high-level ltypes. *)
Ltac normalize_dep_rt_goal_prepare :=
  simpl in *;
  repeat match goal with
  | H : place_rfn _ |- _ => revert H
  | H : plist _ _ |- _ => revert H
  end;
  repeat match goal with
  | |- context[rew [_] ?Heq in _] =>
      assert_fails (is_var Heq); generalize Heq
  | |- context[rew <-[_] ?Heq in _] =>
      assert_fails (is_var Heq); generalize Heq
  end;
  simpl in *;
  repeat match goal with
  | H : _ = _ |- _ => revert H
  end.

Ltac normalize_dep_rt_goal_pass :=
  clear;
  normalize_dep_rt_goal_prepare;
  repeat match goal with
  | |- context[plist (?a ∘ ?b) _] => rewrite (plist_fmap_shift a b)
  end;
  repeat lazymatch goal with
  | |- ∀ (_ : ?A = ?B), _ =>
      first [
        intros [] |
        unify A B;
        let H := fresh "H" in
        intros H; rewrite (UIP_refl _ _ H); clear H |
        intros -> |
        intros <- |
        intros ?
      ]
  | |- _ => intros ?
  end;
  try done.

Ltac normalize_dep_rt_goal :=
  repeat normalize_dep_rt_goal_pass.
