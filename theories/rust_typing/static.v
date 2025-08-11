From refinedrust Require Import base type ltypes programs shr_ref.
From iris.base_logic Require Import ghost_map.
From refinedrust Require Import options.

(** * Support for static variables *)

Record btype `{!typeGS Σ} : Type := {
  btype_rt : RT;
  btype_ty : type btype_rt;
  btype_r : btype_rt;
}.

Definition btype_to_rtype `{!typeGS Σ} (ty : btype) : sigT type :=
  existT _ ty.(btype_ty).

(* TODO: should require that type is Send? *)
Class staticGS `{!typeGS Σ} := {
  static_locs : gmap string loc;
  static_types : gmap string btype;
}.
Global Arguments staticGS _ {_}.

Section statics.
  Context `{!typeGS Σ} `{!staticGS Σ}.

  Import EqNotations.

  (** Assertion stating that the static with name [x] has been registered for location [l] and type [ty]. *)
  (** We assume registration for the expected type and the location parameter in the context where we verify our code *)
  Definition static_is_registered (x : string) (l : loc) (ty : sigT type) :=
    static_locs !! x = Some l ∧ btype_to_rtype <$> (static_types !! x) = Some ty.

  (** In our specifications, we can use this assertion to assume a refinement for the static *)
  Definition static_has_refinement (x : string) {rt} (r : rt) :=
    ∃ ty, static_types !! x = Some ty ∧ ∃ (Heq : rt = ty.(btype_rt)), (rew [id] Heq in r) = ty.(btype_r).

  Lemma static_has_refinement_inj {rt1 rt2} (r1 : rt1) (r2 : rt2) name :
    static_has_refinement name r1 →
    static_has_refinement name r2 →
    ∃ (Heq : rt1 = rt2), rew Heq in r1 = r2.
  Proof.
    intros (ty1 & Hlook1 & Heq1 & Ha).
    intros (ty2 & Hlook2 & Heq2 & Hb).
    simplify_eq. exists eq_refl.
    simpl in *. by subst.
  Qed.

  Global Instance simpl_and_static_has_refinement {rt} (x y : rt) `{!TCFastDone (static_has_refinement name x)} :
    SimplBoth (static_has_refinement name y) (x = y).
  Proof.
    split; last naive_solver.
    rename select (TCFastDone _) into Hs. unfold TCFastDone in Hs.
    intros Ha. destruct (static_has_refinement_inj _ _ _ Hs Ha) as (Heq & <-).
    rewrite (UIP_refl _ _ Heq).
    done.
  Qed.

  (* The global variable "name" has been initialized *)
  Definition initialized (π : thread_id) (name : string) : iProp Σ :=
    ∃ (l : loc) (ty : btype), ⌜static_locs !! name = Some l⌝ ∗ ⌜static_types !! name = Some ty⌝ ∗
        (l ◁ᵥ{π} (#ty.(btype_r)) @ shr_ref static ty.(btype_ty))%I.

  Global Instance initialized_persistent (π : thread_id) (name : string) :
    Persistent (initialized π name).
  Proof. apply _. Qed.

  (*Global Instance initialized_intro_persistent (π : thread_id) name :*)
    (*IntroPersistent (initialized π name) (initialized π name).*)
  (*Proof. constructor. iIntros "#$". Qed.*)

  (* On introduction of `initialized`, destruct it *)
  Lemma simplify_initialized_hyp π name ty l
    `{!TCFastDone (static_is_registered name l ty)} T:
    (∀ r, (□ l ◁ᵥ{π} (#r) @ shr_ref static (projT2 ty)) -∗ ⌜static_has_refinement name r⌝ -∗ T)
    ⊢ simplify_hyp (initialized π name) T.
  Proof.
    unfold TCFastDone in *. destruct ty as [rt' ty].
    iDestruct 1 as "HT". subst; simpl in *.
    iIntros "Hinit".
    iDestruct "Hinit" as "(%l' & %ty' & %Hlook1 & %Hlook2 & #Hl)".
    destruct ty'; simpl in *.
    repeat match goal with | H : static_is_registered _ _ _ |- _ => destruct H as [H1 H2] end.
    apply fmap_Some in H2 as ([] & H2 & Hb).
    simplify_eq. unfold btype_to_rtype in Hb; simpl in *.
    injection Hb. intros ? ->.
    repeat match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end.
    subst. iApply ("HT" with "Hl").
    iPureIntro. eexists _. split; first done. exists eq_refl. done.
  Qed.
  Definition simplify_initialized_hyp_inst := [instance @simplify_initialized_hyp with 0%N].
  Global Existing Instance simplify_initialized_hyp_inst.

  Lemma initialized_intro {rt : RT} π ty name l (x : rt) :
    static_is_registered name l ty →
    static_has_refinement name x →
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew [place_rfnRT] Heq in #x) @ shr_ref static (projT2 ty)) -∗
    initialized π name.
  Proof.
    iIntros ([Hl1 Hl2] (ty2 & Hl3 & Heq' & Hb)) "(%Heq & #Hl)".
    subst. destruct ty. destruct ty2. simpl in *.
    apply fmap_Some in Hl2 as (bt & Hl2 & Ha). subst.
    destruct bt. simpl in *.
    unfold btype_to_rtype in Ha; simpl in *.
    simplify_eq.
    repeat match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end.
    subst.
    iExists _, _. iR. iR.
    simpl. cbn.
    rewrite (UIP_refl _ _ Heq').
    done.
  Qed.

  Lemma simplify_initialized_goal {rt : RT} π (x : rt) name l ty
    `{!TCFastDone (static_is_registered name l ty)} `{!TCFastDone (static_has_refinement name x)} T:
    (∃ (Heq : rt = projT1 ty), l ◁ᵥ{π} (rew [place_rfnRT] Heq in #x) @ shr_ref static (projT2 ty) ∗ T)
    ⊢ simplify_goal (initialized π name) T.
  Proof.
    unfold TCFastDone in *. iIntros "[% [? $]]". subst.
    iApply initialized_intro; [done..|]. by iExists _.
  Qed.
  Definition simplify_initialized_goal_inst := [instance @simplify_initialized_goal with 0%N].
  Global Existing Instance simplify_initialized_goal_inst.

  (** Subsumption *)
  Definition FindInitialized (π : thread_id) (name : string) :=
    {| fic_A := unit: Type; fic_Prop '() := (initialized π name); |}.
  Global Instance related_to_initialized (π : thread_id) name :
    RelatedTo (initialized π name) :=
    {| rt_fic := FindInitialized π name|}.

  Lemma find_in_context_initialized π name (T : unit → iProp Σ):
    (initialized π name ∗ T ())
    ⊢ find_in_context (FindInitialized π name) T.
  Proof. iDestruct 1 as "[Hinit HT]". iExists _. iFrame. Qed.
  Definition find_in_context_initialized_inst :=
    [instance find_in_context_initialized with FICSyntactic].
  Global Existing Instance find_in_context_initialized_inst | 1.

  (*Lemma subsume_initialized π {rt} name (r1 r2 : rt) T:*)
    (*(⌜r1 = r2⌝ ∗ T)*)
    (*⊢ subsume (initialized π name r1) (initialized π name r2) T.*)
  (*Proof. iIntros "(-> & HT) ?". iFrame. Qed.*)
  (*Definition subsume_initialized_inst := [instance subsume_initialized].*)
  (*Global Existing Instance subsume_initialized_inst.*)
End statics.
Global Typeclasses Opaque initialized.
Global Typeclasses Opaque static_has_refinement.

Global Arguments static_has_refinement : simpl never.
Global Arguments static_is_registered : simpl never.


(* After calling adequacy:
    we need to create initialized things.
    then we can provide them to the proof.

   Users of initialized should unpack that hypothesis to get access to the type assignment.
   This type assignment then allows us to call methods etc on the global variable.

 *)


