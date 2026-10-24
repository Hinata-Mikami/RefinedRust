From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.gc.generated Require Import generated_code_gc generated_specs_gc generated_template_drop_glue_Heap.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* The Vec-specific resolvers in stdlib/vec/extra_specs.v are admitted.
   Sweep only carries concrete pointer lists, so use the proved generic
   ghost-resolution rules instead. This changes automation, not obligations. *)
#[local] Remove Hints
  generated_specs_vec.resolve_ghost_Vec_T_owned_inst
  generated_specs_vec.resolve_ghost_Vec_T_uniq_inst : typeclass_instances.

Local Lemma resolve_ghost_Vec_concrete
    {T_rt : RT} (T_ty : type T_rt) {A_rt : RT} (A_ty : type A_rt)
    A_attrs π E L rm lb l bk rs T :
  T L (#rs) True false ⊢
  resolve_ghost π E L rm lb l
    (◁ (Vec_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>)) bk (#rs) T.
Proof. apply resolve_ghost_ofty_default. Qed.
Local Definition resolve_ghost_Vec_concrete_inst :=
  [instance @resolve_ghost_Vec_concrete].
Local Existing Instance resolve_ghost_Vec_concrete_inst | 1.

Lemma drop_glue_Heap_proof (π : thread_id) :
  drop_glue_Heap_lemma π.
Proof.
  drop_glue_Heap_prelude.

  1: rep <-! <3000 liRStep.
  all: liShow.

  (* Each guarded node carries the credits needed to expose its ownership. *)
  iRename select
    ([∗ list] i ↦ v ∈ _, ∃ (l n : loc) (m : bool), _)%I into "Hnodes".
  apply_update updateable_add_fupd.
  iAssert (@fupd (iPropI Σ) _ ⊤ ⊤ (
    [∗ list] i ↦ v ∈ (id <$> x),
      ∃ (l n : loc) (m : bool),
        ⌜(id <$> x0) !! i = Some l⌝ ∗
        ⌜(id <$> x1) !! i = Some n⌝ ∗
        ⌜(id <$> x2) !! i = Some m⌝ ∗
        (l ◁ₗ[π, Owned] # -[#v; #n; #m] @ ◁ (Node_ty <INST!>)) ∗
        freeable_nz l (ly_size (use_layout_alg' Node_sls)) 1 HeapAlloc)%I)
    with "[Hnodes]" as ">Hnodes".
  {
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hnodes").
    iIntros "!>" (i v0 Hlookup) "(%l & %n & %m & %Hl & %Hn & %Hm & Hguard & Hfree)".
    iEval (rewrite /guarded /maybe_creds /have_creds /num_cred /=) in "Hguard".
    iDestruct "Hguard" as "[[Hcredit _] Hnode]".
    iDestruct (lc_weaken 1 with "Hcredit") as "Hcredit"; first lia.
    iMod (lc_fupd_elim_later with "Hcredit Hnode") as "Hnode".
    iModIntro. iExists l, n, m. iFrame. done.
  }
  iModIntro.
  iApply type_val.
  iApply type_val_unit.
  1: rep <-! <3000 liRStep.
  all: liShow.
  iApply prove_with_subtype_default.
  iSplitL "Hnodes".
  {
    iApply (big_sepL_impl with "Hnodes").
    iIntros "!>" (i v0 Hlookup) "(%l & %n & %m & %Hl & %Hn & %Hm & Hnode & Hfree)".
    iExists l, n, m.
    rep liRStep; liShow.
  }
  1: rep <-! <3000 liRStep.
  all: liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
