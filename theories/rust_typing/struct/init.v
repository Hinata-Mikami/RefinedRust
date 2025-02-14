From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def.
From refinedrust Require Import options.

(** ** Initialization rule for structs *)

Section init.
  Context `{!typeGS Σ}.

  (** Struct initialization *)
  Fixpoint struct_init_fold π E L (fields : list (string * expr)) (sts : list (string * syn_type)) (T : ∀ (L : llctx) (rts : list RT), list val → hlist type rts → plist (@id RT) rts → iProp Σ) : iProp Σ :=
    match sts with
    | [] =>
        T L [] [] +[] -[]
    | (name, st) :: sts =>
        (* TODO should have a faster way to do the lookup *)
        ∃ init, ⌜(list_to_map (M:=gmap _ _) fields) !! name = Some init⌝ ∗
        typed_val_expr E L init (λ L2 π2 v rt ty r,
        ⌜π = π2⌝ ∗
        ⌜ty.(ty_syn_type) = st⌝ ∗
        struct_init_fold π E L2 fields sts (λ L3 rts vs tys rs,
            T L3 (rt :: rts) (v :: vs) (ty +:: tys) (r -:: rs)))%I
    end.

  Lemma struct_init_fold_elim π E L fields sts T Φ :
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    struct_init_fold π E L fields sts T -∗
    (∀ vs L3,
      llctx_interp L3 -∗
      (∃ (rts : list RT) (tys : hlist type rts) (rs : plist (@id RT) rts),
      (* get a type assignment for the values *)
      ⌜length rts = length (sts)⌝ ∗
      ([∗ list] i ↦ v; Ty ∈ vs; hpzipl rts tys rs,
        let '(existT rt (ty, r)) := Ty in
        ∃ name st ly, ⌜sts !! i = Some (name, st)⌝ ∗ ⌜syn_type_has_layout st ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty) ly⌝ ∗
        v ◁ᵥ{ π} r @ ty
      ) ∗
      T L3 rts vs tys rs) -∗ Φ vs) -∗
    struct_init_components ⊤ sts fields Φ
  .
  Proof.
    iIntros "#CTX #HE HL Hf Hcont".
    iInduction sts as [ | [name st] sts] "IH" forall (fields L  Φ T).
    { simpl.
      iApply ("Hcont" with "HL"). iExists [], +[], -[]. simpl. eauto. }
    simpl. iDestruct "Hf" as (init Hlook) "Hf".
    (* maybe want to phrase also with custom fold instead of foldr? *)
    iIntros (ly) "%Hst". simpl.
    iPoseProof ("Hf" with "CTX HE HL") as "Ha".
    rewrite Hlook/=.
    iApply (wp_wand with "(Ha [Hcont])").
    2: { eauto. }
    iIntros (L2 π2 v rt ty r) "HL Hv (<- & <- & Hr)".
    iApply ("IH" with "HL Hr").
    iIntros (vs L3) "HL Hc".
    iApply ("Hcont" with "HL").
    iDestruct "Hc" as (rts tys rs) "(%Hlen & Ha & HT)".
    iExists (rt :: rts), (ty +:: tys), (r -:: rs).
    iFrame. iSplitR. { rewrite /=Hlen//. }
    iExists name, (ty_syn_type ty). iExists ly.
    iR. done.
  Qed.

  Lemma type_struct_init E L (sls : struct_layout_spec) (fields : list (string * expr)) (T : typed_val_expr_cont_t) :
    (* find out which thread_id we need *)
    find_in_context FindNaOwn (λ '(π, mask), na_own π mask -∗
    li_tactic (compute_struct_layout_goal sls) (λ sl,
    struct_init_fold π E L fields sls.(sls_fields) (λ L2 rts vs tys rs,
      ∀ v, T L2 π v _ (struct_t sls tys) (pmap (λ _ a, #a) rs))))
    ⊢ typed_val_expr E L (StructInit sls fields) T.
  Proof.
    iIntros "HT". iDestruct "HT" as ([π mask]) "(Hna & HT)".
    rewrite /compute_struct_layout_goal.
    iDestruct ("HT" with "Hna") as (sl) "(%Hsl & HT)".
    iIntros (?) "#CTX #HE HL Hc".
    iApply wp_struct_init2; first done.
    iApply (struct_init_fold_elim with "CTX HE HL HT").
    iIntros (vs L3) "HL Ha".
    iDestruct "Ha" as (rts tys rs) "(%Hlen & Hv & HT)".
    iApply ("Hc" with "HL [Hv] HT").
    simpl. by iApply struct_init_val.
  Qed.

End init.
