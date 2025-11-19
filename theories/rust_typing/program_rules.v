From stdpp Require Import gmap.
From caesium Require Import lang proofmode derived lifting.
From refinedrust Require Export base type lft_contexts annotations ltypes programs.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import options.

(** * Core rules of the type system *)

Section typing.
  Context `{typeGS Σ}.

  Implicit Types (rt : RT).

  (* NOTE: find_in_context instances should always have a sep conj in their premise, even if the LHS is just [True].
      This is needed by the liFindInContext/ liFindHypOrTrue automation!
  *)

  (** Instances so that Lithium knows what to search for when needing to provide something *)
  (** For locations and values, we use the ones that also find a refinement type, since it may be desirable to change it (consider e.g. changing to uninit) *)
  Global Instance related_to_loc l π b {rt} (lt : ltype rt) (r : place_rfn rt) : RelatedTo (l ◁ₗ[π, b] r @ lt)  | 100 :=
    {| rt_fic := FindLocP l |}.
  Global Instance related_to_val v π {rt} (ty : type rt) (r : rt) : RelatedTo (v ◁ᵥ{π} r @ ty)  | 100 :=
    {| rt_fic := FindValP v |}.
  (* TODO: need a relatedto for shared ownership? *)

  Global Instance related_to_named_lfts M : RelatedTo (named_lfts M) | 100 :=
    {| rt_fic := FindNamedLfts |}.

  Global Instance related_to_gvar_pobs {rt} γ (r : rt) : RelatedTo (gvar_pobs γ r) | 100 :=
    {| rt_fic := FindGvarPobsP γ |}.

  Global Instance related_to_credit_store n m : RelatedTo (credit_store n m) | 100 :=
    {| rt_fic := FindCreditStore |}.

  Global Instance related_to_na_own π E : RelatedTo (na_own π E) | 100 :=
    {| rt_fic := FindNaOwn |}.

  Global Instance related_to_freeable l n q k : RelatedTo (freeable_nz l n q k) | 100 :=
    {| rt_fic := FindFreeable l |}.

  Global Instance related_to_loc_in_bounds l pre suf : RelatedTo (loc_in_bounds l pre suf) | 100 :=
    {| rt_fic := FindLocInBounds l |}.

  (* TODO instances needed for the other things? *)

  (** Value ownership *)
  Lemma find_in_context_type_val_id v T :
    (∃ π rt (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T (existT rt (ty, r, π)))
    ⊢ find_in_context (FindVal v) T.
  Proof. iDestruct 1 as (π rt ty r) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_id_inst v :
    FindInContext (FindVal v) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_val_id v T).

  Lemma find_in_context_type_valp_id v T :
    (∃ π rt (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T (v ◁ᵥ{π} r @ ty))
    ⊢ find_in_context (FindValP v) T.
  Proof. iDestruct 1 as (π rt ty r) "(Hl & HT)". iExists (v ◁ᵥ{π} r @ ty)%I => /=. iFrame. Qed.
  Global Instance find_in_context_type_valp_id_inst v :
    FindInContext (FindValP v) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_valp_id v T).

  Lemma find_in_context_type_valp_loc l T :
    (∃ π rt (lt : ltype rt) r, l ◁ₗ[π, Owned false] r @ lt ∗ T (l ◁ₗ[π, Owned false] r @ lt))
    ⊢ find_in_context (FindValP (val_of_loc l)) T.
  Proof. iDestruct 1 as (π rt lt r) "(Hl & HT)". iExists (l ◁ₗ[π, Owned false] r @ lt)%I. iFrame. done. Qed.
  Global Instance find_in_context_type_valp_loc_inst l :
    FindInContext (FindValP (val_of_loc l)) FICSyntactic | 5 :=
    λ T, i2p (find_in_context_type_valp_loc l T).

  Lemma find_in_context_type_val_with_rt_id {rt} v π T :
    (∃ (ty : type rt) r, v ◁ᵥ{π} r @ ty ∗ T (ty, r))
  ⊢ find_in_context (FindValWithRt rt v π) T.
  Proof. iDestruct 1 as (ty r) "[Hl HT]". iExists _ => /=. iFrame. Qed.
Global Instance find_in_context_type_val_with_rt_id_inst {rt} π v :
    FindInContext (FindValWithRt rt v π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_val_with_rt_id v π T).

  (* TODO: generalize to different rt to handle typaram instantiation?*)
  Lemma own_val_subsume_id v π {rt} (r1 r2 : rt) (ty1 ty2 : type rt) T :
    ⌜r1 = r2⌝ ∗ ⌜ty1 = ty2⌝ ∗ T
    ⊢ subsume (Σ := Σ) (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "(-> & -> & $)"; eauto.
  Qed.
  Definition own_val_subsume_id_inst v π {rt} (r1 r2 : rt) (ty1 ty2 : type rt) :
    Subsume (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) :=
    λ T, i2p (own_val_subsume_id v π r1 r2 ty1 ty2 T).

  (** Location ownership *)
  Lemma find_in_context_type_loc_id l T:
    (∃ π rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (existT rt (lt, r, b, π)))
    ⊢ find_in_context (FindLoc l) T.
  Proof. iDestruct 1 as (π rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_id_inst l :
    FindInContext (FindLoc l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_loc_id l T).

  Lemma find_in_context_type_opt_loc_id l T:
    (∃ π rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (Some (existT rt (lt, r, b, π))))
    ⊢ find_in_context (FindOptLoc l) T.
  Proof. iDestruct 1 as (π rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_opt_loc_id_inst l :
    FindInContext (FindOptLoc l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_opt_loc_id l T).
  Lemma find_in_context_type_opt_loc_none l T:
    (True ∗ T None)
    ⊢ find_in_context (FindOptLoc l) T.
  Proof. iDestruct 1 as "[_ HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_opt_loc_none_inst l :
    FindInContext (FindOptLoc l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_type_opt_loc_none l T).

  Lemma find_in_context_type_locp_loc l T :
    (∃ π rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (l ◁ₗ[π, b] r @ lt))
    ⊢ find_in_context (FindLocP l) T.
  Proof. iDestruct 1 as (π rt lt r b) "[Hl HT]". iExists (l ◁ₗ[π, b] r @ lt)%I => /=. iFrame. Qed.
  Global Instance find_in_context_type_locp_loc_inst l :
    FindInContext (FindLocP l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_locp_loc l T).
  Lemma find_in_context_type_locp_val (l : loc) T :
    (∃ π rt (ty : type rt) r , l ◁ᵥ{π} r @ ty ∗ T (l ◁ᵥ{π} r @ ty))
    ⊢ find_in_context (FindLocP l) T.
  Proof. iDestruct 1 as (π rt ty r) "[Hl HT]". iExists (l ◁ᵥ{π} r @ ty)%I => /=. iFrame. Qed.
  (* NOTE: important: has lower priority! If there's a location assignment available, should just use that. *)
  Global Instance find_in_context_type_locp_val_inst l :
    FindInContext (FindLocP l) FICSyntactic | 2 :=
    λ T, i2p (find_in_context_type_locp_val l T).

  Lemma find_in_context_type_loc_with_rt_id {rt} l π T:
    (∃ (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (lt, r, b))
    ⊢ find_in_context (FindLocWithRt rt l π) T.
  Proof. iDestruct 1 as (lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_with_rt_id_inst {rt} π l :
    FindInContext (FindLocWithRt rt l π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_loc_with_rt_id l π T).

  (* used for unifying evars *)
  Lemma own_shr_subsume_id v π {rt} (r1 r2 : rt) (κ1 κ2 : lft) (ty : type rt) T :
    ⌜r1 = r2⌝ ∗ ⌜κ1 = κ2⌝ ∗ T
    ⊢ subsume (Σ := Σ) (v ◁ₗ{π, κ1} r1 @ ty) (v ◁ₗ{π, κ2} r2 @ ty) T.
  Proof.
    iIntros "(-> & -> & $)"; eauto.
  Qed.
  Definition own_shr_subsume_id_inst v π {rt} (r1 r2 : rt) (κ1 κ2 : lft) (ty : type rt) :
    Subsume (v ◁ₗ{π, κ1} r1 @ ty) (v ◁ₗ{π, κ2} r2 @ ty) :=
    λ T, i2p (own_shr_subsume_id v π r1 r2 κ1 κ2 ty T).

  (** NamedLfts *)
  Lemma subsume_named_lfts M M' `{!ContainsProtected M'} T:
    ⌜M = M'⌝ ∗ T ⊢ subsume (Σ := Σ) (named_lfts M) (named_lfts M') T.
  Proof. iIntros "(-> & $) $". Qed.
  Definition subsume_named_lfts_inst := [instance subsume_named_lfts].
  Global Existing Instance subsume_named_lfts_inst.

  (* Low priority instance for strong updates, in particular when doing loop proofs *)
  Lemma subsume_named_lfts_trivial M M' T:
    T ⊢ subsume (Σ := Σ) (named_lfts M) (named_lfts M') T.
  Proof. iIntros "$ Hb". iApply "Hb". Qed.
  Definition subsume_named_lfts_trivial_inst := [instance subsume_named_lfts_trivial].
  Global Existing Instance subsume_named_lfts_trivial_inst | 100.

  Lemma find_in_context_named_lfts T:
    (∃ M, named_lfts M ∗ T M) ⊢
    find_in_context FindNamedLfts T.
  Proof. iDestruct 1 as (M) "[Hn HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_named_lfts_inst :
    FindInContext FindNamedLfts FICSyntactic | 1 :=
    λ T, i2p (find_in_context_named_lfts T).

  (** CreditStore *)
  Lemma subsume_credit_store_evar n m n' m' T `{!ContainsProtected (credit_store n' m')}:
    ⌜n = n'⌝ ∗ ⌜m = m'⌝ ∗ T ⊢ subsume (Σ := Σ) (credit_store n m) (credit_store n' m') T.
  Proof.
    iIntros "(<- & <- & HT) $ //".
  Qed.
  Global Instance subsume_credit_store_evar_inst n m n' m' `{!ContainsProtected (credit_store n' m')} : Subsume (credit_store n m) (credit_store n' m') | 10 :=
    λ T, i2p (subsume_credit_store_evar n m n' m' T).

  Lemma subsume_credit_store n m n' m' T :
    ⌜n' ≤ n⌝ ∗ ⌜m' ≤ m⌝ ∗ T ⊢ subsume (Σ := Σ) (credit_store n m) (credit_store n' m') T.
  Proof.
    iIntros "(% & % & HT) Hc".
    iFrame. iApply (credit_store_mono with "Hc"); done.
  Qed.
  Global Instance subsume_credit_store_inst n m n' m' : Subsume (credit_store n m) (credit_store n' m') :=
    λ T, i2p (subsume_credit_store n m n' m' T).

  Lemma find_in_context_credit_store T :
    (∃ n m, credit_store n m ∗ T (n, m)) ⊢
    find_in_context FindCreditStore T.
  Proof.
    iDestruct 1 as (n m) "[Hc HT]". iExists (n, m). by iFrame.
  Qed.
  Global Instance find_in_context_credit_store_inst :
    FindInContext FindCreditStore FICSyntactic | 1 :=
    λ T, i2p (find_in_context_credit_store T).

  (** NaOwn *)
  Lemma subsume_na_own π E E' T :
    ⌜E' ⊆ E⌝ ∗ T ⊢ subsume (Σ := Σ) (na_own π E) (na_own π E') T.
  Proof.
    iIntros "(%Heq & $) Hna".
    by iDestruct (na_own_acc with "Hna") as "($ & Hna)".
  Qed.
  Global Instance subsume_na_own_inst π E E' : Subsume (na_own π E) (na_own π E') :=
    λ T, i2p (subsume_na_own π E E' T).

  Lemma find_in_context_na_own T :
    (∃ π E, na_own π E ∗ T (π, E)) ⊢
    find_in_context (FindNaOwn) T.
  Proof.
    iDestruct 1 as (π E) "[Hna HT]". iExists _. by iFrame.
  Qed.
  Global Instance find_in_context_na_own_inst :
    FindInContext (FindNaOwn) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_na_own T).

  Lemma find_in_context_opt_na_own_some T :
    (∃ π E, na_own π E ∗ T (Some (π, E))) ⊢
    find_in_context (FindOptNaOwn) T.
  Proof.
    iDestruct 1 as (π E) "[Hna HT]". iExists _. by iFrame.
  Qed.
  Global Instance find_in_context_opt_na_own_some_inst :
    FindInContext (FindOptNaOwn) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_na_own_some T).

  Lemma find_in_context_opt_na_own_none T :
    True ∗ T None
    ⊢ find_in_context (FindOptNaOwn) T.
  Proof.
    iIntros "(_ & ?)".
    iExists _; iFrame.
    by rewrite /FindOptNaOwn.
  Qed.
  Global Instance find_in_context_opt_na_own_none_inst :
    FindInContext (FindOptNaOwn) FICSyntactic | 2 :=
    λ T, i2p (find_in_context_opt_na_own_none T).

  (** FindOptLftDead *)
  Lemma subsume_lft_dead κ1 κ2 T :
    ⌜κ1 = κ2⌝ ∗ T ⊢ subsume (Σ := Σ) ([† κ1]) ([† κ2]) T.
  Proof. iIntros "(-> & $)". eauto. Qed.
  Global Instance subsume_lft_dead_inst κ1 κ2 :
    Subsume ([† κ1]) ([† κ2]) := λ T, i2p (subsume_lft_dead κ1 κ2 T).

  Lemma find_in_context_opt_lft_dead κ T :
    [† κ] ∗ T true
    ⊢ find_in_context (FindOptLftDead κ) T.
  Proof.
    iIntros "(Hdead & HT)". iExists true. iFrame. done.
  Qed.
  Global Instance find_in_context_opt_lft_dead_inst κ :
    FindInContext (FindOptLftDead κ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_lft_dead κ T).

  (* dummy instance in case we don't find it *)
  Lemma find_in_context_opt_lft_dead_none κ T :
    True ∗ T false
    ⊢ find_in_context (FindOptLftDead κ) T.
  Proof.
    iIntros "(_ & HT)". iExists false. iFrame. simpl. done.
  Qed.
  Global Instance find_in_context_opt_lft_dead_none_inst κ :
    FindInContext (FindOptLftDead κ) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_opt_lft_dead_none κ T).

  (** Freeable *)
  Lemma subsume_freeable l1 q1 n1 k1 l2 q2 n2 k2 T :
    ⌜l1 = l2⌝ ∗ ⌜n1 = n2⌝ ∗ ⌜q1 = q2⌝ ∗ ⌜k1 = k2⌝ ∗ T
    ⊢ subsume (freeable_nz l1 n1 q1 k1) (freeable_nz l2 n2 q2 k2) T.
  Proof.
    iIntros "(-> & -> & -> & -> & $)". eauto.
  Qed.
  Global Instance subsume_freeable_inst l1 q1 n1 k1 l2 q2 n2 k2 :
    Subsume (freeable_nz l1 n1 q1 k1) (freeable_nz l2 n2 q2 k2) :=
    λ T, i2p (subsume_freeable l1 q1 n1 k1 l2 q2 n2 k2 T).

  Lemma find_in_context_freeable l T :
    (∃ q n k, freeable_nz l n q k ∗ T (n, q, k))
    ⊢ find_in_context (FindFreeable l) T.
  Proof.
    iDestruct 1 as (q n k) "(Ha & HT)".
    iExists (n, q, k). by iFrame.
  Qed.
  Global Instance find_in_context_freeable_inst l :
    FindInContext (FindFreeable l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_freeable l T).

  Lemma simplify_hyp_freeable l n q k T :
    ((freeable_nz l n q k) -∗ T)
    ⊢ simplify_hyp (freeable l n q k) T.
  Proof.
    iIntros "Ha Hf". iApply "Ha".
    destruct n; done.
  Qed.
  Global Instance simplify_hyp_freeable_inst l n q k :
    SimplifyHyp (freeable l n q k) (Some 0%N) :=
    λ T, i2p (simplify_hyp_freeable l n q k T).


  (** FindOptGvarRel *)
  Lemma find_in_context_opt_gvar_rel γ T :
    (∃ rt (γ' : gname) (R : rt → rt → Prop), Rel2 γ' γ R ∗ T (inl (existT rt (γ', R))))
    ⊢ find_in_context (FindOptGvarRel γ) T.
  Proof.
    iIntros "(%rt & %γ' & %R & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_opt_gvar_rel_inst γ :
    FindInContext (FindOptGvarRel γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_gvar_rel γ T).

  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_gvar_rel_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptGvarRel γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_rel_dummy_inst γ :
    FindInContext (FindOptGvarRel γ) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_opt_gvar_rel_dummy γ T).

  Lemma subsume_gvar_rel {rt} γ1' γ1 γ2' γ2 (R1 R2 : rt → rt → Prop ) T :
    ⌜γ1' = γ2'⌝ ∗ ⌜γ1 = γ2⌝ ∗ ⌜∀ x1 x2, R1 x1 x2 ↔ R2 x1 x2⌝ ∗ T ⊢ subsume (Σ := Σ) (Rel2 γ1' γ1 R1) (Rel2 γ2' γ2 R2) T.
  Proof.
    iIntros "(-> & -> & %HR & $)".
    iIntros "Hrel". iDestruct "Hrel" as "(% & % & ? & ? & %HR')".
    iExists _, _. iFrame. iPureIntro. by apply HR.
  Qed.
  Global Instance subsume_gvar_rel_inst {rt} γ1' γ1 γ2' γ2 (R1 R2 : rt → rt → Prop) : Subsume (Rel2 γ1' γ1 R1) (Rel2 γ2' γ2 R2) :=
    λ T, i2p (subsume_gvar_rel γ1' γ1 γ2' γ2 R1 R2 T).

  (** FindOptGvarPobs *)
  Lemma find_in_context_opt_gvar_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T (inl (existT rt r)))
    ⊢ find_in_context (FindOptGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_opt_gvar_pobs_inst γ :
    FindInContext (FindOptGvarPobs γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_gvar_pobs γ T).

  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_gvar_pobs_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptGvarPobs γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_dummy_inst γ :
    FindInContext (FindOptGvarPobs γ) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_opt_gvar_pobs_dummy γ T).

  (** FindGvarPobs *)
  Lemma find_in_context_gvar_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T ((existT rt r)))
    ⊢ find_in_context (FindGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_inst γ :
    FindInContext (FindGvarPobs γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs γ T).

  Lemma find_in_context_gvar_pobs_p_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T (gvar_pobs γ r))
    ⊢ find_in_context (FindGvarPobsP γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists (gvar_pobs γ r) => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_p_pobs_inst γ :
    FindInContext (FindGvarPobsP γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs_p_pobs γ T).

  Lemma find_in_context_gvar_pobs_p_obs γ T :
    (∃ rt (r : rt), gvar_obs γ r ∗ T (gvar_obs γ r))
    ⊢ find_in_context (FindGvarPobsP γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists (gvar_obs γ r) => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_p_obs_inst γ :
    FindInContext (FindGvarPobsP γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs_p_obs γ T).

  Lemma subsume_gvar_pobs {rt} γ (r1 r2 : rt) T :
    ⌜r1 = r2⌝ ∗ T ⊢ subsume (Σ := Σ) (gvar_pobs γ r1) (gvar_pobs γ r2) T.
  Proof. iIntros "(-> & $) $". Qed.
  Global Instance subsume_gvar_pobs_inst {rt} γ (r1 r2 : rt) : Subsume (gvar_pobs γ r1) (gvar_pobs γ r2) :=
    λ T, i2p (subsume_gvar_pobs γ r1 r2 T).

  Lemma subsume_full_gvar_obs_pobs E L {rt} step γ (r1 r2 : rt) T :
    (⌜r1 = r2⌝ ∗ (gvar_pobs γ r2 -∗ T L (True)%I)) ⊢ subsume_full E L step (gvar_obs γ r1) (gvar_pobs γ r2) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (????) "#CTX #HE HL Hobs". iMod (gvar_obs_persist with "Hobs") as "#Hobs".
    iExists _, _. iPoseProof ("HT" with "Hobs") as "$". iFrame.
    iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance subsume_full_gvar_obs_pobs_inst E L {rt} step γ (r1 r2 : rt) : SubsumeFull E L step (gvar_obs γ r1) (gvar_pobs γ r2) :=
    λ T, i2p (subsume_full_gvar_obs_pobs E L step γ r1 r2 T).

  (** FindInherit *)
  Lemma find_in_context_inherit {K} κ (key : K) P T :
    Inherit κ key P ∗ T () ⊢
    find_in_context (FindInherit κ key P) T.
  Proof.
    iIntros "(Hinh & HT)". iExists (). by iFrame.
  Qed.
  Global Instance find_in_context_inherit_inst {K} κ (key : K) P :
    FindInContext (FindInherit κ key P) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_inherit κ key P T).

  (** FindLocInBounds *)
  Lemma find_in_context_loc_in_bounds l T :
    (∃ pre suf, loc_in_bounds l pre suf ∗ T (loc_in_bounds l pre suf))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (pre suf) "[??]". iExists (loc_in_bounds _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_inst l :
    FindInContext (FindLocInBounds l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_loc_in_bounds l T).

  Lemma find_in_context_loc_in_bounds_loc l T :
    (∃ π k rt (lt : ltype rt) r, l ◁ₗ[π, k] r @ lt ∗ T (l ◁ₗ[π, k] r @ lt))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (?????) "[??]". iExists (ltype_own _ _ _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_loc_inst l :
    FindInContext (FindLocInBounds l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_loc_in_bounds_loc l T).

  Lemma subsume_loc_in_bounds (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T :
    ⌜l1.1 = l2.1⌝ ∗ ⌜(l1.2 + pre2 ≤ l2.2 + pre1)%Z⌝ ∗ ⌜(l2.2 + suf2 ≤ l1.2 + suf1)%Z⌝ ∗ T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof.
    iIntros "(% & % & % & $)". by iApply loc_in_bounds_offset.
  Qed.
  Global Instance subsume_loc_in_bounds_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 100 :=
    λ T, i2p (subsume_loc_in_bounds l1 l2 pre1 suf1 pre2 suf2 T).

  Lemma subsume_loc_in_bounds_evar1 (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T `{!IsProtected pre2} :
    ⌜pre1 = pre2⌝ ∗ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre1 suf2) T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof. iIntros "(-> & $)". Qed.
  Global Instance subsume_loc_in_bounds_evar1_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) `{!IsProtected pre2} :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 20 :=
    λ T, i2p (subsume_loc_in_bounds_evar1 l1 l2 pre1 suf1 pre2 suf2 T).
  Lemma subsume_loc_in_bounds_evar2 (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T `{!IsProtected suf2} :
    ⌜suf1 = suf2⌝ ∗ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf1) T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof. iIntros "(-> & $)". Qed.
  Global Instance subsume_loc_in_bounds_evar2_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) `{!IsProtected suf2} :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 20 :=
    λ T, i2p (subsume_loc_in_bounds_evar2 l1 l2 pre1 suf1 pre2 suf2 T).

  (* TODO: maybe generalize this to have a TC or so so? *)
  Lemma subsume_place_loc_in_bounds π (l1 l2 : loc) {rt} (lt : ltype rt) k r (pre suf : nat) T :
    ⌜l1 = l2⌝ ∗ ⌜pre = 0%nat⌝ ∗ li_tactic (compute_layout_goal (ltype_st lt)) (λ ly,
      ⌜suf ≤ ly_size ly⌝ ∗ (l1 ◁ₗ[π, k] r @ lt -∗ T))
    ⊢ subsume (l1 ◁ₗ[π, k] r @ lt) (loc_in_bounds l2 pre suf) T.
  Proof.
    rewrite /compute_layout_goal. iIntros "(-> & -> & %ly & %Halg & %Ha & HT)".
    iIntros "Ha". iPoseProof (ltype_own_loc_in_bounds with "Ha") as "#Hb"; first done.
    iPoseProof ("HT" with "Ha") as "$".
    iApply (loc_in_bounds_shorten_suf with "Hb"). lia.
  Qed.
  Global Instance subsume_place_loc_in_bounds_inst π (l1 l2 : loc) {rt} (lt : ltype rt) k r (pre suf : nat) :
    Subsume (l1 ◁ₗ[π, k] r @ lt) (loc_in_bounds l2 pre suf) :=
    λ T, i2p (subsume_place_loc_in_bounds π l1 l2 lt  k r pre suf T).

  (** Simplify instances *)
  Lemma simplify_goal_lft_dead_list κs T :
    ([∗ list] κ ∈ κs, [† κ]) ∗ T ⊢ simplify_goal (lft_dead_list κs) T.
  Proof.
    rewrite /simplify_goal. iFrame. eauto.
  Qed.
  Global Instance simplify_goal_lft_dead_list_inst κs :
    SimplifyGoal (lft_dead_list κs) (Some 0%N) := λ T, i2p (simplify_goal_lft_dead_list κs T).

  (** ** SubsumeFull instances *)
  (** We have low-priority instances to escape into subtyping judgments *)
  (* TODO should make compatible with mem_casts? *)
  (*
  Lemma subsume_full_own_val {rt1 rt2} π E L step v (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    weak_subtype E L r1 r2 ty1 ty2 (T L True) -∗
    subsume_full E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "HT" (F ?) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & HT)".
    iDestruct "Hincl" as "(_ & _ & #Hincl & _)".
    iExists _, True%I. iFrame.
    iApply maybe_logical_step_intro. rewrite right_id.
    by iPoseProof ("Hincl" with "Hv") as "$".
  Qed.
  (* low priority, more specific instances should trigger first *)
  Global Instance subsume_full_own_val_inst {rt1 rt2} π E L step v (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) | 100 :=
    λ T, i2p (subsume_full_own_val π E L step v ty1 ty2 r1 r2 T).
  *)

  Lemma subsume_full_value_evar π E L step v {rt} (ty : type rt) (r1 r2 : rt) T :
    ⌜r1 = r2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (v ◁ᵥ{π} r1 @ ty) (v ◁ᵥ{π} r2 @ ty) T.
  Proof.
    iIntros "(-> & HT)". by iApply subsume_full_id.
  Qed.
  Global Instance subsume_full_value_evar_inst π E L step v {rt} (ty : type rt) (r1 r2 : rt) :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty) (v ◁ᵥ{π} r2 @ ty) | 5 :=
    λ T, i2p (subsume_full_value_evar π E L step v ty r1 r2 T).

  Lemma subsume_full_owned_subtype π E L step v {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    owned_subtype π E L false r1 r2 ty1 ty2 (λ L', T L' True%I)
    ⊢ subsume_full E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "HT" (????) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L' & Hincl & HL & HT)".
    iDestruct "Hincl" as "(_ & _ & Hincl)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    iExists _, _. iFrame. iApply maybe_logical_step_intro.
    by iFrame.
  Qed.
  Global Instance subsume_full_uninit_owned_subtype_inst π E L step v {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty1)%I (v ◁ᵥ{π} r2 @ ty2)%I | 100 :=
    λ T, i2p (subsume_full_owned_subtype π E L step v ty1 ty2 r1 r2 T).

  (* TODO: how does the evar thing work here? *)
  Lemma subsume_full_own_loc_bk_evar {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) b1 b2 r1 r2 T `{!ContainsProtected b2}:
    ⌜b1 = b2⌝ ∗ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T
    ⊢ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T.
  Proof. iIntros "(-> & HT)". done. Qed.
  Global Instance subsume_full_own_loc_bk_evar_inst {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 b1 b2 `{!ContainsProtected b2}:
    SubsumeFull E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) | 1000 :=
    λ T, i2p (subsume_full_own_loc_bk_evar π E L step l lt1 lt2 b1 b2 r1 r2 T).

  Lemma subsume_full_own_loc_owned_false {rt1 rt2} π E L l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T :
    owned_subltype_step π E L l r1 r2 lt1 lt2 T
    ⊢ subsume_full E L true (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) T.
  Proof.
    iIntros "HT" (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] CTX HE HL Hl") as "(%L' & %R & Hstep & %Hly & HL & HT)".
    iExists L', R. by iFrame.
  Qed.
  Global Instance subsume_full_own_loc_owned_false_inst {rt1 rt2} π E L l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 :
    SubsumeFull E L true (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) | 1001 :=
    λ T, i2p (subsume_full_own_loc_owned_false π E L l lt1 lt2 r1 r2 T).

  Lemma subsume_full_own_loc_owned_false_true {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T
    `{!TCDone (match ltype_lty _ lt2 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | OpenedNaLty _ _ _ _ => False | _ => True end)} :
    prove_with_subtype E L s ProveDirect (have_creds) (λ L2 κs R,
      subsume_full E L2 s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) (λ L3 R2, T L3 (R ∗ R2)))
    ⊢ subsume_full E L s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned true] r2 @ lt2) T.
  Proof.
    iIntros "HT" (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & %κs & %R & Hs & HL & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl") as "(%L3 & %R2 & Hstep2 & HL & HT)".
    iExists _, _. iFrame.
    iApply (maybe_logical_step_compose with "Hs").
    iApply (maybe_logical_step_compose with "Hstep2").
    iApply maybe_logical_step_intro. iModIntro.
    iIntros "(Hl & $) (Hcred & $)".
    iApply (ltype_own_Owned_false_true with "Hl Hcred"); done.
  Qed.
  Global Instance subsume_full_own_loc_owned_false_true_inst {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2
    `{!TCDone (match ltype_lty _ lt2 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | OpenedNaLty _ _ _ _ => False | _ => True end)} :
    SubsumeFull E L s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned true] r2 @ lt2) | 1001 :=
    λ T, i2p (subsume_full_own_loc_owned_false_true π E L s l lt1 lt2 r1 r2 T).

  Lemma subsume_full_own_loc_owned_true_false {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T
    `{!TCDone (match ltype_lty _ lt1 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | OpenedNaLty _ _ _ _ => False | _ => True end)} :
      introduce_with_hooks E L (£ (num_cred - 1) ∗ atime 1) (λ L2,
      subsume_full E L2 s (l ◁ₗ[π, Owned false] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) T)
    ⊢ subsume_full E L s (l ◁ₗ[π, Owned true] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) T.
  Proof.
    iIntros "HT" (????) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_Owned_true_false with "Hl") as "(((Hcred1 & Hcred) & Hat) & Hl)"; first done.
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iMod ("HT" with "[//] HE HL [$Hcred $Hat]") as "(%L2 & HL & HT)".
    by iApply ("HT" with "[//] [//] [//] CTX HE HL").
  Qed.
  Global Instance subsume_full_own_loc_owned_true_false_inst {rt1 rt2} π E L s l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2
    `{!TCDone (match ltype_lty _ lt1 with | OpenedLty _ _ _ _ _ | CoreableLty _ _ | ShadowedLty _ _ _ => False | OpenedNaLty _ _ _ _ => False | _ => True end)} :
    SubsumeFull E L s (l ◁ₗ[π, Owned true] r1 @ lt1) (l ◁ₗ[π, Owned false] r2 @ lt2) | 1001 :=
    λ T, i2p (subsume_full_own_loc_owned_true_false π E L s l lt1 lt2 r1 r2 T).

  (* TODO should make compatible with location simplification *)
  Lemma subsume_full_own_loc {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) b1 b2 r1 r2 T :
    ⌜lctx_bor_kind_direct_incl E L b2 b1⌝ ∗ weak_subltype E L b2 r1 r2 lt1 lt2 (T L True%I)
    ⊢ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T.
  Proof.
    iIntros "(%Hincl & HT)" (F ???) "#CTX #HE HL Hl".
    iPoseProof (lctx_bor_kind_direct_incl_use with "HE HL") as "#Hincl"; first done.
    iPoseProof (ltype_bor_kind_direct_incl with "Hincl Hl") as "Hl".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & HT)".
    iMod (ltype_incl_use with "Hincl' Hl") as "Hl"; first done.
    iExists _, True%I. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance subsume_full_own_loc_inst {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 b1 b2 :
    SubsumeFull E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) | 1002 :=
    λ T, i2p (subsume_full_own_loc π E L step l lt1 lt2 b1 b2 r1 r2 T).

  (** Weaker Subsume instances for compatibility *)
  Lemma subsume_own_loc {rt} π l (lt1 : ltype rt) (lt2 : ltype rt) b1 b2 r1 r2 T :
    subsume (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T :-
      exhale (⌜b1 = b2⌝);
      exhale (⌜lt1 = lt2⌝);
      exhale (⌜r1 = r2⌝);
      return T.
  Proof.
    iIntros "(-> & -> & -> & HT) Ha". iFrame.
  Qed.
  Definition subsume_own_loc_inst := [instance @subsume_own_loc].
  Global Existing Instance subsume_own_loc_inst.


  (** ** Subtyping instances: [weak_subtype] *)
  Lemma weak_subtype_id E L {rt} (ty : type rt) r T :
    T ⊢ weak_subtype E L r r ty ty T.
  Proof.
    iIntros "$" (??) "?? $". iApply type_incl_refl.
  Qed.
  Global Instance weak_subtype_refl_inst E L {rt} (ty : type rt) r :
    Subtype E L r r ty ty := λ T, i2p (weak_subtype_id E L ty r T).

  Lemma weak_subtype_evar1 E L {rt} (ty : type rt) r r2 T :
    ⌜r = r2⌝ ∗ T ⊢ weak_subtype E L r r2 ty ty T.
  Proof.
    iIntros "(<- & $)" (??) "?? $". iApply type_incl_refl.
  Qed.
  (* We want this to work even if [r2] has shape e.g. [Z.of_nat ?evar], so we do not actually require this to be an evar.
      Instead, we have a super low priority so that more specific instances will get picked first. *)
  Global Instance weak_subtype_evar1_inst E L {rt} (ty : type rt) r r2 :
    Subtype E L r r2 ty ty | 200 := λ T, i2p (weak_subtype_evar1 E L ty r r2 T).

  Lemma weak_subtype_evar2 E L {rt} (ty ty2 : type rt) r r2 T :
    ⌜ty = ty2⌝ ∗ weak_subtype E L r r2 ty ty T ⊢ weak_subtype E L r r2 ty ty2 T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subtype_evar2_inst E L {rt} (ty : type rt) r r2 `{!IsProtected ty2} :
    Subtype E L r r2 ty ty2 | 100 := λ T, i2p (weak_subtype_evar2 E L ty ty2 r r2 T).

  Lemma weak_subtype_subtype_l {rt1 rt2 rt1'} (ty1 : type rt1) (ty1' : type rt1') (ty2 : type rt2) r1 r1' r2 E L T :
    subtype E L r1 r1' ty1 ty1' →
    weak_subtype E L r1' r2 ty1' ty2 T -∗
    weak_subtype E L r1 r2 ty1 ty2 T.
  Proof.
    iIntros (Hsub) "HT". rewrite /weak_subtype.
    iIntros (??) "#CTX #HE HL".
    iPoseProof (subtype_acc with "HE HL") as "#Hincl1"; first done.
    iMod ("HT" with "[] CTX HE HL") as "(#Hincl2 & $ & $)"; first done.
    iModIntro. iApply type_incl_trans; done.
  Qed.
  Lemma weak_subtype_subtype_r {rt1 rt2 rt2'} (ty1 : type rt1) (ty2' : type rt2') (ty2 : type rt2) r1 r2' r2 E L T :
    subtype E L r2' r2 ty2' ty2 →
    weak_subtype E L r1 r2' ty1 ty2' T -∗
    weak_subtype E L r1 r2 ty1 ty2 T.
  Proof.
    iIntros (Hsub) "HT". rewrite /weak_subtype.
    iIntros (??) "#CTX #HE HL".
    iPoseProof (subtype_acc with "HE HL") as "#Hincl1"; first done.
    iMod ("HT" with "[] CTX HE HL") as "(#Hincl2 & $ & $)"; first done.
    iModIntro. iApply type_incl_trans; done.
  Qed.

  (** ** Subtyping instances: [mut_subtype] *)
  Lemma mut_subtype_id E L {rt} (ty : type rt) T :
    T ⊢ mut_subtype E L ty ty T.
  Proof.
    iIntros "$". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_subtype_refl_inst E L {rt} (ty : type rt) :
    MutSubtype E L ty ty | 1 := λ T, i2p (mut_subtype_id E L ty T).

  Lemma mut_subtype_evar E L {rt} (ty ty2 : type rt) T :
    ⌜ty = ty2⌝ ∗ T ⊢ mut_subtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Global Instance mut_subtype_evar_inst E L {rt} (ty : type rt) `{!IsProtected ty2} :
    MutSubtype E L ty ty2 | 100 := λ T, i2p (mut_subtype_evar E L ty ty2 T).

  (** ** Subtyping instances: [mut_eqtype] *)
  Lemma mut_eqtype_id E L {rt} (ty : type rt) T :
    T ⊢ mut_eqtype E L ty ty T.
  Proof.
    iIntros "$". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_eqtype_refl_inst E L {rt} (ty : type rt) :
    MutEqtype E L ty ty | 99 := λ T, i2p (mut_eqtype_id E L ty T).

  Lemma mut_eqtype_evar E L {rt} (ty ty2 : type rt) T :
    ⌜ty = ty2⌝ ∗ T ⊢ mut_eqtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Global Instance mut_eqtype_evar_inst E L {rt} (ty : type rt) `{!IsProtected ty2} :
    MutEqtype E L ty ty2 | 100 := λ T, i2p (mut_eqtype_evar E L ty ty2 T).


  (** ** Subtyping instances: [weak_subltype] *)
  (* Instances for [weak_subltype] include:
      - identity
      - folding/unfolding
      - structural lifting
      - lifetime subtyping; below Uniq, we can only replace by equivalences. Thus, we need to prove subtyping in both directions. We may want to have a dedicated judgment for that.
     We, however, cannot trigger [resolve_ghost], as it needs to open stuff up and thus needs steps.

     The instances, especially for folding/unfolding, should use the structure of the second lt (the target) as guidance for incrementally manipulating the first one.
     After making the heads match, structurally descend.
   *)

  Lemma weak_subltype_id E L {rt} (lt : ltype rt) k r T :
    T ⊢ weak_subltype E L k r r lt lt T.
  Proof. iIntros "$" (??) "_ _ $". iApply ltype_incl_refl. Qed.
  Global Instance weak_subltype_refl_inst E L {rt} (lt : ltype rt) k r : SubLtype E L k r r lt lt | 1 :=
    λ T, i2p (weak_subltype_id E L lt k r T).

  Lemma weak_subltype_evar1 E L {rt} (lt1 : ltype rt) k r1 r2 T :
    ⌜r1 = r2⌝ ∗ T ⊢ weak_subltype E L k r1 r2 lt1 lt1 T.
  Proof.
    iIntros "(<- & HT)" (??) "#CTX #HE HL". iFrame. iApply ltype_incl_refl.
  Qed.
  (*Global Instance weak_subltype_evar1_inst E L {rt} (lt1 : ltype rt) k r1 r2  :*)
    (*SubLtype E L k r1 r2 (lt1)%I (lt1)%I | 1 :=*)
    (*λ T, i2p (weak_subltype_evar1 E L lt1 k r1 r2 T).*)
  Global Instance weak_subltype_evar1_inst E L {rt} (lt1 : ltype rt) k r1 r2 :
    SubLtype E L k r1 r2 (lt1)%I (lt1)%I | 1000 :=
    λ T, i2p (weak_subltype_evar1 E L lt1 k r1 r2 T).

  Lemma weak_subltype_evar2 E L {rt} (lt1 lt2 : ltype rt) k r1 r2 T :
    ⌜lt1 = lt2⌝ ∗ weak_subltype E L k r1 r2 lt1 lt1 T ⊢ weak_subltype E L k r1 r2 lt1 lt2 T.
  Proof. iIntros "(<- & $)". Qed.
  Global Instance weak_subltype_evar2_inst E L {rt} (lt1 lt2 : ltype rt) k r1 r2 `{!IsProtected lt2} :
    SubLtype E L k r1 r2 (lt1)%I (lt2)%I | 100 :=
    λ T, i2p (weak_subltype_evar2 E L lt1 lt2 k r1 r2 T).

  (* Escape into the stronger subtyping judgment. Note: should not be used when lt2 is an evar. *)
  Lemma weak_subltype_base E L {rt} (lt1 lt2 : ltype rt) k r1 r2 T :
    ⌜r1 = r2⌝ ∗ mut_eqltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 lt1 lt2 T.
  Proof.
    iIntros "(<- & %Hsub & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hsub"; first done.
    iFrame. iPoseProof ("Hsub" $! _ _) as "(Ha1 & _)". done.
  Qed.
  Global Instance weak_subltype_base_inst E L {rt} (lt1 lt2 : ltype rt) k r1 r2 :
    SubLtype E L k r1 r2 (lt1)%I (lt2)%I | 200 :=
    λ T, i2p (weak_subltype_base E L lt1 lt2 k r1 r2 T).

  Lemma weak_subltype_ofty_ofty_owned_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) wl r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subtype E L r1 r2' ty1 ty2 T)
    ⊢ weak_subltype E L (Owned wl) (#r1) r2 (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply type_ltype_incl_owned_in.
  Qed.
  Global Instance weak_subltype_ofty_ofty_owned_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) wl r1 r2 : SubLtype E L (Owned wl) #r1 r2 (◁ ty1)%I (◁ ty2)%I | 10 :=
    λ T, i2p (weak_subltype_ofty_ofty_owned_in E L ty1 ty2 wl r1 r2 T).

  Lemma weak_subltype_ofty_ofty_shared_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subtype E L r1 r2' ty1 ty2 T)
    ⊢ weak_subltype E L (Shared κ) (#r1) (r2) (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply type_ltype_incl_shared_in.
  Qed.
  Global Instance weak_subltype_ofty_ofty_shared_in_inst E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ r1 r2 : SubLtype E L (Shared κ) #r1 r2 (◁ ty1)%I (◁ ty2)%I | 10 :=
    λ T, i2p (weak_subltype_ofty_ofty_shared_in E L ty1 ty2 κ r1 r2 T).

  (* Note: no similar rule for Uniq -- we can just get strong subtyping through the base lemmas *)

  (** ** Subtyping instances: [mut_eqltype] *)
  Lemma mut_eqltype_id E L {rt} (lt : ltype rt) T :
    T ⊢ mut_eqltype E L lt lt T.
  Proof. iIntros "$". iPureIntro. reflexivity. Qed.
  Global Instance mut_eqltype_refl_inst E L {rt} (lt : ltype rt) : MutEqLtype E L lt lt | 1 :=
    λ T, i2p (mut_eqltype_id E L lt T).

  Lemma mut_eqltype_base_evar E L {rt} (lt1 lt2 : ltype rt) T :
    ⌜lt1 = lt2⌝ ∗ T
    ⊢ mut_eqltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_eqltype_base_evar_inst E L {rt} (lt1 lt2 : ltype rt) `{!IsProtected lt2} :
    MutEqLtype E L (lt1)%I (lt2)%I | 100 := λ T, i2p (mut_eqltype_base_evar E L lt1 lt2 T).

  Lemma mut_eqltype_ofty E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) T :
    mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqltype E L (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%Heqt & $)".
    iPureIntro. eapply full_eqtype_eqltype; done.
  Qed.
  Global Instance mut_eqltype_ofty_inst E L {rt} `{!Inhabited rt} (ty1 ty2 : type rt) :
    MutEqLtype E L (◁ ty1)%I (◁ ty2)%I | 5 := λ T, i2p (mut_eqltype_ofty E L ty1 ty2 T).

  (** ** Subtyping instances: [mut_subltype] *)
  Lemma mut_subltype_id E L {rt} (lt : ltype rt) T :
    T ⊢ mut_subltype E L lt lt T.
  Proof. iIntros "$". iPureIntro. reflexivity. Qed.
  Global Instance mut_subltype_refl_inst E L {rt} (lt : ltype rt) : MutSubLtype E L lt lt | 1 :=
    λ T, i2p (mut_subltype_id E L lt T).

  Lemma mut_subltype_base_evar E L {rt} (lt1 lt2 : ltype rt) T :
    ⌜lt1 = lt2⌝ ∗ T
    ⊢ mut_subltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Global Instance mut_subltype_base_evar_inst E L {rt} (lt1 lt2 : ltype rt) `{!IsProtected lt2} :
    MutSubLtype E L (lt1)%I (lt2)%I | 100 := λ T, i2p (mut_subltype_base_evar E L lt1 lt2 T).

  (** ** Subtyping instances: [owned_subltype_step] *)

  (** ** casts *)
  Lemma cast_ltype_to_type_id E L {rt} (ty : type rt) T :
    T ty ⊢ cast_ltype_to_type E L (◁ ty) T.
  Proof.
    iIntros "HT". iExists ty. iFrame "HT". done.
  Qed.
  Global Instance cast_ltype_to_type_id_inst E L {rt} (ty : type rt) :
    CastLtypeToType E L (◁ ty)%I :=
    λ T, i2p (cast_ltype_to_type_id E L ty T).

  (** ** prove_place_cond *)
  Lemma prove_place_cond_ofty_refl E L bmin {rt} (ty : type rt) T :
    T (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl) ⊢
    prove_place_cond E L bmin (◁ ty) (◁ ty) T.
  Proof.
    iIntros "HT" (F ?) "#CTX HE $". iExists _. iFrame.
    iSplitR. { iApply upd_bot_min. }
    iSplitR. { iApply typed_place_cond_refl_ofty. }
    done.
  Qed.
  (* high-priority instance for reflexivity *)
  Definition prove_place_cond_ofty_refl_inst := [instance @prove_place_cond_ofty_refl].
  Global Existing Instance prove_place_cond_ofty_refl_inst | 2.

  (* Low priority instances for strong and weak updates *)
  Lemma prove_place_cond_strong_trivial E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) T :
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ T (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)
    ⊢ prove_place_cond E L UpdStrong lt1 lt2 T.
  Proof.
    iIntros "(% & HT)". unfold prove_place_cond.
    iIntros (??) "#CTX #HE HL".
    iFrame. done.
  Qed.
  Definition prove_place_cond_strong_trivial_inst := [instance @prove_place_cond_strong_trivial].
  Global Existing Instance prove_place_cond_strong_trivial_inst | 1000.
  Lemma prove_place_cond_weak_trivial E L {rt} (lt1 lt2 : ltype rt)  T :
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ T (mkPUKRes (allowed:=UpdWeak) UpdWeak eq_refl eq_refl)
    ⊢ prove_place_cond E L UpdWeak lt1 lt2 T.
  Proof.
    iIntros "(% & HT)". unfold prove_place_cond.
    iIntros (??) "#CTX #HE HL".
    iFrame. done.
  Qed.
  Definition prove_place_cond_weak_trivial_inst := [instance @prove_place_cond_weak_trivial].
  Global Existing Instance prove_place_cond_weak_trivial_inst | 1000.

  (** Lemmas to eliminate BlockedLtype on either side *)
  Lemma prove_place_cond_blocked_r_Uniq E L {rt rt2} (ty : type rt) (lt : ltype rt2) κs κ' T :
    ⌜lctx_place_update_kind_outlives E L (UpdUniq κs) [κ']⌝ ∗ prove_place_cond E L (UpdUniq κs) lt (◁ ty) (λ upd,
      (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdUniq κs) upd.(puk_res_eq_2) upd.(puk_res_eq_2)))
    ⊢ prove_place_cond E L (UpdUniq κs) lt (BlockedLtype ty κ') T.
  Proof.
    iIntros "(%Hincl & HT)".
    iIntros (F ?) "#CTX HE HL".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Hincl"; first done.
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl' & Hcond & %Hst & HT)".
    iExists _. iFrame. simpl.
    iSplitR. { iApply lft_list_incl_refl. }
    rewrite Hst. simp_ltypes. iL.
    destruct upd as [upd ? Heq2]; try done. simpl.
    unfold opt_place_update_eq in Heq2.
    simpl in *. subst rt2.
    iPoseProof (typed_place_cond_incl with "Hincl' Hcond") as "Hcond".
    by iApply typed_place_cond_blocked_r_Uniq.
  Qed.
  Definition prove_place_cond_blocked_r_Uniq_inst := [instance @prove_place_cond_blocked_r_Uniq].
  Global Existing Instance prove_place_cond_blocked_r_Uniq_inst | 5.

  Lemma prove_place_cond_blocked_r_Strong E L {rt rt2} (lt : ltype rt2) (ty : type rt) κ' T :
    prove_place_cond E L UpdStrong lt (◁ ty) (λ upd,
     (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdStrong) I upd.(puk_res_eq_2))) ⊢
    prove_place_cond E L UpdStrong lt (BlockedLtype ty κ') T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl & Hcond & %Ht & HT)".
    iExists _. iFrame. done.
  Qed.
  Definition prove_place_cond_blocked_r_Strong_inst := [instance @prove_place_cond_blocked_r_Strong].
  Global Existing Instance prove_place_cond_blocked_r_Strong_inst | 5.
  (* no shared lemma *)

  Lemma prove_place_cond_blocked_l E L {rt rt2} (ty : type rt) (lt : ltype rt2) b κ'  T :
    prove_place_cond E L b (◁ ty)%I lt T ⊢
    prove_place_cond E L b (BlockedLtype ty κ') lt T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & #Hincl & Hcond & %Hst & T))".
    iExists _. iModIntro. iFrame "∗ #".
    iL. by iApply typed_place_cond_blocked_l.
  Qed.
  Definition prove_place_cond_blocked_l_inst := [instance @prove_place_cond_blocked_l].
  Global Existing Instance prove_place_cond_blocked_l_inst | 5.

  (** Lemmas to eliminate ShrBlockedLtype on either side *)
  Lemma prove_place_cond_shrblocked_r_Uniq E L {rt rt2} (ty : type rt) (lt : ltype rt2) κs κ' T :
    ⌜lctx_place_update_kind_outlives E L (UpdUniq κs) [κ']⌝ ∗ prove_place_cond E L (UpdUniq κs) lt (◁ ty) (λ upd,
      (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdUniq κs) upd.(puk_res_eq_2) upd.(puk_res_eq_2)))
    ⊢ prove_place_cond E L (UpdUniq κs) lt (ShrBlockedLtype ty κ') T.
  Proof.
    iIntros "(%Hincl & HT)".
    iIntros (F ?) "#CTX HE HL".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Hincl"; first done.
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl' & Hcond & %Hst & HT)".
    iExists _. iFrame. simpl.
    iSplitR. { iApply lft_list_incl_refl. }
    rewrite Hst. simp_ltypes. iL.
    destruct upd as [upd ? Heq2]; try done. simpl.
    unfold opt_place_update_eq in Heq2.
    simpl in *. subst rt2.
    iPoseProof (typed_place_cond_incl with "Hincl' Hcond") as "Hcond".
    by iApply typed_place_cond_shrblocked_r_Uniq.
  Qed.
  Definition prove_place_cond_shrblocked_r_Uniq_inst := [instance @prove_place_cond_shrblocked_r_Uniq].
  Global Existing Instance prove_place_cond_shrblocked_r_Uniq_inst | 5.

  Lemma prove_place_cond_shrblocked_r_Strong E L {rt rt2} (lt : ltype rt2) (ty : type rt) κ' T :
    prove_place_cond E L UpdStrong lt (◁ ty) (λ upd,
     (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdStrong) I upd.(puk_res_eq_2))) ⊢
    prove_place_cond E L UpdStrong lt (ShrBlockedLtype ty κ') T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl & Hcond & %Ht & HT)".
    iExists _. iFrame. done.
  Qed.
  Definition prove_place_cond_shrblocked_r_Strong_inst := [instance @prove_place_cond_shrblocked_r_Strong].
  Global Existing Instance prove_place_cond_shrblocked_r_Strong_inst | 5.
  (* no shared lemma *)

  Lemma prove_place_cond_shrblocked_l E L {rt rt2} (ty : type rt) (lt : ltype rt2) b κ'  T :
    prove_place_cond E L b (◁ ty)%I lt T ⊢
    prove_place_cond E L b (ShrBlockedLtype ty κ') lt T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & #Hincl & Hcond & %Hst & T))".
    iExists _. iModIntro. iFrame "∗ #".
    iL. by iApply typed_place_cond_shrblocked_l.
  Qed.
  Definition prove_place_cond_shrblocked_l_inst := [instance @prove_place_cond_shrblocked_l].
  Global Existing Instance prove_place_cond_shrblocked_l_inst | 5.

  (** Lemmas to eliminate Coreable on either side *)
  Lemma prove_place_cond_coreable_r_Strong E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs T :
    prove_place_cond E L UpdStrong lt1 lt2 (λ upd,
      (T (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))) ⊢
    prove_place_cond E L UpdStrong lt1 (CoreableLtype κs lt2) T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & ? & Hcond & % & HT)".
    iExists _. iFrame. done.
  Qed.
  Definition prove_place_cond_coreable_r_Strong_inst := [instance @prove_place_cond_coreable_r_Strong].
  Global Existing Instance prove_place_cond_coreable_r_Strong_inst | 5.

  (* κ needs to outlive all the κ' ∈ κs *)
  Lemma prove_place_cond_coreable_r_Uniq E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs κ T :
    ⌜lctx_place_update_kind_outlives E L (UpdUniq κ) κs⌝ ∗
      prove_place_cond E L (UpdUniq κ) lt1 lt2 (λ upd,
      (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdUniq κ) upd.(puk_res_eq_2) upd.(puk_res_eq_2)))
    ⊢ prove_place_cond E L (UpdUniq κ) lt1 (CoreableLtype κs lt2) T.
  Proof.
    iIntros "(%Hal & HT)". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & % & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Hal".
    { apply Hal. }
    iFrame "HL". iExists _. iFrame. simpl.
    iSplitR. { iApply lft_list_incl_refl. }
    destruct upd as [upd Heq1 Heq2]; try done. simpl in *.
    unfold opt_place_update_eq in Heq2. simpl in *. subst rt2.
    destruct upd; try done. iL.
    iPoseProof (typed_place_cond_incl with "Hincl Hcond") as "Hcond".
    by iApply typed_place_cond_coreable_r_Uniq.
  Qed.
  Definition prove_place_cond_coreable_r_Uniq_inst := [instance @prove_place_cond_coreable_r_Uniq].
  Global Existing Instance prove_place_cond_coreable_r_Uniq_inst | 5.

  Lemma prove_place_cond_coreable_l E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs b T :
    prove_place_cond E L b lt1 lt2 T
    ⊢ prove_place_cond E L b (CoreableLtype κs lt1) lt2 T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hincl & Hcond & % & HT)".
    iFrame. iL.
    by iApply typed_place_cond_coreable_l.
  Qed.
  Definition prove_place_cond_coreable_l_inst := [instance @prove_place_cond_coreable_l].
  Global Existing Instance prove_place_cond_coreable_l_inst | 5.

  (* NOTE: unfolding lemmas should have lower priority than the primitive ones. *)

  (** find obs *)
  Import EqNotations.
  Lemma find_observation_direct (rt : RT) γ (T : find_observation_cont_t rt) :
    find_in_context (FindOptGvarPobs γ) (λ res,
      match res with
      | inr _ => find_observation rt γ FindObsModeRel T
      | inl (existT rt' r) => ∃ (Heq : rt' = rt), T (Some (rew Heq in r))
      end)%I
    ⊢ find_observation rt γ FindObsModeDirect T.
  Proof.
    iDestruct 1 as ([[rt' r] | ]) "(Hobs & HT)"; simpl.
    - iDestruct "HT" as (->) "HT". iIntros (??). iModIntro.
      iLeft. eauto with iFrame.
    - iIntros (??). by iApply "HT".
  Qed.
  Global Instance find_observation_direct_inst (rt : RT) γ :
    FindObservation rt γ FindObsModeDirect := λ T, i2p (find_observation_direct rt γ T).

  Lemma find_observation_rel (rt : RT) γ (T : find_observation_cont_t rt) :
    find_in_context (FindOptGvarRel γ) (λ res,
      match res with
      | inr _ => T None
      | inl (existT rt' (γ', R)) => ∃ (Heq : rt' = rt),
          find_observation rt' γ' FindObsModeDirect (λ or,
            match or with
            | None => False
            | Some r => ∀ r', ⌜R r r'⌝ -∗ T (Some $ rew Heq in r')
            end)
      end)%I
    ⊢ find_observation rt γ FindObsModeRel T.
  Proof.
    iDestruct 1 as ([[rt' [γ' R]] | ]) "(Hobs & HT)"; simpl.
    - iDestruct "HT" as (->) "HT".
      iIntros (??). iMod ("HT" with "[//]") as "HT".
      iDestruct "HT" as "[(%r & Hobs' & HT) | []]".
      iPoseProof (Rel2_use_pobs with "Hobs' Hobs") as "(%r2 & Hobs & %HR)".
      iSpecialize ("HT" with "[//]").
      iMod (gvar_obs_persist with "Hobs") as "Hobs".
      iModIntro. iLeft. eauto with iFrame.
    - iIntros (??). iRight. done.
  Qed.
  Global Instance find_observation_rel_inst (rt : RT) γ :
    FindObservation rt γ FindObsModeRel := λ T, i2p (find_observation_rel rt γ T).

  (** ** resolve_ghost *)
  (* One note: these instances do not descend recursively -- that is the task of the stratify_ltype call that is triggering the resolution. resolve_ghost instances should always resolve at top-level, or at the level of atoms of stratify_ltype's traversal (in case of user-defined types) *)
  Import EqNotations.

  (* a trivial low-priority instance, in case no other instance triggers.
    In particular, we should also make sure that custom instances for user-defined types get priority. *)
  Lemma resolve_ghost_id {rt} π E L l (lt : ltype rt) rm lb k r (T : llctx → place_rfn rt → iProp Σ → bool → iProp Σ) :
    match rm with
    | ResolveAll =>
        match r with
        | PlaceIn _ => T L r True true
        | _ => False
        end
    | ResolveTry =>
        T L r True (match r with PlaceIn _ => true | PlaceGhost _ => false end)
    end
    ⊢ resolve_ghost π E L rm lb l lt k r T.
  Proof.
    iIntros "HT" (F ??) "#CTX #HE HL Hl".
    destruct rm.
    - destruct r; last done.
      iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. by iFrame.
    - destruct r.
      + iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
      + iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_id_inst {rt} π E L l (lt : ltype rt) rm lb k r :
    ResolveGhost π E L rm lb l lt k r | 200 := λ T, i2p (resolve_ghost_id π E L l lt rm lb k r T).

  Lemma resolve_ghost_ofty_Owned {rt} π E L l (ty : type rt) γ rm lb wl T :
    find_observation rt γ FindObsModeDirect (λ or,
      match or with
      | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
      | Some r => T L (PlaceIn $ r) True true
      end)
    ⊢ resolve_ghost π E L rm lb l (◁ ty)%I (Owned wl) (PlaceGhost γ) T.
  Proof.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hl".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & ? & %r' & Hrfn & Hb)".
      iPoseProof (gvar_pobs_agree_2 with "Hrfn Hobs") as "->".
      iModIntro. iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. simpl. iSplitL; last done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own. eauto with iFrame.
    - iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance resolve_ghost_ofty_owned_inst {rt} π E L l (ty : type rt) γ wl rm lb :
    ResolveGhost π E L rm lb l (◁ ty)%I (Owned wl) (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_ofty_Owned π E L l ty γ rm lb wl T).

  Lemma resolve_ghost_ofty_Uniq {rt} π E L l (ty : type rt) γ rm lb κ γ' T :
    find_observation rt γ FindObsModeDirect (λ or,
      match or with
      | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
      | Some r => T L (PlaceIn $ r) True true
      end)
    ⊢ resolve_ghost π E L rm lb l (◁ ty)%I (Uniq κ γ') (PlaceGhost γ) T.
  Proof.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hl".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & ? & ? & ? & ? & ? & Hrfn & Hb)".
      iDestruct "Hrfn" as "(%v1 & %v2 & Hauth & Hobs' & %HR)".
      iPoseProof (gvar_pobs_agree_2 with "Hauth Hobs") as "->".
      simpl. subst.
      iModIntro. iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. iSplitL; last done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own. eauto with iFrame.
    - iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance resolve_ghost_ofty_uniq_inst {rt} π E L l (ty : type rt) γ κ γ' rm lb :
    ResolveGhost π E L rm lb l (◁ ty)%I (Uniq κ γ') (PlaceGhost γ) | 7 := λ T, i2p (resolve_ghost_ofty_Uniq π E L l ty γ rm lb κ γ' T).



  (** ** ltype stratification *)
  (* TODO change the ResolveTry and also make it a parameter of stratify *)

  (* when we recursively want to descend, we cannot let the resolution use the logical step *)
  Lemma stratify_ltype_resolve_ghost_rec {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) b r T :
    resolve_ghost π E L ResolveTry false l lt b r (λ L1 r R progress,
      if progress then
      stratify_ltype π E L1 mu mdu ma ml l lt r b
        (λ L2 R' rt' lt' r', T L2 (R ∗ R') rt' lt' r')
      else
        (* otherwise treat this as a leaf *)
        R -∗ stratify_ltype_post_hook π E L1 ml l lt r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "Hres". iIntros (????) "#CTX #HE HL Hl".
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & >(Hl & HR) & HL & HP)"; [done.. | ].
    destruct prog.
    - iPoseProof ("HP" with "[//] [//] [//] CTX HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & Hcond & Hb & HT)".
      iModIntro. iExists L2, _, rt', lt', r'. iFrame "Hcond HT HL".
      iApply (logical_step_wand with "Hb"). iIntros "($ & $)". done.
    - by iApply (stratify_ltype_id _ _ _ mu mdu ma with "(HP HR) [//] [//] [//] CTX HE HL").
  Qed.
  (* at a leaf, we can use the logical step to do the resolution -- this allows to descend deeper into the type, which is useful for custom user-defined types *)
  Lemma stratify_ltype_resolve_ghost_leaf {rt} π E L mu mdu ma {M} (ml : M) rm l (lt : ltype rt) b r T :
    resolve_ghost π E L rm true l lt b r (λ L1 r R progress, T L1 R _ lt r)
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "Hres". iIntros (????) "#CTX #HE HL Hl".
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & Hl & HL & HR)"; [done.. | ].
    simpl. iModIntro. iExists L1, _, _, lt, r1.
    iFrame. done.
  Qed.

  (* This should have a lower priority than the leaf instances we call for individual [ml] -- those should instead use [stratify_ltype_resolve_ghost_leaf]. *)
  Global Instance stratify_ltype_resolve_ghost_inst {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) b γ :
    StratifyLtype π E L mu mdu ma ml l lt (PlaceGhost γ) b | 100 := λ T, i2p (stratify_ltype_resolve_ghost_rec π E L mu mdu ma ml l lt b (PlaceGhost γ) T).

  Lemma stratify_ltype_blocked {rt} π E L mu mdu ma {M} (ml : M) l (ty : type rt) κ r b T :
    find_in_context (FindOptLftDead κ) (λ found,
      if found then stratify_ltype π E L mu mdu ma ml l (◁ ty)%I r b T
      else stratify_ltype_post_hook π E L ml l (BlockedLtype ty κ) r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l (BlockedLtype ty κ) r b T.
  Proof.
    rewrite /FindOptLftDead.
    iIntros "(%found & Hdead & Hp)". destruct found.
    - iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hl".
      iMod (unblock_blocked with "Hdead Hl") as "Hl"; first done.
      iPoseProof ("Hp" with "[//] [//] [//] [$LFT $TIME $LLCTX] HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L' & %R & %rt' & %lt' & %r' & Hl & Hstep & HT)".
      iModIntro. iExists L', R, rt', lt', r'. by iFrame.
    - by iApply stratify_ltype_id.
  Qed.
  (* No instance here, as we may not always want to do that. *)

  (* TODO: also make this one optional *)
  Lemma stratify_ltype_coreable {rt} π E L mu mdu ma {M} (ml : M) l (lt_full lt_full' : ltype rt) κs r b `{Hsimp: !SimpLtype (ltype_core lt_full) lt_full'} T :
    lft_dead_list κs ∗ stratify_ltype π E L mu mdu ma ml l lt_full' r b T
    ⊢ stratify_ltype π E L mu mdu ma ml l (CoreableLtype κs lt_full) r b T.
  Proof.
    destruct Hsimp as [<-].
    iIntros "(#Hdead & Hstrat)".
    iIntros (F ???) "#CTX #HE HL Hl".
    iMod (unblock_coreable with "Hdead Hl") as "Hl"; first done.
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "Ha".
    iDestruct "Ha" as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
    iModIntro. iExists _, _, _, _, _. iFrame.
    iPureIntro. rewrite -Hst ltype_core_syn_type_eq. by simp_ltypes.
  Qed.
  (* No instance here, as we may not always want to do that. *)

  Lemma stratify_ltype_shrblocked {rt} π E L mu mdu ma {M} (ml : M) l (ty : type rt) κ r b T :
    find_in_context (FindOptLftDead κ) (λ found,
      if found then stratify_ltype π E L mu mdu ma ml l (◁ ty)%I r b T
      else stratify_ltype_post_hook π E L ml l (ShrBlockedLtype ty κ) r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShrBlockedLtype ty κ) r b T.
  Proof.
    rewrite /FindOptLftDead.
    iIntros "(%found & Hdead & Hstrat)". destruct found.
    - iIntros (F ???) "#CTX #HE HL Hl".
      iMod (unblock_shrblocked with "Hdead Hl") as "Hl"; first done.
      iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "Ha".
      iDestruct "Ha" as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
      iModIntro. iExists _, _, _, _, _. iFrame.
      iPureIntro. done.
    - by iApply stratify_ltype_id.
  Qed.
  (* No instance here, as we may not always want to do that. *)

  (* NOTE: we make the assumption that, even for fully-owned places, we want to keep the invariant structure, and not just unfold it completely and forget about the invariants. This is why we keep it open when the refinement type is different, even though we could in principle also close it to any lt_cur'.

    Is there a better criterion for this than the refinement type?
    - currently, prove_place_cond requires the refinement type to be the same, even for Owned.
    - for some of the subtyping we may want to allow the subtyping to actually be heterogeneous.

    Points in the design space:
    - [aggressive] just fold every time we can, by always proving a subtyping.
    - [aggressive unless Owned] fold every time as long as the place cond is provable.
        + in particular: fold if we can get back a lifetime token.
    - [relaxed]
    -

    Some thoughts on stuff that would be good:
    - make stratification more syntax-guided, i.e. have a "goal" ltype?
      + this would make the behavior when we moved stuff out beforehand much more predictable, eg. for value_t: don't just have a general rule for stratifying value every time, but only when we actually want to have something there.


  *)
  Lemma stratify_ltype_opened_Owned {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r wl (T : stratify_ltype_cont_t) :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned false) (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost) r'
        else
          trigger_tc (SimpLtype (ltype_core lt_cur')) (λ lt_cur'',
          (* fold the invariant *)
          ∃ ri,
            (* show that the core of lt_cur' is a subtype of lt_inner and then fold to lt_full *)
            weak_subltype E L' (Owned false) (r') (#ri) (lt_cur'') lt_inner (
              (* re-establish the invariant *)
              ∃ rf, prove_with_subtype E L' true ProveWithStratify (Cpre ri rf) (λ L'' κs R2,
              (* either fold to coreable, or to the core of lt_full *)
              match ltype_blocked_lfts lt_cur', κs with
              | [], [] =>
                    trigger_tc (SimpLtype (ltype_core lt_full)) (λ lt_full',
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full lt_full' (#rf)))
              | κs', _ =>
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs' ++ κs) lt_full) (#rf))
              end))))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Owned wl) T.
  Proof.
    iIntros "Hstrat". iIntros (F ???) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst1 & %Hst2 & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst & Hstep & HT)".
    destruct (decide (ma = StratNoRefold)) as [-> | ].
    - (* don't fold *)
      iModIntro.
      iExists _, _, _, _, _. iFrame.
      iSplitR. { iPureIntro. simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. iFrame.
      rewrite -Hst.
      iSplitR. { done. }
      iSplitR; first done. iSplitR; first done.
      iSplitR; first done. done.
    - (* fold it again *)
      iDestruct "HT" as "(%lt_cur'' & %Heq & HT)". destruct Heq as [<-].
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & %rf & HT)".
      iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".
      iPoseProof (imp_unblockable_blocked_dead lt_cur') as "(_ & #Hb)".
      set (κs' := ltype_blocked_lfts lt_cur').
      destruct (decide (κs = [] ∧ κs' = [])) as [[-> ->] | ].
      + iDestruct "HT" as "(% & %Heq & HT)". destruct Heq as [<-].
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. rewrite ltype_core_syn_type_eq. rewrite -Hst2 -Hst1 //. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        iPoseProof ("Hb" with "[] Hl") as "Hl". { by iApply big_sepL_nil. }
        iMod (fupd_mask_mono with "Hl") as "Hl"; first done.
        rewrite ltype_own_core_equiv.
        iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
        simpl.
        iPoseProof ("Hcl" with "Hpre") as "(Hpost & Hvs')".
        iMod (fupd_mask_mono with "(Hvs' [] Hl)") as "Ha"; first done.
        { by iApply lft_dead_list_nil. }
        rewrite ltype_own_core_equiv. by iFrame.
      + iAssert (T L3 (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs' ++ κs) lt_full) #rf)%I with "[HT]" as "HT".
        { destruct κs, κs'; naive_solver. }
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro.
          simp_ltypes. rewrite -Hst2 -Hst1. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iPoseProof ("Hcl" with "Hpre") as "($ & Hvs')".
        iModIntro.
        iExists ly.
        iSplitR. { rewrite -Hst2 -Hst1. done. }
        iSplitR; first done. iSplitR; first done.
        iIntros "Hdead".
        rewrite lft_dead_list_app. iDestruct "Hdead" as "(Hdead' & Hdead)".
        (* unblock lt_cur' *)
        iPoseProof (imp_unblockable_blocked_dead lt_cur') as "(_ & #Hub)".
        iMod ("Hub" with "Hdead' Hl") as "Hl".
        (* shift to lt_inner *)
        rewrite !ltype_own_core_equiv.
        iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
        (* shift to the core of lt_full *)
        iMod ("Hvs'" with "Hdead Hl") as "Hl".
        eauto.
  Qed.
  Global Instance stratify_ltype_opened_owned_inst {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r wl:
    StratifyLtype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Owned wl) := λ T, i2p (stratify_ltype_opened_Owned π E L mu mdu ma ml l lt_cur lt_inner lt_full Cpre Cpost r wl T).

  (* NOTE what happens with the inclusion sidecondition for the κs when we shorten the outer reference?
     - we should not shorten after unfolding (that also likely doesn't work with OpenedLtype -- we cannot arbitrarily modify the lt_inner/lt_full)
     - if we are borrowing at a lifetime which doesn't satisfy this at the borrow time, that is a bug, as we are violating the contract of the outer reference.
     So: this sidecondition does not restrict us in any way. *)
  Lemma stratify_ltype_opened_Uniq {rt_cur rt_inner rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r κ γ T :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned false) (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost) r'
        else
          (* fold the invariant *)
          ∃ ri,
            (* show that lt_cur' is a subtype of lt_inner and then fold to lt_full *)
            weak_subltype E L' (Owned false) (r') (#ri) (lt_cur') lt_inner (
              (* re-establish the invariant *)
              ∃ rf,
              prove_with_subtype E L' true ProveWithStratify (Cpre ri rf) (λ L'' κs R2,
              (* either fold to coreable, or to the core of lt_full *)
              match κs, ltype_blocked_lfts lt_cur' with
              | [], [] =>
                    trigger_tc (SimpLtype (ltype_core lt_full)) (λ lt_full',
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full lt_full' (#rf)))
              | _, κs' =>
                    (* inclusion sidecondition: require that all the blocked stuff ends before κ *)
                    ([∗ list] κ' ∈ κs ++ κs', ⌜lctx_lft_incl E L'' κ' κ⌝) ∗
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs ++ κs') lt_full) (#rf))
              end)))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Uniq κ γ) T.
  Proof.
    iIntros "Hstrat". iIntros (F ???) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst1 & %Hst2 & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst & Hstep & HT)".
    destruct (decide (ma = StratNoRefold)).
    - (* don't fold *)
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR. { iPureIntro. simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. iFrame.
      rewrite -Hst.
      iSplitR. { done. }
      iSplitR; first done. iSplitR; first done.
      iSplitR; first done. done.
    - (* fold it again *)
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & %rf & HT)".
      iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".
      iPoseProof (imp_unblockable_blocked_dead lt_cur') as "#(_ & Hub)".
      set (κs' := ltype_blocked_lfts lt_cur').
      destruct (decide (κs = [] ∧ κs' = [])) as [[-> ->] | ].
      + iDestruct "HT" as "(% & %Heq & HT)". destruct Heq as [<-].
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. rewrite ltype_core_syn_type_eq. rewrite -Hst2 -Hst1 //. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        (* instantiate own_lt_cur' with ownership of lt_cur' *)
        iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
        iMod ("Hcl" $! (λ π _ l, l ◁ₗ[π, Owned false] r' @ lt_cur')%I [] with "Hpre [] Hl []") as "Ha".
        { by iApply big_sepL_nil. }
        { iModIntro. iIntros "_ Hb".
          iMod ("Hub" with "[] Hb") as "Hb". { iApply big_sepL_nil. done. }
          rewrite !ltype_own_core_equiv.
          iApply (ltype_incl_use_core with "Hincl Hb"); first done. }
        iDestruct "Ha" as "($ & Hobs & Hcl)".
        iMod ("Hcl" with "[] Hobs") as "Hl".
        { iApply big_sepL_nil. done. }
        iMod "Hcl_F" as "_". rewrite ltype_own_core_equiv. done.
      + iAssert (([∗ list] κ' ∈ κs ++ κs', ⌜lctx_lft_incl E L3 κ' κ⌝) ∗ T L3 (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs ++ κs') lt_full) (PlaceIn rf))%I with "[HT]" as "HT".
        { destruct κs, κs'; naive_solver. }
        iDestruct "HT" as "(#Hincl1 & HT)".
        iPoseProof (big_sepL_lft_incl_incl with "HE HL Hincl1") as "#Hincl2".
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. simp_ltypes. rewrite -Hst2 -Hst1. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
        iMod ("Hcl" $! (λ π _ l, l ◁ₗ[π, Owned false] r' @ lt_cur')%I (κs ++ κs') with "[Hpre] [] Hl []") as "Ha".
        { rewrite lft_dead_list_app. iIntros "(Hdead & _)". by iApply "Hpre". }
        { done. }
        { iModIntro. iIntros "#Hdead Hb".
          rewrite lft_dead_list_app. iDestruct "Hdead" as "(_ & Hdead)".
          iMod ("Hub" with "Hdead Hb") as "Hb".
          rewrite !ltype_own_core_equiv.
          iApply (ltype_incl_use_core with "Hincl Hb"); first done. }
        iDestruct "Ha" as "($ & Hobs & Hcl)".
        iMod "Hcl_F" as "_".
        iModIntro. rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iExists ly. rewrite -Hst2 -Hst1. iSplitR; first done.
        iSplitR; first done. iSplitR; first done. iFrame.
  Qed.
  Definition stratify_ltype_opened_Uniq_inst := [instance @stratify_ltype_opened_Uniq].
  Global Existing Instance stratify_ltype_opened_Uniq_inst.

  Lemma stratify_ltype_shadowed_shared {rt_cur rt_full} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (r_cur : place_rfn rt_cur) r_full κ T :
    stratify_ltype π E L mu mdu ma ml l lt_cur r_cur (Shared κ) (λ L' R rt_cur' lt_cur' (r_cur' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R rt_full (ShadowedLtype lt_cur' r_cur' lt_full) r_full
        else
          (T L' R rt_full (lt_full) (r_full))
      )
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShadowedLtype lt_cur r_cur lt_full) r_full (Shared κ) T.
  Proof.
    iIntros "Hstrat".
    iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own. iDestruct "Hl" as "(Hcur & Hfull)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hcur") as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hst' & Ha & HT)".
    iModIntro. case_decide.
    - iExists _, _, _, _, _. iFrame. simp_ltypes.
      iR. iApply (logical_step_wand with "Ha").
      iIntros "(Ha & $)". rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
      iFrame.
    - iExists _, _, _, _, _. iFrame. simp_ltypes.
      iR. iApply (logical_step_wand with "Ha").
      iIntros "(Ha & $)". iFrame.
  Qed.
  Definition stratify_ltype_shadowed_shared_inst := [instance @stratify_ltype_shadowed_shared].
  Global Existing Instance stratify_ltype_shadowed_shared_inst.

  (* TODO: OpenedNaType *)

  (* NOTE: instances for descending below MutLty, etc., are in the respective type's files. *)

  (** Unblock stratification: We define instances for the leaves of the unblocking stratifier *)
  (* On an ofty leaf, do a ghost resolution.
    This will also trigger resolve_ghost instances for custom-user defined types.
    This needs to have a lower priority than custom user-defined instances (e.g. for [◁ value_t]), so we give it a high cost. *)
  Global Instance stratify_ltype_unblock_ofty_in_inst {rt} π E L mu mdu ma l (ty : type rt) (r : place_rfn rt) b :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (◁ ty)%I r b | 100 :=
    λ T, i2p (stratify_ltype_resolve_ghost_leaf π E L mu mdu ma StratifyUnblockOp ResolveTry l (◁ ty)%I b r T).

  (* Note: instance needs to have a higher priority than the resolve_ghost instance -- we should first unblock *)
  Global Instance stratify_ltype_unblock_blocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (BlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_blocked π E L mu mdu ma StratifyUnblockOp l ty κ r b T).
  Global Instance stratify_ltype_unblock_shrblocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (ShrBlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_shrblocked π E L mu mdu ma StratifyUnblockOp l ty κ r b T).
  Global Instance stratify_ltype_unblock_coreable_inst {rt} π E L mu mdu ma l (lt lt' : ltype rt) b r κs `{!SimpLtype (ltype_core lt) lt'} :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (CoreableLtype κs lt) r b | 5 := λ T, i2p (stratify_ltype_coreable π E L mu mdu ma StratifyUnblockOp l lt _ κs r b T).

  (** Extract stratification: we also want to Unblock here *)
  Global Instance stratify_ltype_extract_blocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ κ' :
    StratifyLtype π E L mu mdu ma (StratifyExtractOp κ') l (BlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_blocked π E L mu mdu ma (StratifyExtractOp κ') l ty κ r b T).
  Global Instance stratify_ltype_extract_shrblocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ κ' :
    StratifyLtype π E L mu mdu ma (StratifyExtractOp κ') l (ShrBlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_shrblocked π E L mu mdu ma (StratifyExtractOp κ') l ty κ r b T).
  Global Instance stratify_ltype_extract_coreable_inst {rt} π E L mu mdu ma l (lt lt' : ltype rt) b r κs κ' `{!SimpLtype (ltype_core lt) lt'} :
    StratifyLtype π E L mu mdu ma (StratifyExtractOp κ') l (CoreableLtype κs lt) r b | 5 := λ T, i2p (stratify_ltype_coreable π E L mu mdu ma (StratifyExtractOp κ') l lt _ κs r b T).

  (** Resolve stratification: we also want to Unblock here *)
  Global Instance stratify_ltype_resolve_blocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ  :
    StratifyLtype π E L mu mdu ma (StratifyResolveOp) l (BlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_blocked π E L mu mdu ma (StratifyResolveOp) l ty κ r b T).
  Global Instance stratify_ltype_resolve_shrblocked_inst {rt} π E L mu mdu ma l (ty : type rt) b r κ :
    StratifyLtype π E L mu mdu ma (StratifyResolveOp) l (ShrBlockedLtype ty κ) r b | 5 := λ T, i2p (stratify_ltype_shrblocked π E L mu mdu ma (StratifyResolveOp) l ty κ r b T).
  Global Instance stratify_ltype_resolve_coreable_inst {rt} π E L mu mdu ma l (lt lt' : ltype rt) b r κs `{!SimpLtype (ltype_core lt) lt'} :
    StratifyLtype π E L mu mdu ma (StratifyResolveOp) l (CoreableLtype κs lt) r b | 5 := λ T, i2p (stratify_ltype_coreable π E L mu mdu ma (StratifyResolveOp) l lt _ κs r b T).

  (** ** place typing *)

  (** *** Instances for unblocking & updating refinements *)
  (** Note: all of these instances should have higher priority than the id instances,
        so that the client of [typed_place] does not have to do this.
      TODO: can we find an elegant way to do this for nested things (eliminate a stratify_ltype)?
        e.g. when something below is blocked and we need to unblock it, or we need to update the refinement.
        currently, the client has to do this...
        Problem why we can't directly do it: we need at least one step of computation to do it, and typed_place does not always take a step.
    *)

  (* TODO: some of this is really duplicated with stratify, in particular the unblocking and the ltype unfolding. Could we have an instance that just escapes into a shallow version of stratify that requires no logstep in order avoid duplication? *)

  (* TODO: we probably want to generalize this to not immediately require a dead token for κ,
    but rather have a "dead" context and spawn a sidecondition for inclusion in one of the dead lifetimes? *)
  Lemma typed_place_blocked_unblock {rt} π E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P T :
    [† κ] ∗ typed_place π E L l (◁ ty) r bmin0 b P T
    ⊢ typed_place π E L l (BlockedLtype ty κ) r bmin0 b P T.
  Proof.
    iIntros "(Hdead & Hp)". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_blocked with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hl").
    iIntros (L' κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & HR' & ? & ? &?)".
    iFrame.
    simp_ltypes. iR.
    by iApply typed_place_cond_blocked_l.
  Qed.
  Definition typed_place_blocked_unblock_inst := [instance @typed_place_blocked_unblock].
  Global Existing Instance typed_place_blocked_unblock_inst | 5.

  Lemma typed_place_shrblocked_unblock {rt} π E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P T :
    [† κ] ∗ typed_place π E L l (◁ ty) r bmin0 b P T
    ⊢ typed_place π E L l (ShrBlockedLtype ty κ) r bmin0 b P T.
  Proof.
    iIntros "(Hdead & Hp)". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_shrblocked with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hl").
    iIntros (L' κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & HR & ?)".
    iFrame.
    simp_ltypes. iR.
    by iApply typed_place_cond_shrblocked_l.
  Qed.
  Definition typed_place_shrblocked_unblock_inst := [instance @typed_place_shrblocked_unblock].
  Global Existing Instance typed_place_shrblocked_unblock_inst | 5.

  Lemma typed_place_coreable_unblock {rt} π E L l (lt lt' : ltype rt) κs (r : place_rfn rt) bmin0 b P `{Hsimp : !SimpLtype (ltype_core lt) lt'} T :
    lft_dead_list κs ∗ typed_place π E L l lt' r bmin0 b P T
    ⊢ typed_place π E L l (CoreableLtype κs lt) r bmin0 b P T.
  Proof.
    destruct Hsimp as [<-].
    iIntros "(Hdead & Hp)". iIntros (????) "#(LFT & TIME & LLCTX) #HE HL Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_coreable with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $TIME $LLCTX] HE HL Hl").
    iIntros (L' κs' l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & HR & ?)".
    iFrame. simp_ltypes.
    rewrite ltype_core_syn_type_eq in Hst'. rewrite Hst'. iR.
    iApply typed_place_cond_coreable_l.
    iApply typed_place_cond_trans; last done.
    iApply typed_place_cond_core.
  Qed.
  Definition typed_place_coreable_unblock_inst := [instance @typed_place_coreable_unblock].
  Global Existing Instance typed_place_coreable_unblock_inst | 5.

  Lemma typed_place_resolve_ghost {rt} π E L l (lt : ltype rt) bmin0 b γ P T :
    ⌜lctx_bor_kind_alive E L b⌝ ∗
    resolve_ghost π E L ResolveAll false l lt b (PlaceGhost γ) (λ L' r R progress,
      introduce_with_hooks E L' R (λ L'', typed_place π E L'' l lt r bmin0 b P T))
    ⊢ typed_place π E L l lt (PlaceGhost γ) bmin0 b P T.
  Proof.
    iIntros "(%Hw & Hres)". iIntros (????) "#CTX #HE HL Hl HΦ".
    iApply fupd_place_to_wp.
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L' & %r & %R & %prog & Hstep & HL & HP)"; [done.. | ].
    iMod "Hstep" as "(Hl & HR)".
    iMod ("HP" with "[] HE HL HR") as "(%L'' & HL & HP)"; first done.
    iModIntro. iApply ("HP" with "[//] [//] CTX HE HL Hl").
    iIntros (L1 κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iApply ("Hs" with "HL"). simp_ltypes. done.
  Qed.
  (* this needs to have a lower priority than place_blocked_unblock *)
  Definition typed_place_resolve_ghost_inst := [instance @typed_place_resolve_ghost].
  Global Existing Instance typed_place_resolve_ghost_inst | 8.

  (** *** Place access instances *)

  Import EqNotations.


  (* instances for Opened *)
  (* NOTE: these should have a higher priority than place id, because we always want to descend below Opened when accessing a place, in order to get the actual current type *)
  Lemma typed_place_opened_owned π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l wl P T :
    (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
    typed_place π E L l lt_cur r UpdStrong (Owned false) P (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont,
          updcx L2 upd (λ upd',
            cont (mkPUpd _ UpdStrong
            (upd').(pupd_rt)
            (OpenedLtype (upd').(pupd_lt) lt_inner lt_full Cpre Cpost)
            (upd').(pupd_rfn)
            (upd').(pupd_R)
            UpdStrong I I))))
    ⊢ typed_place π E L l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r UpdStrong (Owned wl) P T.
  Proof.
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL Hl HR".
    iPoseProof (opened_ltype_acc_owned with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hl").
    iIntros (L' ??????? updcx) "Hl Hv".
    iApply ("HR" with "Hl").
    iIntros (upd) "Hincl Hl %Hst HR Hcond". simpl.
    iMod ("Hv" with "Hincl Hl [//] HR Hcond") as "Hv".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hv" with "HL Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & ? & ? & ?)".
    iFrame.
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    eauto with iFrame.
  Qed.
  Definition typed_place_opened_owned_inst := [instance @typed_place_opened_owned].
  Global Existing Instance typed_place_opened_owned_inst | 5.

  Lemma typed_place_opened_uniq π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l κ γ P T :
    (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
    typed_place π E L l lt_cur r UpdStrong (Owned false) P (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont,
          updcx L2 upd (λ upd',
            cont (mkPUpd _ UpdStrong
            (upd').(pupd_rt)
            (OpenedLtype (upd').(pupd_lt) lt_inner lt_full Cpre Cpost)
            (upd').(pupd_rfn)
            (upd').(pupd_R)
            UpdStrong I I))))
    ⊢ typed_place π E L l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r UpdStrong (Uniq κ γ) P T.
  Proof.
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL Hl HR".
    iPoseProof (opened_ltype_acc_uniq with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hl").
    iIntros (L' ??????? updcx) "Hl Hv".
    iApply ("HR" with "Hl").
    iIntros (upd) "Hincl Hl %Hst HR Hcond". simpl.
    iMod ("Hv" with "Hincl Hl [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & ? & ? & ?)".
    simpl.
    iFrame.
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    eauto with iFrame.
  Qed.
  Definition typed_place_opened_uniq_inst := [instance @typed_place_opened_uniq].
  Global Existing Instance typed_place_opened_uniq_inst | 5.

  Lemma typed_place_shadowed_shared π E L {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) r_cur (r_full : place_rfn rt_full) bmin0 l κ P (T : place_cont_t rt_full bmin0) :
    (* sidecondition needed for the weak update *)
    ⌜lctx_place_update_kind_outlives E L bmin0 (ltype_blocked_lfts lt_full)⌝ ∗
    typed_place π E L l lt_cur (#r_cur) bmin0 (Shared κ) P (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont,
          updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
            rt_full
            (ShadowedLtype (upd').(pupd_lt) (upd').(pupd_rfn) lt_full)
            r_full
            (upd').(pupd_R)
            (* TODO: basically, we can unblock at _any_ lifetime. so we could strengthen this. *)
            bmin0 opt_place_update_eq_refl opt_place_update_eq_refl)))
    )
    ⊢ typed_place π E L l (ShadowedLtype lt_cur (#r_cur) lt_full) r_full bmin0 (Shared κ) P T.
  Proof.
    iIntros "(%Houtl & HT)".
    iIntros (????) "#CTX #HE HL Hl Hc".
    iPoseProof (lctx_place_update_kind_outlives_use _ _ _ _ Houtl with "HE HL") as "#Houtl'".
    iPoseProof (shadowed_ltype_acc_cur with "Hl") as "(Hcur & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hcur").
    iIntros (L' κs l2 b2 bmin rti ltyi ri updcx) "Hl Hcc".
    iApply ("Hc" with "Hl").

    iIntros (upd) "Hincl Hl %Hst HR Hcond". simpl in *.
    iMod ("Hcc" with "Hincl Hl [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iMod ("Hs" with "HL Hcont") as (upd') "(Hl & %Hst' & Hcond' & Htoks & HR & ? & ?)".
    simpl.
    iPoseProof ("Hcl" with "[] Hl") as "Hl".
    { done. }
    simpl. iFrame. simpl. iFrame.
    simp_ltypes. iR.
    iSplitL; last iApply place_update_kind_incl_refl.
    iApply typed_place_cond_shadowed_update_cur. done.
  Qed.
  Definition typed_place_shadowed_shared_inst := [instance @typed_place_shadowed_shared].
  Global Existing Instance typed_place_shadowed_shared_inst | 5.

  (* TODO: OpenedNaType *)

  (** Typing hints *)
  Lemma interpret_typing_hint_ignore orty E L bmin {rt} (ty : type rt) r (T : interpret_typing_hint_cont_t bmin rt) :
    T rt ty r (mkPUKRes UpdBot eq_refl opt_place_update_eq_refl)
    ⊢ interpret_typing_hint E L orty bmin ty r T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iFrame. iSplitL.
    { iApply type_incl_refl. }
    iSplitL.
    { iApply typed_place_cond_refl_ofty. }
    iApply upd_bot_min.
  Qed.
  Definition interpret_typing_hint_none := interpret_typing_hint_ignore None.
  Definition interpret_typing_hint_none_inst := [instance @interpret_typing_hint_none].
  Global Existing Instance interpret_typing_hint_none_inst.

  Lemma interpret_typing_hint_some_strong E L rty {rt} (ty : type rt) r (T : interpret_typing_hint_cont_t UpdStrong rt) :
    find_in_context (FindNamedLfts) (λ M, named_lfts M -∗
      (** Interpret the type annotation *)
      li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt2 ty2),
      (* TODO it would be really nice to have a stronger form of subtyping here that also supports unfolding/folding of invariants *)
      ∃ r2, weak_subtype E L r r2 ty ty2 (
        T rt2 ty2 r2 (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))))
    ⊢ interpret_typing_hint E L (Some rty) UpdStrong ty r T.
  Proof.
    iIntros "HT".
    rewrite /FindNamedLfts.
    iDestruct "HT" as "(%M & HM & HT)". iPoseProof ("HT" with "HM") as "Ha".
    rewrite /interpret_rust_type_goal. iDestruct "Ha" as "(%rt2 & %ty2 & %r2 & HT)".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(#Hincl3 & HL & HT)".
    iModIntro. iPoseProof "Hincl3" as "(%Hsteq' & _)".
    set (updstrong := mkPUKRes (allowed:=UpdStrong)(rt1:=rt)(rt2:=rt2) UpdStrong I I).
    iExists rt2, ty2, r2, updstrong. by iFrame "HL HT".
  Qed.
  Definition interpret_typing_hint_some_strong_inst := [instance @interpret_typing_hint_some_strong].
  Global Existing Instance interpret_typing_hint_some_strong_inst.

  Lemma interpret_typing_hint_some_weak E L rty {rt} (ty : type rt) r (T : interpret_typing_hint_cont_t UpdWeak rt) :
    find_in_context (FindNamedLfts) (λ M, named_lfts M -∗
      (** Interpret the type annotation *)
      li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt2 ty2),
      (* TODO it would be really nice to have a stronger form of subtyping here that also supports unfolding/folding of invariants *)
      ∃ (Heq : rt = rt2),
      ∃ r2, weak_subtype E L r r2 ty ty2 (
        T rt2 ty2 r2 (mkPUKRes (allowed:=UpdWeak) UpdWeak Heq Heq))))
    ⊢ interpret_typing_hint E L (Some rty) UpdWeak ty r T.
  Proof.
    iIntros "HT".
    rewrite /FindNamedLfts.
    iDestruct "HT" as "(%M & HM & HT)". iPoseProof ("HT" with "HM") as "Ha".
    rewrite /interpret_rust_type_goal. iDestruct "Ha" as "(%rt2 & %ty2 & %Heq & %r2 & HT)".
    subst.
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(#Hincl3 & HL & HT)".
    iModIntro. iPoseProof "Hincl3" as "(%Hsteq' & _)".
    set (updstrong := mkPUKRes (allowed:=UpdWeak)(rt1:=rt2)(rt2:=rt2) UpdWeak eq_refl eq_refl).
    iExists rt2, ty2, r2, updstrong. iFrame "HL HT".
    iR. done.
  Qed.
  Definition interpret_typing_hint_some_weak_inst := [instance @interpret_typing_hint_some_weak].
  Global Existing Instance interpret_typing_hint_some_weak_inst.


  (** typing of expressions *)
  Lemma typed_val_expr_wand E L e T1 T2 :
    typed_val_expr E L e T1 -∗
    (∀ L' π v rt ty r, T1 L' π v rt ty r -∗ T2 L' π v rt ty r) -∗
    typed_val_expr E L e T2.
  Proof.
    iIntros "He HT" (Φ) "#LFT #HE HL HΦ".
    iApply ("He" with "LFT HE HL"). iIntros (L' π v rt ty r) "HL Hv Hty".
    iApply ("HΦ" with "HL Hv"). by iApply "HT".
  Qed.

  Lemma typed_if_wand E L v (P T1 T2 T1' T2' : iProp Σ):
    typed_if E L v P T1 T2 -∗
    ((T1 -∗ T1') ∧ (T2 -∗ T2')) -∗
    typed_if E L v P T1' T2'.
  Proof.
    iIntros "Hif HT Hv". iDestruct ("Hif" with "Hv") as (b ?) "HC".
    iExists _. iSplit; first done. destruct b.
    - iDestruct "HT" as "[HT _]". by iApply "HT".
    - iDestruct "HT" as "[_ HT]". by iApply "HT".
  Qed.

  Lemma typed_bin_op_wand E L v1 P1 Q1 v2 P2 Q2 op ot1 ot2 T:
    typed_bin_op E L v1 Q1 v2 Q2 op ot1 ot2 T -∗
    (P1 -∗ Q1) -∗
    (P2 -∗ Q2) -∗
    typed_bin_op E L v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "H Hw1 Hw2 H1 H2".
    iApply ("H" with "[Hw1 H1]"); [by iApply "Hw1"|by iApply "Hw2"].
  Qed.

  Lemma typed_un_op_wand E L v P Q op ot T:
    typed_un_op E L v Q op ot T -∗
    (P -∗ Q) -∗
    typed_un_op E L v P op ot T.
  Proof.
    iIntros "H Hw HP". iApply "H". by iApply "Hw".
  Qed.

  Definition uncurry_rty {T} (f : ∀ rt, type rt → rt → T) : sigT (λ rt, type rt * rt)%type → T :=
    λ '(existT rt (ty, r)), f rt ty r.

  Lemma type_val_context v π (T : typed_value_cont_t) :
    (find_in_context (FindVal v) (λ '(existT rt (ty, r, π')),
      ⌜π = π'⌝ ∗ T rt ty r)) ⊢
    typed_value π v T.
  Proof.
    iDestruct 1 as ([rt [[ty r] π']]) "(Hv & <- & HT)". simpl in *.
    iIntros "LFT". iExists _, _, _. iFrame.
  Qed.
  Global Instance type_val_context_inst v π :
    TypedValue π v | 100 := λ T, i2p (type_val_context v π T).

  Lemma type_val E L v T :
    find_in_context (FindNaOwn) (λ '(π, E),
      na_own π E -∗ typed_value π v (T L π v)) ⊢
    typed_val_expr E L (Val v) T.
  Proof.
    iIntros "Hv" (Φ) "#LFT #HE HL HΦ".
    iDestruct "Hv" as ([π F]) "(Hna & HT)".
    iDestruct ("HT" with "Hna") as "HT".
    iDestruct ("HT" with "LFT") as "(%rt & %ty & %r & Hty & HT)".
    iApply wp_value. iApply ("HΦ" with "HL Hty HT").
  Qed.

  Lemma type_val_with_π π E L v T :
    typed_value π v (T L π v) ⊢
    typed_val_expr E L (Val v) T.
  Proof.
    iIntros "Hv" (Φ) "#LFT #HE HL HΦ".
    iDestruct ("Hv" with "LFT") as "(%rt & %ty & %r & Hty & HT)".
    iApply wp_value. iApply ("HΦ" with "HL Hty HT").
  Qed.

  Fixpoint interpret_rust_types (M : gmap string lft) (tys : list rust_type) (T : list (sigT type) → iProp Σ) :  iProp Σ :=
    match tys with
    | [] => T []
    | ty :: tys =>
        li_tactic (interpret_rust_type_goal M ty)
          (λ ty, interpret_rust_types M tys (λ tys, T (ty :: tys)))
    end.
  Lemma interpret_rust_types_elim M tys T :
    interpret_rust_types M tys T -∗
    ∃ tys, T tys.
  Proof.
    iIntros "Ha". iInduction tys as [ | ty tys] "IH" forall (T); simpl.
    - iExists []. done.
    - rewrite /li_tactic/interpret_rust_type_goal.
      iDestruct "Ha" as "(%rt & %ty' & Ha)".
      iPoseProof ("IH" with "Ha") as "(%tys' & HT)".
      eauto.
  Qed.

  Lemma type_call E L T ef eκs etys es :
    (∃ M, named_lfts M ∗
    li_tactic (compute_map_lookups_nofail_goal M eκs) (λ eκs',
    interpret_rust_types M etys (λ atys,
    named_lfts M -∗
    typed_val_expr E L ef (λ L' π vf rtf tyf rf,
        foldr (λ e T L'' vl tys, typed_val_expr E L'' e (λ L''' π' v rt ty r,
          ⌜π' = π⌝ ∗
          T L''' (vl ++ [v]) (tys ++ [existT rt (ty, r)])))
              (λ L'' vl tys, typed_call π E L'' eκs' atys vf (vf ◁ᵥ{π} rf @ tyf) vl tys T)
              es L' [] []))))
    ⊢ typed_val_expr E L (CallE ef eκs etys es) T.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %eκs' & _ & He)".
    iPoseProof (interpret_rust_types_elim with "He") as "(%tys & He)".
    iIntros (Φ) "#CTX #HE HL HΦ".
    rewrite /CallE.
    iApply wp_call_bind. iApply ("He" with "Hnamed CTX HE HL"). iIntros (L' π vf rtf tyf rf) "HL Hvf HT".
    iAssert ([∗ list] v;rty∈[];([] : list $ @sigT RT (λ rt, (type rt * rt)%type)), let '(existT rt (ty, r)) := rty in v ◁ᵥ{π} r @ ty)%I as "-#Htys". { done. }
    move: {2 3 5} ([] : list val) => vl.
    generalize (@nil (@sigT RT (fun rt : RT => prod (@type Σ H rt) rt))) at 2 3 as tys'; intros tys'.
    iInduction es as [|e es] "IH" forall (L' vl tys') => /=. 2: {
      iApply ("HT" with "CTX HE HL"). iIntros (L'' π' v rt ty r) "HL Hv (-> & Hnext)".
      iApply ("IH" with "HΦ HL Hvf Hnext").
      iFrame. by iApply big_sepL2_nil.
    }
    by iApply ("HT" with "Hvf Htys CTX HE HL").
  Qed.

  Lemma type_bin_op E L o e1 e2 ot1 ot2 T :
    typed_val_expr E L e1 (λ L1 π1 v1 rt1 ty1 r1, typed_val_expr E L1 e2 (λ L2 π2 v2 rt2 ty2 r2,
      ⌜π1 = π2⌝ ∗ typed_bin_op E L2 v1 (v1 ◁ᵥ{π1} r1 @ ty1) v2 (v2 ◁ᵥ{π1} r2 @ ty2) o ot1 ot2 T))
    ⊢ typed_val_expr E L (BinOp o ot1 ot2 e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL HΦ".
    wp_bind. iApply ("He1" with "LFT HE HL"). iIntros (L1 π1 v1 rt1 ty1 r1) "HL Hv1 He2".
    wp_bind. iApply ("He2" with "LFT HE HL"). iIntros (L2 π2 v2 rt2 ty2 r2) "HL Hv2 (<- & Hop)".
    iApply ("Hop" with "Hv1 Hv2 LFT HE HL HΦ").
  Qed.

  Lemma type_un_op E L o e ot T :
    typed_val_expr E L e (λ L' π v rt ty r, typed_un_op E L' v (v ◁ᵥ{π} r @ ty) o ot T)
    ⊢ typed_val_expr E L (UnOp o ot e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL HΦ".
    wp_bind. iApply ("He" with "LFT HE HL"). iIntros (L' π v rt ty r) "HL Hv Hop".
    by iApply ("Hop" with "Hv LFT HE HL").
  Qed.

  Lemma type_check_bin_op E L o e1 e2 ot1 ot2 T :
    typed_val_expr E L e1 (λ L1 π1 v1 rt1 ty1 r1, typed_val_expr E L1 e2 (λ L2 π2 v2 rt2 ty2 r2,
      ⌜π1 = π2⌝ ∗ typed_check_bin_op E L2 v1 (v1 ◁ᵥ{π1} r1 @ ty1) v2 (v2 ◁ᵥ{π1} r2 @ ty2) o ot1 ot2 T))
    ⊢ typed_val_expr E L (CheckBinOp o ot1 ot2 e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL HΦ".
    wp_bind. iApply ("He1" with "LFT HE HL"). iIntros (L1 π1 v1 rt1 ty1 r1) "HL Hv1 He2".
    wp_bind. iApply ("He2" with "LFT HE HL"). iIntros (L2 π2 v2 rt2 ty2 r2) "HL Hv2 (<- & Hop)".
    iApply ("Hop" with "Hv1 Hv2 LFT HE HL HΦ").
  Qed.

  Lemma type_check_un_op E L o e ot T :
    typed_val_expr E L e (λ L' π v rt ty r, typed_check_un_op E L' v (v ◁ᵥ{π} r @ ty) o ot T)
    ⊢ typed_val_expr E L (CheckUnOp o ot e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL HΦ".
    wp_bind. iApply ("He" with "LFT HE HL"). iIntros (L' π v rt ty r) "HL Hv Hop".
    by iApply ("Hop" with "Hv LFT HE HL").
  Qed.

  Lemma type_ife E L e1 e2 e3 T:
    typed_val_expr E L e1 (λ L' π v rt ty r,
      typed_if E L' v (v ◁ᵥ{π} r @ ty) (typed_val_expr E L' e2 T) (typed_val_expr E L' e3 T))
    ⊢ typed_val_expr E L (IfE BoolOp e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL HΦ".
    wp_bind. iApply ("He1" with "LFT HE HL"). iIntros (L1 π v1 rt1 ty1 r1) "HL Hv1 Hif".
    iDestruct ("Hif" with "Hv1") as "HT".
    iDestruct "HT" as (b) "(% & HT)".
    iApply wp_if_bool; [done|..]. iIntros "!> Hcred".
    destruct b; by iApply ("HT" with "LFT HE HL").
  Qed.

  Lemma type_annot_expr E L n {A} (a : A) e T:
    typed_val_expr E L e (λ L' π v rt ty r, typed_annot_expr E L' n a v (v ◁ᵥ{π} r @ ty) T)
    ⊢ typed_val_expr E L (AnnotExpr n a e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL HΦ".
    wp_bind. iApply ("He" with "LFT HE HL"). iIntros (L' π v rt ty r) "HL Hv HT".
    iDestruct ("HT" with "LFT HE HL Hv") as "HT".
    iInduction n as [|n] "IH" forall (Φ). {
      rewrite /AnnotExpr/=.
      iApply fupd_wp.
      iMod "HT" as "(%L2 & %π' & % & % & % & HL & Hv & Hf)".
      iApply wp_value.
      iApply ("HΦ" with "[$] [$] [$]").
    }
    rewrite annot_expr_S_r. wp_bind.
    iApply wp_skip. iIntros "!> Hcred".
    iApply fupd_wp. iMod "HT".
    iMod (lc_fupd_elim_later with "Hcred HT") as ">HT". iModIntro.
    iApply ("IH" with "HΦ HT").
  Qed.

  Lemma type_logical_and E L e1 e2 T:
    typed_val_expr E L e1 (λ L1 π1 v1 rt1 ty1 r1, typed_if E L1 v1 (v1 ◁ᵥ{π1} r1 @ ty1)
       (typed_val_expr E L1 e2 (λ L2 π2 v2 rt2 ty2 r2, typed_if E L2 v2 (v2 ◁ᵥ{π2} r2 @ ty2)
           (typed_value π1 (val_of_bool true) (T L2 π1 (val_of_bool true)))
           (typed_value π1 (val_of_bool false) (T L2 π1 (val_of_bool false)))))
       (typed_value π1 (val_of_bool false) (T L1 π1 (val_of_bool false))))
    ⊢ typed_val_expr E L (e1 &&{BoolOp, BoolOp, U8} e2)%E T.
  Proof.
    iIntros "HT". rewrite /LogicalAnd. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L1 π v rt ty r) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    2: { iApply type_val_with_π. by rewrite !val_of_bool_i2v. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L2 π2 v2 rt2 ty2 r2) "HT".
    iApply (typed_if_wand with "HT").
    iSplit; iIntros "HT"; iApply type_val_with_π; by rewrite !val_of_bool_i2v.
  Qed.

  Lemma type_logical_or E L e1 e2 T:
    typed_val_expr E L e1 (λ L1 π1 v1 rt1 ty1 r1, typed_if E L1 v1 (v1 ◁ᵥ{π1} r1 @ ty1)
      (typed_value π1 (val_of_bool true) (T L1 π1 (val_of_bool true)))
      (typed_val_expr E L1 e2 (λ L2 π2 v2 rt2 ty2 r2,
        typed_if E L2 v2 (v2 ◁ᵥ{π2} r2 @ ty2)
          (typed_value π1 (val_of_bool true) (T L2 π1 (val_of_bool true)))
          (typed_value π1 (val_of_bool false) (T L2 π1 (val_of_bool false))))))
    ⊢ typed_val_expr E L (e1 ||{BoolOp, BoolOp, U8} e2)%E T.
  Proof.
    iIntros "HT". rewrite /LogicalOr. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L1 π1 v rt ty r) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    1: { iApply type_val_with_π. by rewrite !val_of_bool_i2v. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L2 π2 v2 rt2 ty2 r2) "HT".
    iApply (typed_if_wand with "HT").
    iSplit; iIntros "HT"; iApply type_val_with_π; by rewrite !val_of_bool_i2v.
  Qed.

  (** Similar to type_assign, use is formulated with a skip over the expression, in order to allow
    on-demand unblocking. We can't just use any of the potential place access steps, because there might not be any (if it's just a location). So we can't easily use any of the other steps around.
   *)
  Lemma type_use E L ot e o (T : typed_read_cont_t) :
    ⌜if o is Na2Ord then False else True⌝ ∗
      typed_read E L e ot (λ L2 π v rt ty r,
        introduce_with_hooks E L2 (atime 2 ∗ £ num_cred) (λ L3,
          T L3 π v rt ty r))
    ⊢ typed_val_expr E L (use{ot, o} e)%E T.
  Proof.
    iIntros "[% Hread]" (Φ) "#(LFT & TIME & LLCTX) #HE HL HΦ".
    wp_bind.
    iApply ("Hread" $! _ ⊤ with "[//] [//] [//] [//] [$TIME $LFT $LLCTX] HE HL").
    iIntros (l) "Hl".
    iApply ewp_fupd.
    rewrite /Use. wp_bind.
    iApply (wp_logical_step with "TIME Hl"); [solve_ndisj.. | ].
    iMod (persistent_time_receipt_0) as "#Hp".
    iMod (additive_time_receipt_0) as "Ha".
    iApply (wp_skip_credits with "TIME Ha Hp"); first done.
    iNext. iIntros "Hcred Hat".
    iIntros "(%v & %q & %π & %rt & %ty & %r & %Hlyv & %Hv & Hl & Hv & Hcl)".
    iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref_credits with "TIME Hat Hp Hl") => //; try by eauto using val_to_of_loc.
    { destruct o; naive_solver. }
    iIntros "!> %st Hl Hcred2 Hat Hcl".
    iMod ("Hcl" with "Hl Hv") as "(%L' & %rt' & %ty' & %r' & HL & Hv & HT)"; iModIntro.
    iDestruct "Hcred2" as "(Hcred1' & Hcred2)".
    iMod ("HT" with "[] HE HL [$Hat $Hcred2]") as "(%L3 & HL & HT)"; first done.
    by iApply ("HΦ" with "HL Hv HT").
  Qed.

  (* TODO move *)
  Lemma num_laters_per_step_linear n m :
    num_laters_per_step (n + m) = num_laters_per_step n + num_laters_per_step m.
  Proof.
    rewrite /num_laters_per_step/=. lia.
  Qed.

  (* This lemma is about AssignSE, which adds a skip around the LHS expression.
     The reason is that we might need to unblock e1 first and only after that get access to the location we need for justifying the actual write
      - so we can't just use the actual write step,
      - and we also cannot use the place access on the LHS itself, because that might not even take a step (if it's just a location).
     *)
  Lemma type_assign E L ot e1 e2 s fn R o ϝ :
    typed_val_expr E L e2 (λ L' π v rt ty r, ⌜if o is Na2Ord then False else True⌝ ∗
      typed_write π E L' e1 ot v ty r (λ L2,
        introduce_with_hooks E L2 (atime 2 ∗ £ num_cred) (λ L3,
        typed_stmt E L3 s fn R ϝ)))
    ⊢ typed_stmt E L (e1 <-{ot, o} e2; s) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#(LFT & TIME & LLCTX) #HE HL Hcont".
    wps_bind. iApply ("He" with "[$TIME $LFT $LLCTX] HE HL"). iIntros (L' π v rt ty r) "HL Hv [% He1]".
    wps_bind. iApply ("He1" $! _ ⊤ with "[//] [//] [//] [//] [$TIME $LFT $LLCTX] HE HL"). iIntros (l) "HT".
    unfold AssignSE. wps_bind.
    iSpecialize ("HT" with "Hv").
    iApply (wp_logical_step with "TIME HT"); [solve_ndisj.. | ].
    iMod (persistent_time_receipt_0) as "#Hp".
    iMod (additive_time_receipt_0) as "Ha".
    iApply (wp_skip_credits with "TIME Ha Hp"); first done.
    iNext. iIntros "Hcred Ha (Hly & Hl & Hcl)".
    iModIntro.
    (* TODO find a way to do this without destructing the logstep *)
    rewrite /logical_step.
    iMod "Hcl" as "(%n & Hat & Hcl)".
    iCombine "Ha Hat" as "Hat".
    iApply (wps_assign_credits with "TIME Hp Hat"); rewrite ?val_to_of_loc //. { destruct o; naive_solver. }
    iMod (fupd_mask_subseteq) as "Hcl_m"; last iApply fupd_intro.
    { destruct o; solve_ndisj. }
    iFrame. iNext. iIntros "Hl Hat Hcred'". iMod "Hcl_m" as "_".
    rewrite Nat.add_0_r. iDestruct "Hcred'" as "(Hcred1 & Hcred')".
    iEval (rewrite (additive_time_receipt_sep 1)) in "Hat".
    iEval (rewrite (additive_time_receipt_sep 1)) in "Hat".
    iDestruct "Hat" as "(Hat1 & Hat1' & Hat)".
    rewrite Nat.add_0_r.
    rewrite num_laters_per_step_linear.
    iDestruct "Hcred'" as "(Hcred2 & Hcred')".
    iMod ("Hcl" with "Hcred' Hat Hl") as ">(%L'' & HL & Hs)".
    iCombine "Hat1 Hat1'" as "Hat".
    iMod ("Hs" with "[] HE HL [$Hat $Hcred2]") as "(%L3 & HL & HT)"; first done.
    by iApply ("HT" with "[$TIME $LFT $LLCTX] HE HL").
  Qed.

  Lemma type_mut_addr_of E L e T :
    typed_addr_of_mut E L e T
    ⊢ typed_val_expr E L (&raw{Mut} e)%E T.
  Proof.
    iIntros "HT" (?) "#CTX #HE HL Hcont".
    rewrite /Raw. wp_bind.
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] CTX HE HL").
    iIntros (l) "HT".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wp_logical_step with "TIME HT"); [done.. | ].
    iApply wp_skip. iNext. iIntros "Hcred".
    iDestruct 1 as (L' π rt ty r) "(Hl & HL & HT)".
    iApply ("Hcont" with "HL Hl HT").
  Qed.
  (* Corresponding lemmas for borrows are in references.v *)


  Import EqNotations.
  (** Entry point for checking reads *)
  Lemma type_read E L T T' e ot :
    (** Decompose the expression *)
    IntoPlaceCtx E e T' →
    T' L (λ L' K l,
      (** Find the type assignment *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      (** Check the place access *)
      typed_place π E L' l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto bmin UpdStrong),
        (** Stratify *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (** Omitted from the paper: Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (** Require the stratified place to be a value type *)
        (* TODO remove this and instead have a [ltype_read_as] TC or so. Currently this will prevent us from reading from ShrBlocked*)
        cast_ltype_to_type E L2 lt3 (λ ty3,
        (** Finish reading *)
        typed_read_end π E L2 l2 (◁ ty3) ri3 b2 bmin ot (λ L3 v rt3 ty3 r3 rt2' lt2' ri2' upd2,
        typed_place_finish π E L3 updcx (place_update_kind_res_trans upd upd2) (R ∗ llft_elt_toks κs) l b lt2' ri2' (λ L4, T L4 π v _ ty3 r3))
      ))))))%I
    ⊢ typed_read E L e ot T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL HΦ".
    iApply (HT' with "CTX HE HL HT'").
    iIntros (L' K l) "HL". iDestruct 1 as ([rt ([[ty r] π] & ?)]) "[Hl HP]".
    iApply ("HP" with "[//] [//] CTX HE HL Hl").
    iIntros (L'' κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply "HΦ".
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L2 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & %Hst' & HT)".
    iApply (logical_step_wand with "Hl2").
    iIntros "!> (Hl2 & HR)".
    iDestruct "HT" as "(%ty3 & %Heqt & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heqt.
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "(Hincl' & HL)"; first done; first apply Heqt.
    iMod  ("Hincl'" with "Hl2") as "Hl2".
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl2") as "Hread".
    iDestruct "Hread" as (q v rt2 ty2' r2) "(% & % & Hl2 & Hv & Hcl)".
    iModIntro. iExists v, q, _, _, _, _. iR. iR.
    iFrame "Hl2 Hv".
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl" (st) "Hl2 Hv".
    iMod ("Hcl" $! st with "Hl2 Hv") as (L3 rt4 ty4 r4) "(Hmv & HL & Hcl)".
    iDestruct "Hcl" as "(%rt' & %lt' & %r' & %res & Hl2 & %Hsteq & #Hincl2 & Hcond2 & Hfin)" => /=.

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd res) lt' r').

    iMod ("Hs" $! upd_inner with "[] Hl2 [] [] [Hcond Hcond2]") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. rewrite Hsteq Hst'.
      unshelve iSpecialize ("Heq" $! inhabitant inhabitant); [apply _.. | ].
      iPoseProof (ltype_eq_syn_type with "Heq") as "->".
      done. }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply ltype_eq_place_cond_ty_trans; first iApply "Heq".
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }
    iMod ("Hs" with "HL Hfin") as (upd') "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & HT)".
    iPoseProof ("HT" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _, _, _, _. iFrame.
  Qed.

  (** [type_read_end] instance that does a copy *)
  Lemma type_read_ofty_copy E L {rt} π b2 bmin l (ty : type rt) r ot `{!Copyable ty} (T : typed_read_end_cont_t bmin rt) :
    (** We have to show that the type allows reads *)
    (⌜ty_has_op_type ty ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗
      (** The place is left as-is *)
      ∀ v, T L v rt ty r rt (◁ ty) (#r) (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl))
    ⊢ typed_read_end π E L l (◁ ty) (#r) b2 bmin ot T.
  Proof.
    iIntros "(%Hot & %Hal & Hs)".
    iIntros (F ????) "#CTX #HE HL".

    set (weak_upd := (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)).

    destruct b2 as [ wl | | ]; simpl.
    - iIntros "Hb".
      iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & #Hv & Hcl))"; first done.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      specialize (ty_op_type_stable Hot) as Halg''.
      assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
      iModIntro. iExists _, _, rt, _, _.
      iFrame "Hl Hv".
      iSplitR; first done. iSplitR; first done.
      iApply (logical_step_wand with "Hcl").
      iIntros "Hcl %st Hl _". iMod ("Hcl" with "Hl [//] Hsc Hv") as "Hl".
      iModIntro. iExists L, rt, ty, r.
      iPoseProof (ty_memcast_compat with "Hv") as "Ha"; first done. iFrame "Ha HL".
      iExists _, _, _, weak_upd. iFrame.
      iR. iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      by iApply "Hs".
    - iIntros "#Hl".
      simpl in Hal.
      iPoseProof (ofty_ltype_acc_shared with "Hl") as "(%ly & %Halg & %Hly & Hlb & >Hl')"; first done.
      assert (ly = ot_layout ot) as ->.
      { specialize (ty_op_type_stable Hot) as ?. eapply syn_type_has_layout_inj; done. }

      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Htok & HL & Hclose)"; [solve_ndisj | done | ].
      iMod (copy_shr_acc with "CTX Hl' Htok") as "(>%Hly' & (%q'' & %v & (>Hll & #Hv) & Hclose_l))";
        [solve_ndisj.. | done | ].

      iDestruct (ty_own_val_has_layout with "Hv") as "#>%Hlyv"; first done.
      iModIntro. iExists _, _, rt, _, _. iFrame "Hll Hv".
      iSplitR; first done. iSplitR; first done.
      iApply logical_step_intro. iIntros (st) "Hll Hv'".
      iMod ("Hclose_l" with "[Hv Hll]") as "Htok".
      { eauto with iFrame. }
      iMod ("Hclose" with "Htok HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro. iExists L, rt, ty, r.
      iPoseProof (ty_memcast_compat with "Hv'") as "Hid"; first done. simpl. iFrame.

      iExists _, _, _, weak_upd.
      iFrame "Hl".
      iR. iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      by iApply "Hs".
    - iIntros "Hl".
      simpl in Hal.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as (q') "(Htok & HL_cl2)"; [solve_ndisj | ].
      iPoseProof (ofty_ltype_acc_uniq with "CTX Htok HL_cl2 Hl") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
      iMod "HF_cl" as "_".
      assert (ly = ot_layout ot) as ->.
      { specialize (ty_op_type_stable Hot) as ?. eapply syn_type_has_layout_inj; done. }
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iSplitR; first done.
      iApply logical_step_mask_mono; last iApply (logical_step_wand with "Hcl"); first done.
      iIntros "[Hcl _]".
      iIntros (st) "Hl #Hv".
      iMod (fupd_mask_mono with "(Hcl Hl Hv)") as "(Hl & HL)"; first done.
      iPoseProof ("HL_cl" with "HL") as "HL".
      iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.
      iModIntro. iExists L, rt, ty, r. iFrame "Hid HL".

      iExists _, _, _, weak_upd.
      iFrame "Hl".
      iR. iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      by iApply "Hs".
  Qed.
  Definition type_read_ofty_copy_inst := [instance @type_read_ofty_copy].
  Global Existing Instance type_read_ofty_copy_inst | 10.

  (*
  For more generality, maybe have LtypeReadAs lty (λ ty r, ...)
    that gives us an accessor as a type?
    => this should work fine.
     - T ty .. (Shared κ) -∗ LtypeReadAs (ShrBlocked ty) T
     - T ty .. k -∗ LtypeReadAs (◁ ty) T
     -
  How does that work for moves? Well, we cannot move if it isn't an OfTy.
     so there we should really cast first.
  Note here: we should only trigger the copy instance if we can LtypeReadAs as something that is copy.
     So we should really make that a TC and make it a precondition, similar to SimplifyHyp etc.

  And similar for LtypeWriteAs lty (λ ty r, ...)?
    well, there it is more difficult, because it even needs to hold if there are Blocked things below.
    I don't think we can nicely solve that part.
   *)

  (** NOTE instance for moving is defined in value.v *)

  (** Reading products: read each of the components in sequence *)
  (* TODO check if this is the right thing to do.
  Lemma type_read_prod E L π {rt1 rt2} `{ghost_varG Σ rt1} `{ghost_varG Σ rt2} `{ghost_varG Σ ((place_rfn rt1) * (place_rfn rt2))} b2 bmin l (lt1 : lty rt1) (lt2: lty rt2) r1 r2 sl ot
    (T : val → ∀ rt', ghost_varG Σ rt' → lty rt' → place_rfn rt' → type (place_rfn rt1 * place_rfn rt2)%type → (place_rfn rt1 * place_rfn rt2) → iProp Σ) :
    typed_read_end E L π (GetMemberLoc l sl "0") rt1 lt1 r1 b2 bmin ot (λ v1 rt1' _ lt1' r1' ty1 r1t,
      typed_read_end E L π (GetMemberLoc l sl "1") rt2 lt2 r2 b2 bmin ot (λ v2 rt2' _ lt2' r2' ty2 r2t,
        li_tactic (find_gvar_inst_goal (place_rfn rt1' * place_rfn rt2')) (λ _,
        T (v1 ++ v2) (place_rfn rt1' * place_rfn rt2')%type _ (ProdLty lt1' lt2' sl) (PlaceIn (r1', r2')) (pair_t ty1 ty2 sl) (PlaceIn r1t, PlaceIn r2t)))) -∗
    typed_read_end E L π l (place_rfn rt1 * place_rfn rt2) (ProdLty lt1 lt2 sl) (PlaceIn (r1, r2)) b2 bmin ot T.
  Proof.
  Admitted.
  Global Instance type_read_prod_inst E L π {rt1 rt2} `{ghost_varG Σ rt1} `{ghost_varG Σ rt2} `{ghost_varG Σ ((place_rfn rt1) * (place_rfn rt2))} b2 bmin l (lt1 : lty rt1) (lt2: lty rt2) r1 r2 sl ot :
    TypedReadEnd E L π l (ProdLty lt1 lt2 sl) (PlaceIn (r1, r2)) b2 bmin ot | 10 :=
    λ T, i2p (type_read_prod E L π b2 bmin l lt1 lt2 r1 r2 sl ot T).

  (** We can do copy reads from shr-blocked places *)
  Lemma type_read_shr_blocked_copy E L π {rt} `{ghost_varG Σ rt} b2 bmin l (ty : type rt) r κ ot `{!Copyable ty} (T : val → ∀ rt', ghost_varG Σ rt' → lty rt' → place_rfn rt' → type rt → rt → iProp _) :
    (⌜ty.(ty_has_op_type) ot⌝ ∗ ⌜lctx_lft_alive E L κ⌝ ∗ (∀ v, T v rt _ (ShrBlockedLty ty κ) (PlaceIn r) ty r)) -∗
    typed_read_end E L π l rt (ShrBlockedLty ty κ) (PlaceIn r) b2 bmin ot T.
  Proof.
  Admitted.
  Global Instance type_read_shr_blocked_copy_inst E L π {rt} `{ghost_varG Σ rt} b2 bmin l (ty : type rt) r κ ot `{!Copyable ty} :
    TypedReadEnd E L π l (ShrBlockedLty ty κ) (PlaceIn r) b2 bmin ot | 10 :=
    λ T, i2p (type_read_shr_blocked_copy E L π b2 bmin l ty r κ ot T).
  *)



  (* TODO: potentially lemmas for reading from mut-ref and box ltypes.
      (this would be required for full generality, because shr_blocked can be below them)
   *)

  Lemma type_write E L T T' e ot v rt (ty : type rt) r π :
    IntoPlaceCtx E e T' →
    T' L (λ L' K l, find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π')),
      ⌜π' = π⌝ ∗
      typed_place π E L' l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) (bmin : place_update_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto bmin UpdStrong),
        (* unblock etc. TODO: this requirement is too strong. *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (* certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (* end writing *)
        typed_write_end π E L2 ot v ty r b2 bmin l2 lt3 ri3 (λ L3 (rt3' : RT) (ty3 : type rt3') (r3 : rt3') upd2,
        typed_place_finish π E L3 updcx (place_update_kind_res_trans upd upd2) (R ∗ llft_elt_toks κs) l b (◁ ty3)%I (#r3) T))))))
    ⊢ typed_write π E L e ot v ty r T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL HΦ".
    iApply (HT' with "CTX HE HL HT'").
    iIntros (L' K l) "HL". iDestruct 1 as ([rt1 ([[ty1 r1] π'] & ?)]) "(Hl & -> & HP)".
    iApply ("HP" with "[//] [//] CTX HE HL Hl").
    iIntros (L'' κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ"). iIntros "Hv".
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L2 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iModIntro. iApply (logical_step_wand with "Hl2").
    iIntros "(Hl2 & HR)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl2 & Hcond & %Hst_eq & HT)".
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl2 Hv") as "Hwrite".
    iDestruct "Hwrite" as "(% & Hl2 & Hcl)".
    iModIntro. iFrame "Hl2". iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl Hl2".
    iMod ("Hcl" with "Hl2") as "Hcl".
    iDestruct "Hcl" as "(%L3 & %rt3 & %ty3 & %r3 & %res & HL & Hl2 & %Hsteq & #Hincl2' & Hcond2 & Hfin)".

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd res) (◁ ty3)%I (#r3)).

    iMod ("Hs" $! upd_inner with "[] Hl2 [] [] [Hcond Hcond2]") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. rewrite Hst_eq Hsteq. simp_ltypes. done. }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }
    iMod ("Hs" with "HL Hfin") as (upd') "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & Hfin)".
    iPoseProof ("Hfin" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _. iFrame.
  Qed.

  (* TODO: generalize to other places where we can overwrite, but which can't be folded to an ofty *)

  (** Currently have [ty2], want to write [ty]. This allows updates of the refinement type (from rt to rt2).
     This only works if the path is fully owned ([bmin = Owned _]).
     We could in principle allow this also for Uniq paths by suspending the mutable reference's contract with [OpenedLtype], but currently we have decided against that. *)
  (* TODO the syntype equality requirement currently is too strong: it does not allow us to go from UntypedSynType to "proper sy types".
    more broadly, this is a symptom of our language not understanding about syntypes.
  *)
  Lemma type_write_ofty_strong E L {rt rt2} π l (ty : type rt) (ty2 : type rt2) `{Hg : !TyGhostDrop ty2} r1 (r2 : rt2) v ot wl (T : typed_write_end_cont_t UpdStrong rt2) :
    (⌜ty_has_op_type ty ot MCNone⌝ ∗ ⌜ty_syn_type ty = ty_syn_type ty2⌝ ∗
        (ty_ghost_drop_for ty2 Hg π r2 -∗ T L rt ty r1 (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)))
    ⊢ typed_write_end π E L ot v ty r1 (Owned wl) UpdStrong l (◁ ty2) (#r2) T.
  Proof.
    iIntros "(%Hot & %Hst_eq & HT)".
    iIntros (F qL ???) "#CTX #HE HL Hl Hv".
    iPoseProof (ofty_ltype_acc_owned with "Hl") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v0 & Hl0 & Hv0 & Hcl))"; first done.
    set (upd_strong := (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)).

    iDestruct (ty_own_val_has_layout with "Hv0") as "%Hlyv0"; first done.
    iDestruct (ty_has_layout with "Hv") as "#(%ly' & % & %Hlyv)".
    assert (ly' = ly) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite Hst_eq. }
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iSplitR; first done.
    iSplitL "Hl0".
    { iExists v0. iFrame. iSplitR; first done. done. }
    iPoseProof (ty_own_ghost_drop _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
    iApply (logical_step_compose with "Hcl").
    iApply (logical_step_compose with "Hgdrop").
    iApply logical_step_intro.
    iIntros "Hgdrop Hcl Hl".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc'".
    iMod ("Hcl" with "Hl [//] Hsc' Hv") as "Hl".
    iExists _, rt, ty, r1, upd_strong. iFrame.
    iSplitR. { done. }
    iR. iR.
    iApply ("HT" with "Hgdrop").
  Qed.
  Definition type_write_ofty_strong_inst := [instance @type_write_ofty_strong].
  Global Existing Instance type_write_ofty_strong_inst | 10.

  (** This does not allow updates to the refinement type, rt stays the same. *)
  (* TODO: also allow writes here if the place is not an ofty *)
  (* Write v : r1 @ ty to l : #r2 @ ◁ ty2.
     We first need to show that ty is a subtype of ty2 (in order to handl e
     Afterwards, we obtain l : #r3 @ ◁ ty2 for some r3, as well as the result of ghost-dropping r2 @ ty2. *)
  Lemma type_write_ofty_weak E L {rt} π b2 bmin l (ty ty2 : type rt) `{Hg : !TyGhostDrop ty2} r1 r2 v ot (T : typed_write_end_cont_t bmin rt) :
    (∃ r3, owned_subtype π E L false r1 r3 ty ty2 (λ L2,
      ⌜ty_syn_type ty = ty_syn_type ty2⌝ ∗ (* TODO: would be nice to remove this requirement *)
      ⌜ty_has_op_type ty ot MCNone⌝ ∗ ⌜lctx_bor_kind_alive E L2 b2⌝ ∗
      ⌜bor_kind_writeable b2⌝ ∗
      (ty_ghost_drop_for ty2 Hg π r2 -∗
        T L2 rt ty2 r3 (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl))))
    ⊢ typed_write_end π E L ot v ty r1 b2 bmin l (◁ ty2) (#r2) T.
  Proof.
    iIntros "(%r3 & HT)".
    iIntros (F qL ???) "#CTX #HE HL Hl Hv".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & Hsub & HL & %Hst_eq & %Hot & %Hal & %Hwriteable & HT)".
    iDestruct ("Hsub") as "(#%Hly_eq & _ & Hsub)".
    iPoseProof ("Hsub" with "Hv") as "Hv".

    set (weak_upd := (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)).

    destruct b2 as [ wl | | ]; simpl.
    - iPoseProof (ofty_ltype_acc_owned with "Hl") as "(%ly & %Halg & %Hly & #Hsc & _ & >(%v0 & Hl & Hv0 & Hcl))"; first done.
      iDestruct (ty_own_val_has_layout with "Hv0") as "%"; first done.
      iDestruct (ty_has_layout with "Hv") as "(%ly'' & % & %)".
      assert (ly'' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      specialize (ty_op_type_stable Hot) as ?.
      assert (ly = ot_layout ot) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite -Hst_eq. }
      iModIntro. iSplitR; first done. iSplitL "Hl".
      { iExists v0. iFrame. done. }
      iPoseProof (ty_own_ghost_drop _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hgdrop").
      iApply logical_step_intro. iIntros "Hgdrop Hcl Hl".
      (*iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc'".*)
      iMod ("Hcl" with "Hl [] [] Hv") as "Hl"; [done.. | ].
      iModIntro.
      iExists _, _, ty2, r3, weak_upd.
      iFrame.
      iR.
      iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      iApply ("HT" with "Hgdrop").
    - (* Shared, so it can't be writeable *)
      done.
    - simpl in Hal.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as "(%q & Htok & Htok_cl)"; first done.
      iPoseProof (ofty_ltype_acc_uniq lftE with "CTX Htok Htok_cl Hl") as "(%ly & %Halg & %Hly & Hlb & >Hb)"; first done.
      iMod "HF_cl" as "_".
      iDestruct "Hb" as "(%v0 & Hl & Hv0 & Hcl)".
      iDestruct (ty_own_val_has_layout with "Hv0") as "%"; first done.
      iDestruct (ty_has_layout with "Hv") as "(%ly'' & % & %)".
      assert (ly'' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      specialize (ty_op_type_stable  Hot) as ?.
      assert (ly = ot_layout ot) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite -Hst_eq. }
      iModIntro. iSplitR; first done. iSplitL "Hl".
      { iExists v0. iFrame. done. }
      iPoseProof (ty_own_ghost_drop _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
      iApply (logical_step_compose with "Hgdrop").
      iApply (logical_step_mask_mono lftE); first done.
      iApply (logical_step_compose with "Hcl").
      iApply logical_step_intro. iIntros "[Hcl _] Hgdrop Hl".
      iMod (fupd_mask_mono with "(Hcl Hl Hv)") as "(Hl & HL)"; [done.. | ].
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro.
      iExists _, _, ty2, r3, weak_upd. iFrame.
      iR.
      iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      iApply ("HT" with "Hgdrop").
  Qed.
  Definition type_write_ofty_weak_inst := [instance @type_write_ofty_weak].
  Global Existing Instance type_write_ofty_weak_inst | 20.

  (* TODO move *)
  (*
  Fixpoint try_fold_lty {rt} (lt : lty rt) : option (type rt) :=
    match lt with
    | BlockedLty _ _ => None
    | ShrBlockedLty _ _ => None
    | OfTy ty => Some ty
    | MutLty lt κ =>
        ty ← try_fold_lty lt;
        Some (mut_ref ty κ)
    | ShrLty lt κ =>
        (* TODO *)
        (*ty ← try_fold_lty lt;*)
        (*Some (shr_ref ty κ)*)
        None
    | BoxLty lt =>
        (* TODO *)
        (*ty ← try_fold_lty lt;*)
        (*Some (box ty)*)
        None
    | ProdLty lt1 lt2 sl =>
        ty1 ← try_fold_lty lt1;
        ty2 ← try_fold_lty lt2;
        if decide (sl = pair_layout_spec ty1 ty2) then Some (pair_t ty1 ty2) else None
    end.
  Lemma try_fold_lty_correct {rt} (lt : lty rt) (ty : type rt) :
    try_fold_lty lt = Some ty →
    ⊢ ltype_eq lt (◁ ty)%I.
  Proof.
  Abort.

  (* The following lemmas are really somewhat awkward, because of the whole "pushing down" thing: we are really overwriting the MutLty(etc.) here, not its contents. But still, we need to replicate these lemmas that are really similar, because we can't phrase the ownership generically. *)

  (* Basically for Uniq ownership. We need to take care that we are not disrupting the contract of the mutable reference that may be above it (in the b2=Uniq case). *)
  Lemma type_write_mutlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt * gname)) (lt2 : lty rt) r1 r2 v κ ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (MutLty lt2 κ)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (MutLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_mutlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v κ wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (MutLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.

  (* Same lemmas for box *)
  Lemma type_write_boxlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt)) (lt2 : lty rt) r1 r2 v ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (BoxLty lt2)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (BoxLty lt2) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_boxlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (BoxLty lt2) (PlaceIn r2) T.
  Proof.
  Abort.

  (* Same for sharing. This works, again, because we are writing to the place the shared reference is stored in, not below the shared reference. *)
  Lemma type_write_shrlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt)) (lt2 : lty rt) r1 r2 v κ ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (ShrLty lt2 κ)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (ShrLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_shrlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v κ wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (ShrLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
   *)

  (* TODO: product typing rule.
    This will be a bit more complicated, as we essentially need to require that directly below the product, nothing is blocked.
    Of course, with nested products, this gets more complicated...
   *)

  Lemma opt_place_update_eq_strong {rt1 rt2} bmin (Heq : bmin = UpdStrong) :
    opt_place_update_eq bmin rt1 rt2.
  Proof.
    unfold opt_place_update_eq.
    rewrite Heq.
    exact I.
  Defined.

  Lemma type_addr_of_mut E L (e : expr) (T : typed_addr_of_mut_cont_t) T' :
    IntoPlaceCtx E e T' →
    T' L (λ L1 K l, find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      (* place *)
      typed_place π E L1 l lt1 r1 UpdStrong b K (λ L2 κs (l2 : loc) (b2 : bor_kind) (bmin : place_update_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) updcx,
        (* We need to be able to do a strong update *)
        ∃ (Heqmin : bmin = UpdStrong),
        typed_addr_of_mut_end π E L2 l2 lt2 ri2 b2 UpdStrong (λ L3 rtb tyb rb rt' lt' r',
          typed_place_finish π E L3 updcx (mkPUKRes UpdStrong I (opt_place_update_eq_strong bmin Heqmin)) (llft_elt_toks κs) l b lt' r' (λ L4,
            (* in case lt2 is already an AliasLtype, the simplify_hyp instance for it will make sure that we don't actually introduce that assignment into the context *)
            l2 ◁ₗ[π, Owned false] ri2 @ lt2 -∗
            T L4 π l2 rtb tyb rb)))))
    ⊢ typed_addr_of_mut E L e T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL HΦ".
    iApply (HT' with "CTX HE HL HT'").
    iIntros (L1 K l) "HL". iDestruct 1 as ([rto [[[lt1 r1] b] π]]) "(Hl & Hplace)" => /=.
    iApply ("Hplace" with "[//] [//] CTX HE HL Hl").
    iIntros (L2 κs l2 bmin b2 rti ltyi ri updcx) "Hl2 Hs (%Heqmin & Hcont) HL".
    iApply "HΦ".
    iApply logical_step_fupd.
    iSpecialize ("Hcont" with "[//] [//] [//] CTX HE HL Hl2").

    iApply (logical_step_wand with "Hcont").
    iDestruct 1 as (L3 rtb tyb rb rt' lt' r') "(Htyb & Hl2 & Hl2' & %Hst & HL & HT)".

    set (upd_strong := (mkPUKRes UpdStrong I (opt_place_update_eq_strong bmin Heqmin))).
    set (upd_inner := typed_place_finish_upd upd_strong lt' r').
    iMod ("Hs" $! upd_inner with "[] Hl2 [] [$] [$]") as "Hs".
    { simpl. by rewrite Heqmin. }
    { simpl. done. }
    iMod ("Hs" with "HL HT") as (upd') "(Hl & %Hsteq & Hcond & ? & ? & ? & HL & HT)".
    iDestruct ("HT" with "Hl") as "HT".
    iMod ("HT" with "[//] HE HL [$]") as "(%L4 & HL & HT)".
    iModIntro.
    iExists L4, _, _, tyb, rb. iFrame.
    by iApply "HT".
  Qed.
  (* NOTE: instances for [typed_addr_of_mut_end] are in alias_ptr.v *)

  (** Top-level rule for creating a mutable borrow *)
  Lemma type_borrow_mut E L T T' e κ (orty : option rust_type) :
    (** Decompose the expression *)
    IntoPlaceCtx E e T' →
    T' L (λ L1 K l,
      (** Find the type assignment in the context *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      (** Check the place access *)
      typed_place π E L1 l lt1 r1 UpdStrong b K (λ L2 κs (l2 : loc) (b2 : bor_kind) (bmin : place_update_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) updcx,
        (* We need to be able to borrow at least at [κ] *)
        ⌜lctx_place_update_kind_outlives E L2 bmin [κ]⌝ ∗
        (** Omitted from paper: find the credit context to give the borrow-step a time receipt *)
        find_in_context (FindCreditStore) (λ '(n, m),
        (** Stratify *)
        stratify_ltype_unblock π E L2 StratRefoldFull l2 lt2 ri2 b2 (λ L3 R rt2' lt2' ri2',
        (** Omitted from paper: Certify that this stratification is allowed *)
        prove_place_cond E L3 bmin lt2 lt2' (λ upd,
        (** finish borrow *)
        typed_borrow_mut_end π E L3 κ l2 orty lt2' ri2' b2 bmin (λ (γ : gname) rt3 (lt3 : ltype rt3) (r3 : place_rfn rt3) ty4 r4 upd',
        (** return the credit store *)
        credit_store n m -∗
        typed_place_finish π E L3 updcx (place_update_kind_res_trans upd upd') (R ∗ llft_elt_toks κs) l b
          lt3 r3 (λ L4, T L4 π (val_of_loc l2) γ rt3 ty4 r4))))))))
    ⊢ typed_borrow_mut E L e κ orty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL HΦ".
    iApply (HT' with "CTX HE HL HT'").
    iIntros (L1 K l) "HL". iDestruct 1 as ([rt1 [[[ty1 r1] ?] π]]) "[Hl HP]".
    iApply ("HP" $! _ F with "[//] [//] CTX HE HL Hl").
    iIntros (L2 κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL2".
    iDestruct "HT" as "(%Houtl & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL2") as "#Houtl".
    { apply Houtl. }

    iDestruct "HT" as ([n m]) "(Hstore & HT)".
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hstore)".
    (* bring the place type in the right shape *)
    iApply ("HΦ" with "Hat").
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL2 Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L3 & %R & %rt' & %lt' & %r' & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & %Hsteq & HT)".

    iApply (logical_step_wand with "Hl2").
    iIntros "!> (Hl2 & HR) !> Hcred Hat".
    iPoseProof ("Hstore" with "Hat") as "Hstore".
    iPoseProof (ltype_own_has_layout with "Hl2") as "(%ly & %Halg & %Hly)".

    iMod ("HT" $! F with "[//] [//] [//] CTX HE HL Hl2 Hcred") as "Hbor".
    iDestruct "Hbor" as (γ ly' rt2 ty2 r2 upd') "(Hobs & Hbor & Hsc & %Halg' & Hlb & Hblock & #Hincl2 & Hcond' & %Hst_eq & HL & HT)".
    iSpecialize ("HT" with "Hstore").
    assert (ly' = ly) as ->. { move: Hst_eq Halg' Halg. simp_ltypes => -> ??. by eapply syn_type_has_layout_inj. }

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd upd') (BlockedLtype ty2 κ)%I (👻 γ)).

    iMod ("Hs" $! upd_inner with "[] Hblock [] [] [Hcond Hcond']") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. iPureIntro. simp_ltypes. rewrite Hsteq Hst_eq//.  }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }
    iMod ("Hs" with "HL HT") as (upd'') "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & HT)".
    iPoseProof ("HT" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _. iFrame.
    iL. done.
  Qed.


  (* Problem:
    - mutrefs will now allow UpdStrong.
      But we still don't want to allow this, because we don't really want to open the mutref above.

      Maybe I want another level that isn't semantically different from UpdStrong, but still signifies that we shouldn't do tis.

    Maybe I should have another flag that has no semantic meaning but is purely a heuristic.
    Depending on that flag I can then decide what to actually do.

    Or I dont' emit a typing hint in the frontend if it's below a reference.

   *)

  (** Finish a mutable borrow *)
  Lemma type_borrow_mut_end_owned E L π κ l orty (rt : RT) (ty : type rt) (r : rt) wl bmin (T : typed_borrow_mut_end_cont_t bmin rt) :
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    (** The lifetime at which we borrow still needs to be alive *)
    ⌜lctx_lft_alive E L κ⌝ ∗
    (* Interpret the typing hint *)
    interpret_typing_hint E L orty bmin ty r (λ rt' ty' r' upd,
      (** Then, the place becomes blocked *)
      (∀ γ, T γ rt' (BlockedLtype ty' κ) (PlaceGhost γ) ty' r'
        (place_update_kind_res_trans upd (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl))))
    ⊢ typed_borrow_mut_end π E L κ l orty (◁ ty) (#r) (Owned wl) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hl Hcred".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl1"; first apply Hincl.

    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%rt2 & %ty2 & %r2 & %upd & HL & #Hincl2 & #Hcond1 & #Hincl3 & HT)".
    iPoseProof (type_ltype_incl_owned_in _ _ wl with "Hincl2") as "Hincl2'".
    iMod (ltype_incl_use with "Hincl2' Hl") as "Hl"; first done.

    set (upd1 := (mkPUKRes (allowed:=bmin)(rt1:=rt2) (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)).

    (* owned *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcreda & (%r' & Hrfn & Hb))".
    iDestruct "Hrfn" as "<-".
    iDestruct "CTX" as "(LFT & TIME & LLFT)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_m"; first done.
    iMod (gvar_alloc r2) as (γ) "[Hauth Hobs]".
    iMod (bor_create lftE κ (∃ r' : rt2, gvar_auth γ r' ∗ |={lftE}=> l ↦: ty2.(ty_own_val) π r') with "LFT [Hauth Hb]") as "[Hb Hinh]"; first solve_ndisj.
    { iPoseProof (maybe_later_mono with "Hb") as "Hb". iNext. eauto with iFrame. }
    iMod "Hcl_m" as "_".
    iModIntro. iExists γ, ly, rt2, ty2, r2, _.
    iSpecialize ("HT" $! γ).
    iFrame "Hb HL Hlb Hsc HT".
    iSplitL "Hobs".
    { done. }
    iSplitR; first done.
    iSplitL "Hinh Hcred Hcreda".
    { rewrite ltype_own_blocked_unfold /blocked_lty_own.
      iExists ly. iSplitR; first done. iSplitR; first done. iSplitR; first done.
      iFrame "Hlb Hcreda". iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
      iIntros "Hdead". iMod ("Hinh" with "Hdead") as "Hinh".
      iApply (lc_fupd_add_later with "Hcred1").
      iNext. done. }
    iSplitR. { simpl. iApply place_update_kind_incl_lub; done. }
    iSplitL. {
      simpl. iApply typed_place_cond_trans.
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last iApply ofty_blocked_place_cond; last iApply place_update_kind_incl_refl.
      iApply place_update_kind_max_incl_r. }
    iPoseProof (ltype_incl_syn_type with "Hincl2'") as "->".
    by simp_ltypes.
  Qed.
  Definition type_borrow_mut_end_owned_inst := [instance @type_borrow_mut_end_owned].
  Global Existing Instance type_borrow_mut_end_owned_inst | 20.

  (* NOTE: this can't use typing hints right now, as [interpret_typing_hint] only shows inclusion, not equality *)
  Lemma type_borrow_mut_end_uniq E L π κ l orty (rt : RT) (ty : type rt) (r : rt) κ' γ bmin (T : typed_borrow_mut_end_cont_t bmin rt) :
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    ⌜lctx_lft_incl E L κ κ'⌝ ∗
    (** The lifetime at which we borrow still needs to be alive *)
    ⌜lctx_lft_alive E L κ⌝ ∗
    (** Then, the place becomes blocked *)
    (∀ γ, T γ rt (BlockedLtype ty κ) (PlaceGhost γ) ty r (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl))
    ⊢ typed_borrow_mut_end π E L κ l orty (◁ ty) (#r) (Uniq κ' γ) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hincl2 & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hl Hcred".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl1"; first apply Hincl.
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1'"; first apply Hincl2.
    (* mutable bor: reborrow *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcreda & Hrfn & Hb)".

    iDestruct "CTX" as "(LFT & TIME & LLFT)".
    iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    iMod (pinned_bor_rebor_full _ _ κ with "LFT [] [Hcred1 Hcred2] Hb") as "(Hb & Hcl_b)"; [done | | | ].
    { done. }
    { iEval (rewrite lc_succ). iFrame. }

    simpl.
    iMod (gvar_alloc r) as (γ') "[Hauth' Hobs']".

    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (Hal with "HE HL") as "(%q' & Htok & Htok_cl)"; first done.

    (* put in the refinement *)
    iMod (bor_create lftE κ (∃ r', gvar_obs γ r' ∗ gvar_auth γ' r') with "LFT [Hrfn Hauth']") as "(Hrfn & Hcl_rfn)"; first done.
    { iNext. iExists _. iFrame. }
    iMod (bor_combine with "LFT Hb Hrfn") as "Hb"; first done.

    iMod (bor_acc_cons with "LFT Hb Htok") as "(Hb & Hcl_b')"; first done.
    iDestruct "Hb" as "((%r1 & >Hauth1 & Hb1) & (%r2 & >Hobs1 & >Hauth2))".
    iPoseProof (gvar_agree with "Hauth2 Hobs'") as "->".
    iPoseProof (gvar_agree with "Hauth1 Hobs1") as "->".
    set (bor' := ((∃ r' : rt, gvar_auth γ' r' ∗ (|={lftE}=> l ↦: ty_own_val ty π r')))%I).
    iMod ("Hcl_b'" $! bor' with "[Hobs1 Hauth1] [Hauth2 Hb1]") as "(Ha & Htok)".
    { iNext. iIntros "Ha".
      iDestruct "Ha" as "(%r'' & Hauth & Ha)".
      iMod (gvar_update r'' with "Hauth1 Hobs1") as "(Hauth1 & Hobs1)".
      iModIntro. iNext. iSplitL "Ha Hauth1"; eauto with iFrame. }
    { iNext. iExists _. iFrame. }
    iMod ("Htok_cl" with "Htok") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    iMod "Hcl_F" as "_".
    iModIntro. iExists γ', _. iSpecialize ("HT" $! γ').
    iFrame.
    iR. iR. iR.
    (* we've got some leftover credits here *)
    iSplitL "Hcl_b Hcl_rfn Hcreda".
    { rewrite ltype_own_blocked_unfold /blocked_lty_own.
      iExists _. iR. iR. iR. iR.
      iDestruct "Hcreda" as "($ & $)".
      iIntros "#Hdead". iMod ("Hcl_b" with "Hdead") as "$".
      iMod ("Hcl_rfn" with "Hdead") as "Hrfn".
      iDestruct "Hrfn" as "(%r'' & >Hobs & >Hauth)".
      iMod (gvar_obs_persist with "Hauth") as "Hauth".
      iModIntro. iExists _, _. iFrame. done. }
    iR. iL.
    iApply ofty_blocked_place_cond.
    iApply place_update_kind_incl_refl.
  Qed.
  Definition type_borrow_mut_end_uniq_inst := [instance @type_borrow_mut_end_uniq].
  Global Existing Instance type_borrow_mut_end_uniq_inst | 20.

  (* Low-priority default instance to fold to [OfTy] *)
  Lemma typed_borrow_mut_end_fold π E L κ l orty {rt} (lt : ltype rt) r b bmin T :
    cast_ltype_to_type E L lt (λ ty,
      typed_borrow_mut_end π E L κ l orty (◁ ty) r b bmin T)
    ⊢ typed_borrow_mut_end π E L κ l orty lt r b bmin T.
  Proof.
    unfold cast_ltype_to_type, typed_borrow_mut_end.
    iIntros "(%ty & %Heqt & HT)".
    iIntros (????) "#CTX #HE HL Hl Hcred".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; [apply Heqt | ].
    iDestruct ("Hincl" $! _ _) as "(Hincl1 & _)".
    iPoseProof (ltype_incl_syn_type with "Hincl1") as "%Hst0".
    iMod (ltype_incl_use with "Hincl1 Hl") as "Hl"; first done.
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl Hcred") as "(%γ & %ly & % & %ty2 & % & %res & Hrfn & ? & ? & %Hst & ? & hl & ? & Hcond & %Hst' & HL & HT)".
    iFrame. iR.
    rewrite -Hst' -Hst0. iL.
    iApply (ltype_eq_place_cond_trans with "[//] Hcond").
  Qed.
  Definition typed_borrow_mut_end_fold_inst := [instance @typed_borrow_mut_end_fold].
  Global Existing Instance typed_borrow_mut_end_fold_inst | 1000.

  Lemma type_borrow_shr E L T T' e κ orty :
    IntoPlaceCtx E e T' →
    T' L (λ L1 K l, find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      (* place *)
      typed_place π E L1 l lt1 r1 UpdStrong b K (λ L2 κs (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) updcx,
      (* stratify *)
      stratify_ltype_unblock π E L2 StratRefoldOpened l2 lt2 ri2 b2 (λ L3 R rt2' lt2' ri2',
      (* certify that this stratification is allowed, or otherwise commit to a strong update *)
      prove_place_cond E L3 bmin lt2 lt2' (λ upd,
      (* finish borrow *)
      typed_borrow_shr_end π E L3 κ l2 orty lt2' ri2' b2 bmin (λ rt3 (lt3 : ltype rt3) (r3 : place_rfn rt3) (ty4 : type rt3) r4 upd',
      (* return toks *)
      typed_place_finish π E L3 updcx (place_update_kind_res_trans upd upd') (R ∗ llft_elt_toks κs) l b lt3 r3
        (λ L4, T L4 π (val_of_loc l2) rt3 ty4 (#r4))))))))
    ⊢ typed_borrow_shr E L e κ orty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL HΦ".
    iApply (HT' with "CTX HE HL HT'").
    iIntros (L1 K l) "HL". iDestruct 1 as ([rt1 [[[ty1 r1] ?] π]]) "[Hl HP]".
    iApply ("HP" $! _ F with "[//] [//] CTX HE HL Hl").
    iIntros (L2 κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL".
    (* bring the place type in the right shape *)
    iApply ("HΦ").
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step.
    iMod "Hb" as "(%L3 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl2 & Hcond & %Hsteq & HT)".
    (* needs two logical steps: one for stratification and one for initiating sharing.
       - that means: creating a reference will now be two skips.
       - this shouldn't be very problematic. *)
    iApply (logical_step_wand with "Hl2").
    iIntros "!>(Hl2 & HR)".
    iApply fupd_logical_step.
    iPoseProof (ltype_own_has_layout with "Hl2") as "(%ly & %Halg & %Hly)".

    iPoseProof ("HT" $! F with "[//] [//] [//] [//] CTX HE HL Hl2") as ">Hb".
    iModIntro. iApply logical_step_fupd. iApply (logical_step_wand with "Hb").
    iIntros "Ha !> Hcred".
    iMod ("Ha" with "Hcred") as "(%ly' & %rt2 & %lt2 & %r2 & %ty3 & %upd' & HT)".
    iDestruct "HT" as "(Hshr & %Halg' & Hlb & Hsc & Hblocked & Hcond' & %Hsteq1 & %Hsteq2 & #Hincl & HL & HT)".
    assert (ly' = ly) as ->. {
      move: Halg' Halg.
      rewrite -Hsteq2.
      by eapply syn_type_has_layout_inj. }
    (*iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heq.*)

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd upd') lt2 (#r2)).

    iMod ("Hs" $! upd_inner with "[] Hblocked [] [] [Hcond Hcond']") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. rewrite Hsteq Hsteq1//. }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }

    iMod ("Hs" with "HL HT") as (?) "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & HT)".
    iPoseProof ("HT" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _. iFrame.
    iL. done.
  Qed.

  Lemma type_borrow_shr_end_owned E L π κ l orty {rt : RT} (ty : type rt) (r : rt) bmin wl (T : typed_borrow_shr_end_cont_t bmin rt):
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜Forall (lctx_lft_alive E L) (ty_lfts ty)⌝ ∗
    (T rt (ShrBlockedLtype ty κ) (#r) ty r (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl))
    ⊢ typed_borrow_shr_end π E L κ l orty (◁ ty) (#r) (Owned wl) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hal & %Hal' & HT)".
    iIntros (F ????) "#[LFT TIME] #HE HL Hl".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iMod (lctx_lft_alive_tok_noend (κ ⊓ (lft_intersect_list (ty_lfts ty))) with "HE HL") as "Ha"; first done.
    { eapply lctx_lft_alive_intersect; first done. by eapply lctx_lft_alive_intersect_list. }
    iDestruct "Ha" as "(%q' & Htok & HL & Hcl_L')".
    (* owned *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & %r' & Hrfn & Hl)".
    iMod (maybe_use_credit with "Hcred Hl") as "(Hcred & Hat & (%v & Hl & Hv))"; first done.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (bor_create lftE κ (∃ v, l ↦ v ∗ v ◁ᵥ{π} r' @ ty)%I with "LFT [Hv Hl]") as "(Hb & Hinh)"; first done.
    { eauto with iFrame. }
    iMod "Hcl_F" as "_".
    (*iPoseProof (place_rfn_interp_owned_share' with "Hrfn") as "#Hrfn'".*)
    rewrite ty_lfts_unfold.
    iPoseProof (ty_share _ F with "[$LFT $TIME] Htok [//] [//] Hlb Hb") as "Hshr"; first done.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hshr").
    iApply (logical_step_intro_maybe with "Hat").
    iModIntro. iIntros "Hcred' !> (#Hshr & Htok) !> Hcred1".
    iMod ("Hcl_L'" with "Htok HL") as "HL".
    iPoseProof ("Hcl_L" with "HL") as "HL".
    set (upd := (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)).
    iExists ly, rt, (ShrBlockedLtype ty κ), _, ty, upd.
    iFrame "Hshr Hlb Hsc HL". iSplitR; first done.
    iSplitL "Hcred' Hinh Hcred1".
    { iModIntro. rewrite ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iExists ly. iFrame "Hlb Hsc". iSplitR; first done. iSplitR; first done.
      iExists r'. iSplitR; first done. iFrame "Hshr Hcred'".
      iIntros "Hdead". iMod ("Hinh" with "Hdead"). iApply (lc_fupd_add_later with "Hcred1").
      iNext. eauto with iFrame. }
    iModIntro.
    iSplitR.
    { simpl. iExists eq_refl.
      simp_ltypes. iSplitR. { iIntros (??). iApply ltype_eq_refl. }
      iApply shr_blocked_imp_unblockable.
    }
    simp_ltypes. iR. iR. iR.
    iDestruct "Hrfn" as "->".
    iApply "HT".
  Qed.
  Definition type_borrow_shr_end_owned_inst := [instance @type_borrow_shr_end_owned].
  Global Existing Instance type_borrow_shr_end_owned_inst | 20.

  Lemma type_borrow_shr_end_uniq E L π κ l orty {rt : RT} (ty : type rt) (r : rt) bmin κ' γ (T : typed_borrow_shr_end_cont_t bmin rt):
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    ⌜lctx_lft_incl E L κ κ'⌝ ∗
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜Forall (lctx_lft_alive E L) (ty_lfts ty)⌝ ∗
    (T rt (ShrBlockedLtype ty κ) (#r) ty r (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl))
    ⊢ typed_borrow_shr_end π E L κ l orty (◁ ty) (#r) (Uniq κ' γ) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hincl2 & %Hal & %Hal' & HT)".
    (* basically, we do the same as for creating a mutable reference, but then proceed to do sharing *)
    iIntros (F ????) "#(LFT & TIME & LLCTX) #HE HL Hl".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hincl2.
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iMod (lctx_lft_alive_tok_noend (κ ⊓ (lft_intersect_list (ty_lfts ty))) with "HE HL") as "Ha"; first done.
    { eapply lctx_lft_alive_intersect; first done. by eapply lctx_lft_alive_intersect_list. }
    iDestruct "Ha" as "(%q' & Htok & HL & Hcl_L')".
    (* uniq *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & Hrfn & Hl)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hl".
    iDestruct "Hcred" as "((Hcred1 & Hcred2 & Hcred) & Hat)".
    iMod (pinned_bor_rebor_full _ _ κ with "LFT [] [Hcred1 Hcred2] Hl") as "(Hl & Hl_cl)"; first done.
    { done. }
    { iSplitL "Hcred1"; iFrame. }
    iMod "Hcl_F" as "_".

    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
    iMod (bor_exists_tok with "LFT Hl Htok1") as "(%r' & Hl & Htok1)"; first done.
    iMod (bor_sep with "LFT Hl") as "(Hauth & Hl)"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (bor_fupd_later with "LFT Hl Htok1") as "Ha"; [done.. | ].
    iApply (lc_fupd_add_later with "Hcred1").
    iNext. iMod ("Ha") as "(Hl & Htok1)".

    iMod (place_rfn_interp_mut_share' with "LFT Hrfn Hauth Htok1") as "(#Hrfn & Hmut & Hauth & Htok1)"; first done.
    iPoseProof (ty_share _ F with "[$LFT $TIME $LLCTX] [Htok1 Htok2] [] [] Hlb Hl") as "Hstep".
    { done. }
    { rewrite ty_lfts_unfold -lft_tok_sep. iFrame. }
    { done. }
    { done. }
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_atime with "Hat").
    iModIntro. iIntros "Hcred' Hat". iModIntro.
    iIntros "(#Hshr & Htok) Hcred1".
    iDestruct "Hrfn" as "<-".

    set (upd := (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)).
    iExists ly, rt, (ShrBlockedLtype ty κ), r, ty, upd. iFrame.
    iR. iR. iR.
    rewrite lft_tok_sep.
    rewrite ty_lfts_unfold.
    iMod ("Hcl_L'" with "Htok HL") as "HL".
    iPoseProof ("Hcl_L" with "HL") as "$".

    iDestruct "Hmut" as ">Hmut". iR.
    iSplitL "Hauth Hmut Hat Hcred' Hl_cl".
    { rewrite ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iExists ly. iR. iR. iR. iR. iExists _. iR.
      iFrame. done. }
    iSplitR.
    { iApply ofty_shr_blocked_place_cond. iApply place_update_kind_incl_refl. }
    iR. iR.
    done.
  Qed.
  Definition type_borrow_shr_end_uniq_inst := [instance @type_borrow_shr_end_uniq].
  Global Existing Instance type_borrow_shr_end_uniq_inst | 20.

  Lemma type_borrow_shr_end_shared E L π κ l orty {rt : RT} (ty : type rt) (r : rt) κ' bmin (T : typed_borrow_shr_end_cont_t bmin rt) :
    ⌜lctx_lft_incl E L κ κ'⌝ ∗
    (T rt (◁ ty) (#r) ty r (mkPUKRes UpdBot eq_refl opt_place_update_eq_refl))
    ⊢ typed_borrow_shr_end π E L κ l orty (◁ ty) (#r) (Shared κ') bmin T.
  Proof.
    simpl. iIntros "(%Hincl & HT)".
    iIntros (F ????) "#[LFT TIME] #HE HL #Hl".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl"; first apply Hincl.
    iModIntro. iApply logical_step_intro. iIntros "Hcred".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hsc & Hlb & %r' & Hrfn & #Hl)".
    iDestruct "Hl" as "-#Hl". iMod (fupd_mask_mono with "Hl") as "#Hl"; first done.
    set (upd := (mkPUKRes UpdBot eq_refl opt_place_update_eq_refl)).
    iExists ly, rt, (◁ ty)%I, r, ty, upd.
    iDestruct "Hrfn" as "<-".
    iPoseProof (ty_shr_mono with "Hincl Hl") as "$".
    iR. iFrame "Hlb Hsc". iModIntro.
    iSplitR. { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iR. iR. by iFrame "∗ #". }
    iFrame. iSplitR. { iApply typed_place_cond_refl_ofty. }
    iR. iR. iApply upd_bot_min.
  Qed.
  Definition type_borrow_shr_end_shared_inst := [instance @type_borrow_shr_end_shared].
  Global Existing Instance type_borrow_shr_end_shared_inst | 20.

  (* Low-priority default instance to fold to [OfTy] *)
  (* TODO: should have more specific instances for different ltypes, or a mechanism to extract a sharing predicate from an ltype *)
  Lemma typed_borrow_shr_end_fold π E L κ l orty {rt} (lt : ltype rt) r b bmin T :
    cast_ltype_to_type E L lt (λ ty,
      typed_borrow_shr_end π E L κ l orty (◁ ty) r b bmin T)
    ⊢ typed_borrow_shr_end π E L κ l orty lt r b bmin T.
  Proof.
    unfold cast_ltype_to_type, typed_borrow_shr_end.
    iIntros "(%ty & %Heqt & HT)".
    iIntros (?????) "#CTX #HE HL Hl".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; [apply Heqt | ].
    iDestruct ("Hincl" $! _ _) as "(Hincl1 & _)".
    iPoseProof (ltype_incl_syn_type with "Hincl1") as "%Hst0".
    iMod (ltype_incl_use with "Hincl1 Hl") as "Hl"; first done.
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl") as "Ha".
    iApply (logical_step_wand with "Ha").
    iModIntro. iIntros "HT Hcred".
    iMod ("HT" with "Hcred") as "(%ly & % & %lt2 & % & %ty2 & %res & Hl & %Hst1 & ? & ? & Hl' & Hcond & %Hst2 & %Hst3 & ? & HL & HT)".
    iFrame. iR.
    rewrite -Hst3 -Hst2 -Hst0. iL.
    iApply (ltype_eq_place_cond_trans with "[//] Hcond").
  Qed.
  Definition typed_borrow_shr_end_fold_inst := [instance @typed_borrow_shr_end_fold].
  Global Existing Instance typed_borrow_shr_end_fold_inst | 1000.

  (** statements *)
  Inductive CtxFoldExtract : Type :=
    | CtxFoldExtractAllInit (κ : lft)
    | CtxFoldExtractAll (κ : lft).

  Inductive CtxFoldResolve : Type :=
    | CtxFoldResolveAllInit
    | CtxFoldResolveAll.

  Inductive CtxFoldStratify : Type :=
    | CtxFoldStratifyAllInit
    | CtxFoldStratifyAll.

  Lemma type_goto E L b fn R s ϝ :
    fn.(rf_fn).(f_code) !! b = Some s →
    introduce_with_hooks E L (£ 1) (λ L2,
      typed_stmt E L2 s fn R ϝ)
    ⊢ typed_stmt E L (Goto b) fn R ϝ.
  Proof.
    iIntros (HQ) "Hs". iIntros (?) "#LFT #HE HL Hcont".
    iApply wps_goto => //.
    iModIntro. iIntros "Hcred".
    iMod ("Hs" with "[] HE HL Hcred") as "(%L2 & HL & HT)"; first done.
    by iApply ("HT" with "LFT HE HL").
  Qed.

  (** Goto a block if we have already proved it with a particular precondition [P]. *)
  (* This is not in Lithium goal shape, but that's fine since it is only manually applied by automation. *)
  (* We might also want to stratify here -- but this is difficult, because we'd need a second logical step.
     Instead, we currently insert an annotation for that in the frontend. *)
  Lemma type_goto_precond E L P b fn R ϝ :
    typed_block P b fn R ϝ ∗
    (* [true] so that we can deinitialize with [owned_subltype_step] *)
    prove_with_subtype E L true ProveDirect (P E L) (λ L' _ R,
      ⌜L = L'⌝ ∗ True (* TODO maybe relax and require inclusion of contexts or so. *))
    ⊢ typed_stmt E L (Goto b) fn R ϝ.
  Proof.
    iIntros "(Hblock & Hsubt)". iIntros (?) "#CTX #HE HL Hcont".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L' & % & %R2 & HP & HL & HT)"; [done.. | ].
    simpl.
    iDestruct ("HT") as "(<- & _)".
    iSpecialize ("Hblock" with "CTX HE HL [HP]").
    { iApply (logical_step_wand with "HP"). iIntros "($ & _)". }
    by iApply "Hblock".
  Qed.

  Lemma typed_block_rec fn R P b ϝ s :
    fn.(rf_fn).(f_code) !! b = Some s →
    (□ (∀ E L, (□ typed_block P b fn R ϝ) -∗
      introduce_with_hooks E L (P E L) (λ L2,
        typed_stmt E L2 s fn R ϝ)))
    ⊢ typed_block P b fn R ϝ.
  Proof.
    iIntros (Hs) "#Hb". iLöb as "IH".
    iIntros (? E L) "#CTX #HE HL HP Hcont".
    rewrite /logical_step.
    iMod "HP" as "(%n & Hat & HP)".
    iMod (persistent_time_receipt_0) as "Hpt".
    iApply (wps_goto_credits with "[] Hat Hpt") => //=.
    { iDestruct "CTX" as "(? & $ & ?)". }
    rewrite Nat.add_0_r.
    rewrite lc_succ. rewrite additive_time_receipt_succ.
    iMod (fupd_mask_subseteq ∅) as "Hcl"; first done.
    iModIntro.  iModIntro. iMod "Hcl" as "_". iModIntro.
    iIntros "(Hcred1 & Hcred) (_ & Hat)".
    iMod ("HP" with "Hcred Hat") as "HP".
    iMod ("Hb" with "IH [] HE HL HP") as "(%L2 & HL & Hs)"; first done.
    by iApply ("Hs" with "CTX HE HL").
  Qed.

  (** current goal: Goto.
     Instead of just jumping there, we can setup an invariant [P] on ownership and the lifetime contexts.
     Then instead prove: wp of the block, but in the context we can persistently assume the WP of the goto with the same invariant already. *)
  (* Note: these need to be manually applied. *)
  Lemma typed_goto_acc E L fn R P b ϝ s :
    fn.(rf_fn).(f_code) !! b = Some s →
    (* TODO maybe also stratify? *)
    prove_with_subtype E L true ProveDirect (P E L) (λ L' _ R2,
      ⌜L' = L⌝ ∗ (* TODO maybe relax if we have a separate condition on lifetime contexts *)
      (* gather up the remaining ownership *)
      accu (λ Q,
      (∀ E L, (□ typed_block (λ E L, P E L ∗ Q) b fn R ϝ) -∗
          introduce_with_hooks E L (P E L ∗ Q) (λ L2,
          typed_stmt E L2 s fn R ϝ))))
    ⊢ typed_stmt E L (Goto b) fn R ϝ.
  Proof.
    iIntros (Hlook) "Hsubt". iIntros (?) "#CTX #HE HL Hcont".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L' & % & %R2 & Hinv & HL & HT)"; [done.. | ].
    iDestruct ("HT") as "(-> & Hrec)".
    rewrite /accu.
    iDestruct "Hrec" as "(%Q & HQ & #Hrec)".
    iApply (typed_block_rec with "Hrec CTX HE HL [Hinv HQ]").
    - done.
    - iApply (logical_step_wand with "Hinv"). iIntros "(? & ?)". iFrame.
    - done.
  Qed.

  (* A variant where [P] is first instantiated with the refinement of some local variable *)
  Lemma typed_goto_acc' E L fn R b ϝ s {rt : RT} (l : loc) (P : RT_xt rt → elctx → llctx → iProp Σ) :
    fn.(rf_fn).(f_code) !! b = Some s →
    find_in_context (FindLoc l) (λ '(existT rt' (lt, r, bk, π)),
    l ◁ₗ[π, bk] r @ lt -∗
    ∃ (Heq : rt = rt') (r' : RT_xt rt), ⌜r = # $# (rew [RT_xt] Heq in r')⌝ ∗
    (* TODO maybe also stratify? *)
    prove_with_subtype E L true ProveDirect (P r' E L) (λ L' _ R2,
      ⌜L' = L⌝ ∗ (* TODO maybe relax if we have a separate condition on lifetime contexts *)
      (* gather up the remaining ownership *)
      accu (λ Q,
      (∀ E L, (□ typed_block (λ E L, P r' E L ∗ Q) b fn R ϝ) -∗
          introduce_with_hooks E L (P r' E L ∗ Q) (λ L2,
          typed_stmt E L2 s fn R ϝ)))))
    ⊢ typed_stmt E L (Goto b) fn R ϝ.
  Proof.
    iIntros (Hlook) "Hsubt". iIntros (?) "#CTX #HE HL Hcont".
    unfold FindLoc.
    iDestruct "Hsubt" as "(%x & Hlt & HT)". simpl in *.
    destruct x as [rt' (((lt & r) & ?) & ?)].
    iDestruct ("HT" with "Hlt") as "(%Heq & %r' & -> & Hsubt)".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L' & % & %R2 & Hinv & HL & HT)"; [done.. | ].
    iDestruct ("HT") as "(-> & Hrec)".
    rewrite /accu.
    iDestruct "Hrec" as "(%Q & HQ & #Hrec)".
    iApply (typed_block_rec with "Hrec CTX HE HL [Hinv HQ]").
    - done.
    - iApply (logical_step_wand with "Hinv"). iIntros "(? & ?)". iFrame.
    - done.
  Qed.

  Lemma type_assert E L e s fn R ϝ :
    typed_val_expr E L e (λ L' π v rt ty r, typed_assert π E L' v ty r s fn R ϝ)
    ⊢ typed_stmt E L (assert{BoolOp}: e; s) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hcont". wps_bind.
    iApply ("He" with "CTX HE HL"). iIntros (L' v π rt ty r) "HL Hv Hs".
    iDestruct ("Hs" with "CTX HE HL Hv") as (?) "(HL & Hs)".
    iApply wps_assert_bool; [done.. | ]. iIntros "!> Hcred". by iApply ("Hs" with "CTX HE HL").
  Qed.

  Lemma type_if E L e s1 s2 fn R join ϝ :
    typed_val_expr E L e (λ L' π v rt ty r, typed_if E L' v (v ◁ᵥ{π} r @ ty)
          (typed_stmt E L' s1 fn R ϝ) (typed_stmt E L' s2 fn R ϝ))
    ⊢ typed_stmt E L (if{BoolOp, join}: e then s1 else s2) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hcont". wps_bind.
    iApply ("He" with "CTX HE HL"). iIntros (L' v π rt ty r) "HL Hv Hs".
    iDestruct ("Hs" with "Hv") as "(%b & % & Hs)".
    iApply wps_if_bool; [done|..]. iIntros "!> Hcred". by destruct b; iApply ("Hs" with "CTX HE HL").
  Qed.

  Lemma type_switch E L it e m ss def fn R ϝ:
    typed_val_expr E L e (λ L' π v rt ty r, typed_switch π E L' v rt ty r it m ss def fn R ϝ)
    ⊢ typed_stmt E L (Switch it e m ss def) fn R ϝ.
  Proof.
    iIntros "He" (?) "#CTX #HE HL Hcont".
    have -> : (Switch it e m ss def) = (W.to_stmt (W.Switch it (W.Expr e) m (W.Stmt <$> ss) (W.Stmt def)))
      by rewrite /W.to_stmt/= -!list_fmap_compose list_fmap_id.
    iApply tac_wps_bind; first done.
    rewrite /W.to_expr /W.to_stmt /= -list_fmap_compose list_fmap_id.

    iApply ("He" with "CTX HE HL"). iIntros (L' v π rt ty r) "HL Hv Hs".
    iDestruct ("Hs" with "Hv") as (z Hn) "Hs".
    iAssert (⌜∀ i : nat, m !! z = Some i → is_Some (ss !! i)⌝%I) as %?. {
      iIntros (i ->). iDestruct "Hs" as (s ->) "_"; by eauto.
    }
    iApply wps_switch; [done|done|..]. iIntros "!> Hcred".
    destruct (m !! z) => /=.
    - iDestruct "Hs" as (s ->) "Hs". by iApply ("Hs" with "CTX HE HL").
    - by iApply ("Hs" with "CTX HE HL").
  Qed.

  Lemma type_exprs E L s e fn R ϝ :
    (typed_val_expr E L e (λ L' π v rt ty r, v ◁ᵥ{π} r @ ty -∗ typed_stmt E L' s fn R ϝ))
    ⊢ typed_stmt E L (ExprS e s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hcont". wps_bind.
    iApply ("Hs" with "CTX HE HL"). iIntros (L' π v rt ty r) "HL Hv Hs".
    iApply wps_exprs. iApply step_fupd_intro => //. iIntros "!> Hcred".
    by iApply ("Hs" with "Hv CTX HE HL").
  Qed.

  Lemma type_skips E L s fn R ϝ :
    (|={⊤}[∅]▷=> (£1 -∗ typed_stmt E L s fn R ϝ)) ⊢ typed_stmt E L (SkipS s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hcont".
    iApply wps_skip. iApply (step_fupd_wand with "Hs"). iIntros "Hs Hcred".
    by iApply ("Hs" with "Hcred CTX HE HL").
  Qed.

  Lemma type_skips' E L s fn R ϝ :
    typed_stmt E L s fn R ϝ ⊢ typed_stmt E L (SkipS s) fn R ϝ.
  Proof.
    iIntros "Hs". iApply type_skips. iApply step_fupd_intro; first done.
    iIntros "!> Hcred". done.
  Qed.

  Lemma typed_stmt_annot_skip {A} E L (a : A) s fn R ϝ :
    typed_stmt E L s fn R ϝ ⊢ typed_stmt E L (annot: a; s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hcont".
    iApply wps_annot. iApply step_fupd_intro; first done.
    iIntros "!> _". by iApply ("Hs" with "CTX HE HL").
  Qed.
  Lemma typed_stmt_annot_credits `{!typeGS Σ} E L {A} (a : A) s rf R ϝ n :
    atime n -∗
    (atime (S n) -∗ £ (S (num_laters_per_step n)) -∗ typed_stmt E L s rf R ϝ) -∗
    typed_stmt E L (annot: a; s) rf R ϝ.
  Proof.
    iIntros "Hat HT".
    iIntros (?) "#CTX #HE HL Hcont".
    iMod (persistent_time_receipt_0) as "Hp".
    iApply (derived.wps_annot_credits with "[] Hat Hp").
    { iDestruct "CTX" as "(_ & $ & _)". }
    iNext. iIntros "Hcred Hat".
    rewrite Nat.add_0_r.
    by iApply ("HT" with "Hat Hcred CTX HE HL").
  Qed.

  Lemma typed_expr_assert_type π E L n sty v {rt} (ty : type rt) r T :
    (∃ lfts, named_lfts lfts ∗
      (named_lfts lfts -∗ li_tactic (interpret_rust_type_goal lfts sty) (λ '(existT _ ty2),
        ∃ r2, subsume_full E L false (v ◁ᵥ{π} r @ ty) (v ◁ᵥ{π} r2 @ ty2) (λ L2 R2, R2 -∗ T L2 π v _ ty2 r2))))%I
    ⊢ typed_annot_expr E L n (AssertTypeAnnot sty) v (v ◁ᵥ{π} r @ ty) T.
  Proof.
    iIntros "(%lfts & Hnamed & HT)". iPoseProof ("HT" with "Hnamed") as "HT".
    rewrite /interpret_rust_type_goal. iDestruct "HT" as "(%rt2 & %ty2 & %r2 & HT)".
    iIntros "#CTX #HE HL Hv".
    iApply step_fupdN_intro; first done. iNext.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L2 & %R2 & >(Hv & HR2) & HL & HT)"; [done.. | ].
    iModIntro. iExists _, _, _, _, _. iFrame. by iApply ("HT" with "HR2").
  Qed.
  Global Instance typed_expr_assert_type_inst π E L n sty v {rt} (ty : type rt) r :
    TypedAnnotExpr E L n (AssertTypeAnnot sty) v (v ◁ᵥ{π} r @ ty) :=
    λ T, i2p (typed_expr_assert_type π E L n sty v ty r T).

  (** ** Handling of lifetime-related annotations *)
  (** Endlft triggers *)
  (** Instance for returning lifetime tokens [Inherit κ1 InheritDynIncl (llft_elt_toks κs)] *)
  Lemma typed_on_endlft_trigger_dyn_incl E L κs T :
    li_tactic (llctx_release_toks_goal L κs) (λ L', T L')
    ⊢ typed_on_endlft_trigger E L InheritDynIncl (llft_elt_toks κs) T.
  Proof.
    rewrite /llctx_release_toks_goal.
    iIntros "(%L' & %Hrel & Hs)" (F ?) "#HE HL Htoks".
    iMod (llctx_return_elt_toks _ _ L' with "HL Htoks") as "HL"; first done.
    eauto with iFrame.
  Qed.
  Global Instance typed_on_endlft_trigger_dyn_incl_inst E L κs : TypedOnEndlftTrigger E L InheritDynIncl (llft_elt_toks κs) :=
    λ T, i2p (typed_on_endlft_trigger_dyn_incl E L κs T).

  (** Instance for obtaining observations [Inherit κ1 (InheritGhost) ..] *)
  Lemma typed_on_endlft_trigger_ghost E L (P : iProp Σ) T :
    (P -∗ T L)
    ⊢ typed_on_endlft_trigger E L InheritGhost P T.
  Proof.
    iIntros "HT" (F ?) "#HE HL HP".
    iPoseProof ("HT" with "HP") as "HT".
    eauto with iFrame.
  Qed.
  Global Instance typed_on_endlft_trigger_ghost_inst E L (P : iProp Σ) : TypedOnEndlftTrigger E L InheritGhost P :=
    λ T, i2p (typed_on_endlft_trigger_ghost E L P T).

  (** Instance for resolving Rel2 with another observation *)
  (* TODO *)

  (* Currently the thing with static is broken.
    Maybe I should have MaybeInherit that simplifies to the direct proposition if it doesn't have a lifetime. *)

  (* Point: I should still run the endlft hooks *)
  (* TODO *)
  Lemma introduce_with_hooks_maybe_inherit_none E L {K} (k : K) P T :
    introduce_with_hooks E L P T
    ⊢ introduce_with_hooks E L (MaybeInherit None k P) T.
  Proof.
    iIntros "HT" (??) "#HE HL Hinh".
    rewrite /MaybeInherit.
    iMod ("Hinh" with "[//]") as "HP".
    iApply ("HT" with "[//] HE HL HP").
  Qed.
  Global Instance introduce_with_hooks_maybe_inherit_none_inst E L {K} (k : K) P :
    IntroduceWithHooks E L (MaybeInherit None k P) := λ T, i2p (introduce_with_hooks_maybe_inherit_none E L k P T).

  Lemma introduce_with_hooks_maybe_inherit_some E L {K} (k : K) κ P T :
    introduce_with_hooks E L (Inherit κ k P) T
    ⊢ introduce_with_hooks E L (MaybeInherit (Some κ) k P) T.
  Proof.
    iIntros "HT" (??) "#HE HL Hinh".
    rewrite /MaybeInherit. iApply ("HT" with "[//] HE HL Hinh").
  Qed.
  Global Instance introduce_with_hooks_maybe_inherit_some_inst E L {K} (k : K) κ P :
    IntroduceWithHooks E L (MaybeInherit (Some κ) k P) := λ T, i2p (introduce_with_hooks_maybe_inherit_some E L k κ P T).

  Lemma introduce_with_hooks_inherit E L {K} (k : K) κ P T :
    find_in_context (FindOptLftDead κ) (λ dead,
      if dead
      then typed_on_endlft_trigger E L k P T
      else Inherit κ k P -∗ T L)
    ⊢ introduce_with_hooks E L (Inherit κ k P) T.
  Proof.
    rewrite /FindOptLftDead/=. iIntros "(%dead & Hdead & HT)".
    simpl in *. destruct dead.
    - iIntros (??) "#HE HL Hinh".
      rewrite /Inherit. iMod ("Hinh" with "[//] Hdead") as "HP".
      iApply ("HT" with "[//] HE HL HP").
    - iIntros (??) "#HE HL Hinh".
      iExists L. iFrame. by iApply ("HT" with "Hinh").
  Qed.
  Global Instance introduce_with_hooks_inherit_inst E L {K} (k : K) κ P :
    IntroduceWithHooks E L (Inherit κ k P) := λ T, i2p (introduce_with_hooks_inherit E L k κ P T).

  Lemma introduce_with_hooks_lft_toks E L κs T :
    li_tactic (llctx_release_toks_goal L κs) T ⊢
    introduce_with_hooks E L (llft_elt_toks κs) T.
  Proof.
    rewrite /li_tactic /llctx_release_toks_goal.
    iIntros "(%L' & %HL & HT)".
    iIntros (F ?) "#HE HL Htoks".
    iMod (llctx_return_elt_toks _ _ L' with "HL Htoks") as "HL"; first done.
    eauto with iFrame.
  Qed.
  Global Instance introduce_with_hooks_lft_toks_inst E L κs : IntroduceWithHooks E L (llft_elt_toks κs) | 10 :=
    λ T, i2p (introduce_with_hooks_lft_toks E L κs T).

  (** StartLft *)
  Lemma type_startlft E L (n : string) sup_lfts s fn R ϝ :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookups_nofail_goal M sup_lfts) (λ κs,
      ∀ κ, named_lfts (named_lft_update n κ M) -∗
      (* add a credit -- will be used by endlft *)
      introduce_with_hooks E ((κ ⊑ₗ{0%nat} κs) :: L) (£ 1) (λ L2,
      typed_stmt E L2 s fn R ϝ)))
    ⊢ typed_stmt E L (annot: (StartLftAnnot n sup_lfts); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %κs & %Hlook & Hcont)".
    iIntros (?) "#(LFT & TIME & LLCTX) #HE HL Hcont'".
    iApply wps_annot => /=.
    iMod (llctx_startlft _ _ κs with "LFT LLCTX HL") as (κ) "HL"; [solve_ndisj.. | ].
    iApply step_fupd_intro; first solve_ndisj. iNext. iIntros "Hcred".
    iApply fupd_wps.
    iMod ("Hcont" with "[Hnamed] [] HE HL Hcred") as "(%L2 & HL & HT)"; [ | done | ].
    { iApply named_lfts_update. done. }
    by iApply ("HT" with "[$LFT $TIME $LLCTX] HE HL").
  Qed.

  (** Alias lifetimes: like startlft but without the atomic part *)
  Lemma type_alias_lft E L (n : string) sup_lfts s fn R ϝ :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookups_nofail_goal M sup_lfts) (λ κs,
      ∀ κ, named_lfts (named_lft_update n κ M) -∗ typed_stmt E ((κ ≡ₗ κs) :: L) s fn R ϝ))
    ⊢ typed_stmt E L (annot: (AliasLftAnnot n sup_lfts); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %κs & %Hlook & Hcont)".
    iIntros (?) "#(LFT & TIME & LLCTX) #HE HL Hcont'".
    iApply wps_annot => /=.
    set (κ := lft_intersect_list κs).
    iAssert (llctx_interp ((κ ≡ₗ κs) :: L))%I with "[HL]" as "HL".
    { iFrame "HL". iSplit; iApply lft_incl_refl. }
    iApply step_fupd_intro; first solve_ndisj. iNext. iIntros "Hcred".
    iApply ("Hcont" $! κ with "[Hnamed] [$LFT $TIME $LLCTX] HE HL").
    { iApply named_lfts_update. done. }
    done.
  Qed.

  (** EndLft *)
  (* TODO: also make endlft apply to local aliases, endlft should just remove them, without triggering anything. *)


  Lemma type_endlft E L (n : string) s fn R ϝ :
    (∃ M, named_lfts M ∗
      (* if this lifetime does not exist anymore, this is a nop *)
      li_tactic (compute_map_lookup_goal M n true) (λ o,
      match o with
      | Some κ =>
        (* find some credits *)
        prove_with_subtype E L false ProveDirect (£1) (λ L1 _ R2,
        (* find the new llft context *)
        li_tactic (llctx_find_llft_goal L1 κ LlctxFindLftFull) (λ '(_, L1'),
        li_tactic (llctx_remove_dead_aliases_goal L1' κ) (λ L2,
        (* simplify the name map *)
        li_tactic (simplify_lft_map_goal (named_lft_delete n M)) (λ M',
        named_lfts M' -∗
        (□ [† κ]) -∗
        (* extract observations from now-dead mutable references *)
        typed_pre_context_fold E L2 (CtxFoldExtractAllInit κ) (λ L3,
        (*typed_pre_context_fold E L3 (CtxFoldResolveAllInit) (λ L3',*)
        (* give back credits *)
        introduce_with_hooks E L3 (R2 ∗ £1 ∗ atime 1) (λ L4,
        (* run endlft triggers *)
        typed_on_endlft_pre E L4 κ (λ L5,
        typed_stmt E L5 s fn R ϝ)))))))
      | None => named_lfts M -∗ typed_stmt E L s fn R ϝ
      end))
    ⊢ typed_stmt E L (annot: (EndLftAnnot n); s) fn R ϝ.
  Proof.
    iIntros "(%M & Hnamed & Hlook)".
    unfold compute_map_lookup_goal.
    iDestruct "Hlook" as (o) "(<- & HT)".
    destruct (M !! n) as [κ | ]; first last.
    { iIntros (?) "#CTX #HE HL Hcont". iApply wps_annot.
      iApply step_fupdN_intro; first done.
      iIntros "!> _". by iApply ("HT" with "Hnamed CTX HE HL"). }
    unfold llctx_find_llft_goal, llctx_remove_dead_aliases_goal, li_tactic.
    iIntros (?) "#CTX #HE HL Hcont".
    iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & % & %R2 & >(Hc & HR2) & HL & HT)"; [done.. | ].
    iDestruct "HT" as "(%L' & % & %Hkill & Hs)".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%L'' & %Hsub & Hs)".
    iDestruct "Hs" as "(%M' & _ & Hs)".
    iPoseProof (llctx_end_llft ⊤ with "HL") as "Ha"; [done | done | apply Hkill | ].
    iApply fupd_wps.
    iMod ("Ha"). iApply (lc_fupd_add_later with "Hc"). iNext. iMod ("Ha") as "(#Hdead & HL)".
    iPoseProof (llctx_interp_sublist with "HL") as "HL".
    { apply Hsub. }

    iPoseProof ("Hs" with "[Hnamed] Hdead") as "HT".
    { by iApply named_lfts_update. }
    iPoseProof ("HT" $! ⊤ with "[] [] [] CTX HE HL") as "Hstep"; [done.. | ].
    rewrite /logical_step.
    iMod ("Hstep") as "(%k & Hat' & Hk)".
    iMod (persistent_time_receipt_0)as "Hp".
    iApply (wps_annot_credits with "[] Hat' Hp").
    { iDestruct "CTX" as "(_ & $ & _)". }
    iModIntro. iNext. iIntros "(Hc1 & Hc) Hat'". rewrite Nat.add_0_r.
    iEval (rewrite additive_time_receipt_succ) in "Hat'".
    iDestruct "Hat'" as "(Hat1 & Hat)".
    iMod ("Hk" with "Hc Hat") as "(%L5 & HL & HT)".

    iMod ("HT" with "[] HE HL [$HR2 $Hc1 $Hat1]") as "(%L6 & HL & HT)"; first done.
    iMod ("HT" with "[] HE HL Hdead") as "(%L7 & HL & HT)".
    { done. }
    by iApply ("HT" with "CTX HE HL").
  Qed.

  (** Dynamic inclusion *)
  Lemma type_dyn_include_lft E L n1 n2 s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n1) (λ κ1,
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (lctx_lft_alive_count_goal E L κ2) (λ '(κs, L'),
      Inherit κ1 InheritDynIncl (llft_elt_toks κs) -∗
      named_lfts M -∗
      typed_stmt ((κ1 ⊑ₑ κ2) :: E) L' s fn R ϝ))))
    ⊢ typed_stmt E L (annot: DynIncludeLftAnnot n1 n2; s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ1 & %Hlook1 & %κ2 & %Hlook2 & Hs)".
    unfold lctx_lft_alive_count_goal.
    iDestruct "Hs" as "(%κs & %L' & %Hal & Hs)".
    iIntros (?) "#(LFT & TIME & LCTX) #HE HL Hcont".
    iMod (lctx_include_lft_sem with "LFT HE HL") as "(HL & #Hincl & Hinh)"; [done.. | ].
    iSpecialize ("Hs" with "Hinh").
    iApply wps_annot. iApply step_fupdN_intro; first done.
    iIntros "!> _".
    iApply ("Hs" with "Hnamed [$] [] HL").
    { iFrame "HE Hincl". }
    done.
  Qed.

  (** ExtendLft *)
  Lemma type_extendlft E L (n : string) s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n) (λ κ,
      li_tactic (llctx_find_llft_goal L κ LlctxFindLftOwned) (λ '(κs, L'),
      (named_lfts M -∗ typed_stmt E ((κ ≡ₗ κs) :: L') s fn R ϝ))))
    ⊢ typed_stmt E L (annot: (EndLftAnnot n); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal /llctx_find_llft_goal.
    iIntros "(%M & Hnamed & %κ & _ & %L' & %κs & %Hfind & Hs)".
    iIntros (?) "#(LFT & TIME & LCTX) #HE HL Hcont".
    iMod (llctx_extendlft_local_owned with "LFT HL") as "HL"; [done.. | ].
    iApply wps_annot. iApply step_fupdN_intro; first done. iIntros "!> _".
    by iApply ("Hs" with "Hnamed [$] HE HL").
  Qed.

  (** UnconstrainedLftAnnot *)
  Lemma type_unconstrained_lft E L (n : string) s fn R ϝ sup `{!TCFastDone (UnconstrainedLftHint n sup)} :
    typed_stmt E L (annot: (StartLftAnnot n sup); s) fn R ϝ
    ⊢ typed_stmt E L (annot: (UnconstrainedLftAnnot n); s) fn R ϝ.
  Proof.
    done.
  Qed.

  (** CopyLftNameAnnot *)
  Lemma type_copy_lft_name E L n1 n2 s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (simplify_lft_map_goal (named_lft_update n1 κ2 (named_lft_delete n1 M))) (λ M',
        named_lfts M' -∗ typed_stmt E L s fn R ϝ)))
    ⊢ typed_stmt E L (annot: CopyLftNameAnnot n1 n2; s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ2 & _ & Hs)".
    iIntros (?) "#CTX #HE HL Hcont".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%M' & _ & Hs)".
    iApply wps_annot. iApply step_fupdN_intro; first done.
    iIntros "!> _". by iApply ("Hs" with "Hnamed CTX HE HL").
  Qed.

  (** We instantiate the context folding mechanism for unblocking. *)
  Definition typed_context_fold_stratify_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_stratify π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R T :
    (* TODO: this needs a different stratification strategy *)
    stratify_ltype_unblock π E L StratRefoldOpened l lt r (Owned false)
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_stratify_interp π) E L' (CtxFoldStratifyAll) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_stratify_interp π) π E L (CtxFoldStratifyAll) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_stratify_inst := [instance typed_context_fold_step_stratify].
  Global Existing Instance typed_context_fold_step_stratify_inst.

  (* Note: the following lemma introduces evars on application and is thus not suitable to be directly applied with Lithium. *)
  Lemma typed_context_fold_stratify_init tctx π E L T :
    typed_context_fold (typed_context_fold_stratify_interp π) E L (CtxFoldStratifyAll) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_stratify_interp π) E L' acc T)
    ⊢ typed_pre_context_fold E L CtxFoldStratifyAllInit T.
  Proof.
    iIntros "Hf". iApply (typed_context_fold_init (typed_context_fold_stratify_interp π) ([], True%I) _ _ (CtxFoldStratifyAll)). iFrame.
    rewrite /typed_context_fold_stratify_interp/type_ctx_interp; simpl; done.
  Qed.

  Lemma type_stratify_context_annot E L s fn R ϝ :
    typed_pre_context_fold E L CtxFoldStratifyAllInit (λ L', typed_stmt E L' s fn R ϝ)
    ⊢ typed_stmt E L (annot: (StratifyContextAnnot); s) fn R ϝ.
  Proof.
    iIntros "HT".
    iIntros (?) "#CTX #HE HL Hcont".
    iApply fupd_wps.
    iPoseProof ("HT" $! ⊤ with "[//] [//] [//] CTX HE HL") as "Hstep".
    (* TODO need to unfold logical_step because we cannot eliminate one over a statement wp *)
    rewrite /logical_step.
    iMod "Hstep" as "(%n & Hat & Hvs)".
    iMod (persistent_time_receipt_0) as "Hp".
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iApply (wps_annot_credits with "TIME Hat Hp").
    iModIntro. iNext. rewrite Nat.add_0_r. rewrite (additive_time_receipt_sep 1).
    iIntros "[Hcred1 Hcred] [Hat1 Hat]".
    iApply fupd_wps.
    iMod ("Hvs" with "Hcred Hat") as "(%L' & HL & HT)".
    by iApply ("HT" with "[$LFT $TIME $LLCTX] HE HL").
  Qed.

  (** We instantiate the context folding mechanism for extraction of observations. *)
  Definition typed_context_fold_extract_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_extract π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R κ T :
    stratify_ltype_extract π E L StratNoRefold l lt r (Owned false) κ
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_stratify_interp π) E L' (CtxFoldExtractAll κ) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_extract_interp π) π E L (CtxFoldExtractAll κ) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_extract_inst := [instance typed_context_fold_step_extract].
  Global Existing Instance typed_context_fold_step_extract_inst.

  Lemma typed_context_fold_extract_init tctx π E L κ T :
    typed_context_fold (typed_context_fold_stratify_interp π) E L (CtxFoldExtractAll κ) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_stratify_interp π) E L' acc T)
    ⊢ typed_pre_context_fold E L (CtxFoldExtractAllInit κ) T.
  Proof.
    iIntros "Hf". iApply (typed_context_fold_init (typed_context_fold_stratify_interp π) ([], True%I) _ _ (CtxFoldExtractAll κ)). iFrame.
    rewrite /typed_context_fold_stratify_interp/type_ctx_interp; simpl; done.
  Qed.

  (** We instantiate the context folding mechanism for resolution of observations. *)
  Definition typed_context_fold_resolve_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_resolve π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R T :
    stratify_ltype_resolve π E L StratNoRefold l lt r (Owned false)
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_resolve_interp π) E L' (CtxFoldResolveAll) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_resolve_interp π) π E L (CtxFoldResolveAll) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_resolve_inst := [instance typed_context_fold_step_resolve].
  Global Existing Instance typed_context_fold_step_resolve_inst.

  Lemma typed_context_fold_resolve_init tctx π E L T :
    typed_context_fold (typed_context_fold_resolve_interp π) E L (CtxFoldResolveAll) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_resolve_interp π) E L' acc T)
    ⊢ typed_pre_context_fold E L (CtxFoldResolveAllInit) T.
  Proof.
    iIntros "Hf". iApply (typed_context_fold_init (typed_context_fold_resolve_interp π) ([], True%I) _ _ (CtxFoldResolveAll)). iFrame.
    rewrite /typed_context_fold_resolve_interp/type_ctx_interp; simpl; done.
  Qed.

  (* Typing rule for [Return] *)
  Lemma type_return E L e fn (R : typed_stmt_R_t) ϝ:
    typed_val_expr E L e (λ L' π v rt ty r,
      v ◁ᵥ{π} r @ ty -∗
      typed_context_fold (typed_context_fold_stratify_interp π) E L' CtxFoldStratifyAll fn.(rf_locs).*1 ([], True%I) (λ L2 m' acc,
        introduce_with_hooks E L2 (type_ctx_interp π acc.1 ∗ acc.2) (λ L3,
          prove_with_subtype E L3 true ProveDirect (
            foldr (λ (e : (loc * layout)) T, e.1 ◁ₗ[π, Owned false] (#()) @ (◁ (uninit (UntypedSynType e.2))) ∗ T)
            True%I
            fn.(rf_locs)) (λ L3 _ R2, introduce_with_hooks E L3 R2 (λ L4,
            (* important: when proving the postcondition [R v], we already have the ownership obtained by deinitializing the local variables [R2] available.
              The remaining goal is fully encoded by [R v], so the continuation is empty.
            *)
            R v L4
            )))))
    ⊢ typed_stmt E L (return e) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hcont". wps_bind.
    wp_bind.
    iApply ("He" with "CTX HE HL").
    iIntros (L' π v rt ty r) "HL Hv HR".
    iApply fupd_wp.
    iMod ("HR" with "Hv [] [] [] CTX HE HL []") as "(%L2 & %acc & %m' & HL & Hstep & HT)"; [done.. | | ].
    { simpl. iApply logical_step_intro. iSplitR; last done. rewrite /type_ctx_interp. done. }
    iDestruct "CTX" as "(LFT & TIME & LLCTX)".
    iModIntro. iApply to_expr_wp. wp_bind.
    iApply (wp_logical_step with "TIME Hstep"); [done.. | ].
    iApply wp_skip. iNext. iIntros "_ Hacc".
    rewrite /typed_context_fold_stratify_interp.
    destruct acc as (ctx & R2).
    iMod ("HT" with "[] HE HL Hacc") as "(%L3 & HL & HT)"; first done.
    iMod ("HT" with "[] [] [] [$] HE HL") as "(%L4 & % & %R3 & HP & HL & HT)"; [done.. | ].
    iApply (wp_maybe_logical_step with "TIME HP"); [done.. | ].
    iModIntro. iApply wp_skip. iNext. iIntros "_ (Ha & HR2)".
    iApply wps_return.
    unfold li_tactic, llctx_find_llft_goal.
    iMod ("HT" with "[] HE HL HR2") as "(%L5 & HL & HT)"; first done.


    generalize (rf_locs fn) as ls => ls.
    iAssert (|={⊤}=> ([∗ list] l ∈ ls, l.1 ↦|l.2|))%I with "[Ha]" as ">Ha".
    { iInduction ls as [|[l ly] ls] "IH"; csimpl in*; simplify_eq.
      { by iFrame. }
      iDestruct "Ha" as "[Hl HR]".
      iMod ("IH" with "HR") as "?".
      iFrame.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly' & %Halg & % & _ & _ & _ & % & <- & Hv)".
      simpl in Halg. apply syn_type_has_layout_untyped_inv in Halg as [-> _].
      iMod (fupd_mask_mono with "Hv") as "(%v0 & Hl & Hv)"; first done.
      iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Halg' & %)".
      simpl in Halg'. apply syn_type_has_layout_untyped_inv in Halg' as [-> _].
      iExists _. by iFrame. }
    by iApply ("Hcont" with "HL Ha HT").
  Qed.
End typing.



(* This must be an hint extern because an instance would be a big slowdown . *)
Global Hint Extern 1 (Subsume (?v ◁ᵥ{_} ?r1 @ ?ty1) (?v ◁ᵥ{_} ?r2 @ ?ty2)) =>
  class_apply own_val_subsume_id_inst : typeclass_instances.
Global Hint Extern 1 (Subsume (?l ◁ₗ{_, _} ?r1 @ ?ty) (?l ◁ₗ{_, _} ?r2 @ ?ty)) =>
  class_apply own_shr_subsume_id_inst : typeclass_instances.


Global Typeclasses Opaque subsume_full.
Global Typeclasses Opaque credit_store.
Global Typeclasses Opaque typed_value.
Global Typeclasses Opaque typed_option_map.
Global Typeclasses Opaque typed_val_expr.

Global Typeclasses Opaque typed_bin_op.

Global Typeclasses Opaque typed_un_op.

Global Typeclasses Opaque typed_check_bin_op.

Global Typeclasses Opaque typed_check_un_op.

Global Typeclasses Opaque typed_if.

Global Typeclasses Opaque typed_call.

Global Typeclasses Opaque typed_annot_expr.

Global Typeclasses Opaque introduce_with_hooks.
Global Typeclasses Opaque typed_stmt_post_cond.

Global Typeclasses Opaque typed_assert.

Global Typeclasses Opaque typed_annot_stmt.

Global Typeclasses Opaque typed_switch.

Global Typeclasses Opaque typed_place.

Global Typeclasses Opaque cast_ltype_to_type.

Global Typeclasses Opaque resolve_ghost.

Global Typeclasses Opaque find_observation.

Global Typeclasses Opaque stratify_ltype.
Global Typeclasses Opaque typed_stmt.

Global Typeclasses Opaque typed_block.


Global Typeclasses Opaque stratify_ltype_post_hook.

Global Typeclasses Opaque weak_subtype.

Global Typeclasses Opaque weak_subltype.

Global Typeclasses Opaque owned_subtype.

Global Typeclasses Opaque owned_subltype_step.

Global Typeclasses Opaque mut_subtype.

Global Typeclasses Opaque mut_subltype.

Global Typeclasses Opaque mut_eqtype.

Global Typeclasses Opaque mut_eqltype.

Global Typeclasses Opaque prove_with_subtype.

Global Typeclasses Opaque prove_place_cond.
Global Typeclasses Opaque typed_read_end.

Global Typeclasses Opaque typed_write_end.

Global Typeclasses Opaque typed_borrow_mut.

Global Typeclasses Opaque typed_borrow_mut_end.

Global Typeclasses Opaque typed_borrow_shr.

Global Typeclasses Opaque typed_borrow_shr_end.

Global Typeclasses Opaque typed_addr_of_mut.

Global Typeclasses Opaque typed_addr_of_mut_end.

Global Typeclasses Opaque interpret_typing_hint.

Global Typeclasses Opaque typed_context_fold.


Global Typeclasses Opaque typed_context_fold_end.

Global Typeclasses Opaque relate_list.

Global Typeclasses Opaque relate_hlist.

Global Typeclasses Opaque fold_list.

Global Typeclasses Opaque typed_on_endlft.

Global Typeclasses Opaque typed_on_endlft_trigger.
Global Typeclasses Opaque typed_pre_context_fold.

Global Typeclasses Opaque typed_context_fold_step.

Global Typeclasses Opaque typed_write.



Global Typeclasses Opaque llctx_release_toks_goal.

Global Typeclasses Opaque lctx_lft_alive_count_goal.

Global Typeclasses Opaque typed_place_finish.

Global Typeclasses Transparent typed_place_finish.

Global Typeclasses Opaque typed_read.
