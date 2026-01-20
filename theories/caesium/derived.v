From caesium Require Export tactics lifting proofmode.
Set Default Proof Using "Type".

Section derived.
  Context `{refinedcG Σ} `{ALG : LayoutAlg}.

  Lemma wps_annot A (a : A) π Q Ψ s:
    (|={⊤}⧗=> WPs{π} s {{ Q, Ψ }}) -∗ WPs{π} AnnotStmt 1 a s {{ Q , Ψ }}.
  Proof using ALG.
    iIntros "Hs".
    rewrite /AnnotStmt /SkipES /=.
    wps_bind. iApply wp_skip.
    iApply (physical_step_wand with "Hs"). iIntros "Hs".
    iApply wps_exprs.
    iApply physical_step_intro.
    iNext. done.
  Qed.
End derived.
