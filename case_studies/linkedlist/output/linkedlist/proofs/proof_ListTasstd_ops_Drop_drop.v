From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_ListTasstd_ops_Drop_drop.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ListTasstd_ops_Drop_drop_proof (π : thread_id) :
  ListTasstd_ops_Drop_drop_lemma π.
Proof.
  ListTasstd_ops_Drop_drop_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_dropped [].
  rep <-! liRStep; liShow.
  - destruct remaining as [|xhead remaining]; simpl in H23; first done.
    injection H23 as <-.
    simpl.
    rep <-! liRStep; liShow.
    rep liRStep; liShow.
    liInst Hevar_dropped (dropped ++ [xhead]).
    rep <-! liRStep; liShow.
    iApply prove_with_subtype_default.
    rewrite big_sepL_app. simpl. iFrame.
    rep <-! liRStep; liShow.
  - destruct remaining as [|xhead remaining]; simpl in H23; last done.
    simpl.
    rep <-! liRStep; liShow.
    rep liRStep; liShow.
    iApply prove_with_subtype_default.
    simpl. iFrame.
    rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
