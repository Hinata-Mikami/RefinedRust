From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import programs ltypes.
From refinedrust Require Import options.

Section rules.
  Context `{!typeGS Σ}.

  Lemma owned_subltype_step_enum_uninit π E L l {rt rte} (en : enum rt) (lte : ltype rte) rs tag re st T  :
    owned_subltype_step π E L l #rs #() (EnumLtype en tag lte re) (◁ uninit st) T :-
    ∀ le,
      (*ste ← tactic (compute_map_lookup_goal (list_to_map (en.(enum_els).(els_variants))) tag false);*)
      return owned_subltype_step π E L le #re #() lte (◁ uninit (ltype_st lte)) T.
  Proof.
  Admitted.
  Definition owned_subltype_step_enum_uninit_inst := [instance owned_subltype_step_enum_uninit].
  Global Existing Instance owned_subltype_step_enum_uninit_inst | 20.

End rules.
