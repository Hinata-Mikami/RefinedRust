From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs struct.subltype.
From refinedrust Require Import options.

(** ** Lemmas about deinitializing *)

Section deinit.
  Context `{!typeGS Σ}.


  (* TODO *)
  Lemma ltype_deinit_struct F π {rts} (lts : hlist ltype rts) (sls : struct_layout_spec) rs st l wl :
    lftE ⊆ F →
    syn_type_compat sls st →
    (l ◁ₗ[π, Owned wl] rs @ (StructLtype lts sls)) ={F}=∗
    l ◁ₗ[π, Owned false] #() @ (◁ uninit st).
  Proof.
    iIntros (? Hstcomp) "Hl".
    rewrite ltype_own_struct_unfold /struct_ltype_own.
    (* this doesn't hold because we might have an alias. *)

    (*
    iDestruct "Hl" as "(%ly & %Halg & % & Hlb & Hcreds & %r' & ? & Hb)".
    iMod (maybe_use_credit with "Hcreds Hb") as "(? & ? & %l' & Hl & Hb)"; first done.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly. simpl. iSplitR.
    { destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iR.
    iSplitL "Hlb"; first by iFrame. iR.
    iExists tt. iR.
    iModIntro. iExists l'. iFrame. rewrite uninit_own_spec. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hstcomp as [<- | (ly1 & Hst' & ->)]; first done.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.
     *)
  Abort.

End deinit.

Section rules.
  Context `{!typeGS Σ}.

  (* We iterate over all the fields to deinitialize them first, and then deinitialize the struct itself *)
  Lemma owned_subltype_step_struct_uninit π E L l {rts} (lts : hlist ltype rts) rs sls st T :
    owned_subltype_step π E L l #rs #() (StructLtype lts sls) (◁ uninit st) T :-
    exhale (⌜st = sls⌝);
    L2, R2 ← iterate: zip (hpzipl rts lts rs) sls.(sls_fields) with L, True%I {{ '((existT rt (lt, r)), (field, stf)) T L2 R2,
      return owned_subltype_step π E L2 (l atst{sls}ₗ field) r #() lt (◁ uninit stf) (λ L3 R3,
        T L3 (R2 ∗ R3))
      }};
    return T L2 R2.
  Proof.
    iIntros "(-> & Hit)".
    iIntros (??) "#CTX #HE HL Hl".

    rewrite ltype_own_struct_unfold/struct_ltype_own/=.
    iDestruct "Hl" as "(%sl & %Halg & %Hlen & %Hly & Hlb & _ & %rs' & -> & Hl)".
    iMod (fupd_mask_mono with "Hl") as "Hl"; first done.

    iPoseProof (struct_ltype_focus_components with "Hl") as "(Hl & Hclose_l)"; [done.. | ].
    Search li.iterate "elim".
    (* invariant: ownership of the first n uninit segments.
        ownership for the rest
    *)

    (*
    set (INV := λ (i : nat) (L2 : llctx) (R2 : iProp Σ),
      llctx_interp L2 ∗

      logical_step F ( ∗ R2)).
     *)

    (*Search iterate_elim2*)

  Admitted.
  Definition owned_subltype_step_struct_uninit_inst := [instance owned_subltype_step_struct_uninit].
  Global Existing Instance owned_subltype_step_struct_uninit_inst | 20.

  (* TODO: extractop *)
End rules.
