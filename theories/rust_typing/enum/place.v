From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype programs.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.


Section rules.
  Context `{!typeGS Σ}.

  (** Unfolding instances *)

  (* needs to have lower priority than the id instance *)
  Import EqNotations.
  Lemma typed_place_ofty_enum_owned {rt} π E L l (en : enum rt) (r : rt) bmin0 wl P T :
    typed_place π E L l (EnumLtype en (enum_tag' en r) (◁ enum_ty en r) (enum_r en r)) (#r) bmin0 (Owned wl) P T
    ⊢ typed_place π E L l (◁ (enum_t en)) (#r) bmin0 (Owned wl) P T.
  Proof.
    (*iIntros "Hp". iApply typed_place_eqltype; last iFrame.*)
    (*iIntros (?) "HL CTX HE".*)
    (*iIntros (??). iApply struct_t_unfold.*)
  (*Qed.*)
  Admitted.
  Definition typed_place_ofty_enum_owned_inst := [instance @typed_place_ofty_enum_owned].
  Global Existing Instance typed_place_ofty_enum_owned_inst | 30.

  (* Also directly unfold the struct field *)
  Lemma typed_place_ofty_enum_struct_owned {rt} π E L l (en : enum rt) (r : rt) {rts} (tys : hlist type rts) rs sls tag bmin0 wl P T :
    typed_place π E L l (EnumLtype en tag (StructLtype (hmap (λ _, OfTy) tys) sls) (rs)) (#r) bmin0 (Owned wl) P T
    ⊢ typed_place π E L l (EnumLtype en tag (◁ struct_t sls tys) (rs)) (#r) bmin0 (Owned wl) P T.
  Proof.
  Admitted.
  Definition typed_place_ofty_enum_struct_owned_inst := [instance @typed_place_ofty_enum_struct_owned].
  Global Existing Instance typed_place_ofty_enum_struct_owned_inst | 30.

  Lemma typed_place_ofty_enum_shared {rt} π E L l (en : enum rt) (r : rt) bmin0 κ P T :
    typed_place π E L l (EnumLtype en (enum_tag' en r) (◁ enum_ty en r) (enum_r en r)) (#r) bmin0 (Shared κ) P T
    ⊢ typed_place π E L l (◁ (enum_t en)) (#r) bmin0 (Shared κ) P T.
  Proof.
    (*iIntros "Hp". iApply typed_place_eqltype; last iFrame.*)
    (*iIntros (?) "HL CTX HE".*)
    (*iIntros (??). iApply struct_t_unfold.*)
  (*Qed.*)
  Admitted.
  Definition typed_place_ofty_enum_shared_inst := [instance @typed_place_ofty_enum_shared].
  Global Existing Instance typed_place_ofty_enum_shared_inst | 30.

  (* Also directly unfold the struct field *)
  Lemma typed_place_ofty_enum_struct_shared {rt} π E L l (en : enum rt) (r : rt) {rts} (tys : hlist type rts) rs sls tag bmin0 κ P T :
    typed_place π E L l (EnumLtype en tag (StructLtype (hmap (λ _, OfTy) tys) sls) (rs)) (#r) bmin0 (Shared κ) P T
    ⊢ typed_place π E L l (EnumLtype en tag (◁ struct_t sls tys) (rs)) (#r) bmin0 (Shared κ) P T.
  Proof.
  Admitted.
  Definition typed_place_ofty_enum_struct_shared_inst := [instance @typed_place_ofty_enum_struct_shared].
  Global Existing Instance typed_place_ofty_enum_struct_shared_inst | 30.

  (* TODO also need resolve ghost instances, eventually *)
  (* TODO: plan for allowing strong updates:
      - OpenedLtype? but to what do we open...
      - we could also have an argument for the current refinement type and refinement.
        Problem: how does that impact the full refinement?
          Also that cannot be okay for mutable references. for mutable references, I need to be sure that I can get back to the original borrow.
          But I guess that would always be satisfied? I suppose in the unique representation it works.. I enforce that the type is the same between the current and final thing in the pinned borrow. and that the refinement type stays the same, so that the gvar interpretation works.
          but then the full power I only use in Owned.
          I only get a weak update
      - or we refine EnumLtype by the current inner refinement..
        Problem: then we do strong refinement updates, which isn't cool below mutable refs.
   *)
  (*place_cont_t*)

  Program Definition enum_tag_ty_inj' {rt} (en : enum rt) (r : rt) (tag : string) (Heq : enum_tag en r = Some tag) :
    sigT (λ e : enum_tag_sem rt, enum_tag_ty_inj en tag = Some e) :=
    (*match enum_tag_compat _ en r tag Heq with*)
    (*| existT vinj Heq' => existT (mk_enum_tag_sem (enum_rt en r) (enum_ty en r) vinj) Heq'*)
    (*end*)
    existT (mk_enum_tag_sem (enum_rt en r) (enum_ty en r)
      (match enum_tag_compat _ en r tag Heq with
      | existT vinj Heq' => vinj
      end))
      (match enum_tag_compat _ en r tag Heq with
      | existT vinj Heq' => Heq'
      end)
  .
  Next Obligation.
    simpl. intros. exact eq_refl.
  Defined.
  Definition enum_tag_rfn_inj {rt} (en : enum rt) (tag : string)
    (r_old : rt)
    (Heq : enum_tag en r_old = Some tag)
    : (enum_rt en r_old) → rt :=
    enum_tag_rt_inj (projT1 (enum_tag_ty_inj' en r_old tag Heq)).

  (*Definition enum_tag_rfn_inj' {rt} (en : enum rt) (tag : string)*)
    (*(r_old : rt)*)
    (*(Heq : enum_tag en r_old = Some tag)*)
    (*: (enum_tag_rt' en tag) → rt :=*)
    (*λ ri,*)
      (*enum_tag_rfn_inj en tag r_old Heq (rew <-[id] (enum_variant_rt_tag_rt_eq en r_old tag Heq) in ri).*)

  (*Definition placein_or_default {rt} (r : place_rfn rt) (def : rt) : rt :=*)
    (*match r with*)
    (*| PlaceIn r => r*)
    (*| _ => def*)
    (*end.*)

  Lemma typed_place_enum_data_field_owned {rt} π E L l (en : enum rt) (r : rt) bmin0 els tag tag' sls mem {rts} (lts : hlist ltype rts) rs P T :
    typed_place π E L l (EnumLtype en tag (StructLtype lts sls) rs) (#r) bmin0 (Owned false) (EnumDataPCtx els tag' :: GetMemberPCtx sls mem :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜tag = tag'⌝);
      ∃ (Heq : enum_tag en r = Some tag),
      ∃ (i : nat),
      exhale (⌜sls_field_index_of (sls_fields sls) mem = Some i⌝);
      ∃ (lto : ltype (lnth (unit : RT) rts i))
        (ro : place_rfn (lnth (unit : RT) rts i)),
      exhale (⌜hnth (UninitLtype UnitSynType) lts i = lto⌝);
      exhale (⌜pnth (# tt) rs i = ro⌝);
      return (typed_place π E L ((GetEnumDataLocSt l els) atst{sls}ₗ mem) lto ro bmin0 (Owned false) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (mkPUpd _ bmin0 
              _ 
              (EnumLtype en tag (StructLtype (hlist_insert rts lts i _ upd'.(pupd_lt)) sls) (plist_insert rts rs i _ upd'.(pupd_rfn)))
              (* no update, as we are owned *)
              #r
              upd'.(pupd_R)
              upd'.(pupd_performed)
              opt_place_update_eq_refl
              opt_place_update_eq_refl)))
      )).
  Proof.
  Admitted.
  Definition typed_place_enum_data_field_owned_inst := [instance @typed_place_enum_data_field_owned].
  Global Existing Instance typed_place_enum_data_field_owned_inst.

  (*typed_place_struct_uniq*)
  Lemma typed_place_enum_data_field_shared {rt} π E L l (en : enum rt) (r : rt) bmin0 els tag tag' sls mem {rts} (lts : hlist ltype rts) rs κ P T :
    typed_place π E L l (EnumLtype en tag (StructLtype lts sls) rs) (#r) bmin0 (Shared κ) (EnumDataPCtx els tag' :: GetMemberPCtx sls mem :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜tag = tag'⌝);
      ∃ (Heq : enum_tag en r = Some tag),
      ∃ (i : nat),
      exhale (⌜sls_field_index_of (sls_fields sls) mem = Some i⌝);
      ∃ (lto : ltype (lnth (unit : RT) rts i))
        (ro : place_rfn (lnth (unit : RT) rts i)),
      exhale (⌜hnth (UninitLtype UnitSynType) lts i = lto⌝);
      exhale (⌜pnth (# tt) rs i = ro⌝);
      return (typed_place π E L ((GetEnumDataLocSt l els) atst{sls}ₗ mem) lto ro bmin0 (Shared κ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (mkPUpd _ bmin0 
              _ 
              (EnumLtype en tag (StructLtype (hlist_insert rts lts i _ upd'.(pupd_lt)) sls) (plist_insert rts rs i _ upd'.(pupd_rfn)))
              (* no update, as we are shared *)
              #r
              upd'.(pupd_R)
              upd'.(pupd_performed)
              opt_place_update_eq_refl
              opt_place_update_eq_refl)))
      )).
  Proof.
  Admitted.
  Definition typed_place_enum_data_field_shared_inst := [instance @typed_place_enum_data_field_shared].
  Global Existing Instance typed_place_enum_data_field_shared_inst.

  (* NOTE for the uniq case, I'll need to know that the enum ty here is a struct. Will need some eqcasts, I guess.

    The interpretation will say that it is in the valid part,
      i.e.:
      - the refinement type matches up.
      - the refinement of the projection is in sync
     Moreover (implicit property as part of the borrow): we can unblock to it.
    I provide that equality there as an assumption.
     alternative: I prove it so that I get an eq_refl.

    If I do a strong update, I put OpenedLtype, which releases the constraint on the data field.

    If I do a weak update, I need to update the outer refinement as well.

  *)

  Lemma typed_place_enum_data_field_uniq {rt} π E L l (en : enum rt) (r : rt) bmin0 els tag tag' sls mem {rts} (lts : hlist ltype rts) rs κ γ P T :
    typed_place π E L l (EnumLtype en tag (StructLtype lts sls) rs) (#r) bmin0 (Uniq κ γ) (EnumDataPCtx els tag' :: GetMemberPCtx sls mem :: P) T :-
      exhale (⌜en.(enum_els) = els⌝);
      exhale (⌜tag = tag'⌝);
      ∃ (Heq : enum_tag en r = Some tag),
      (* the variant is in sync with the tag
        (we could also assume this from the interpretation, but we want that this is eq_refl) *)
      ∃ (Heq2 : enum_rt en r = plist place_rfnRT rts),
      inhale (⌜rs = rew [RT_rt] Heq2 in (enum_r en r)⌝);
      (* access the struct field *)
      ∃ (i : nat),
      exhale (⌜sls_field_index_of (sls_fields sls) mem = Some i⌝);
      ∃ (lto : ltype (lnth (unit : RT) rts i))
        (ro : place_rfn (lnth (unit : RT) rts i)),
      exhale (⌜hnth (UninitLtype UnitSynType) lts i = lto⌝);
      exhale (⌜pnth (# tt) rs i = ro⌝);
      return (typed_place π E L ((GetEnumDataLocSt l els) atst{sls}ₗ mem) lto ro bmin0 (Uniq κ γ) P (λ L2 κs l2 b2 bmin2 rti ltyi ri updcx,
        T L2 κs l2 b2 bmin2 rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd', 
            li_tactic (check_llctx_place_update_kind_incl_uniq_goal E L3 upd'.(pupd_performed) ([κ])) (λ oeq,
              match oeq with
              | Some Heq3 =>
                cont (mkPUpd _ bmin0 _
                  (EnumLtype en tag (StructLtype (hlist_insert rts lts i _ upd'.(pupd_lt)) sls) (plist_insert rts rs i _ upd'.(pupd_rfn)))
                  (#(enum_tag_rfn_inj en tag r Heq (rew <- [RT_rt] Heq2 in (plist_insert_id (unit : RT) rts rs i (
                    rew <- opt_place_update_eq_use _ _ _ Heq3 upd'.(pupd_eq_1)  in upd'.(pupd_rfn))))))
                  upd'.(pupd_R) 
                  upd'.(pupd_performed)
                  opt_place_update_eq_refl
                  opt_place_update_eq_refl
                )
              | None =>
                (* TODO strong update with Opened *)
                False
              end
            )))
        )).
  Proof.
  Admitted.
  Definition typed_place_enum_data_field_uniq_inst := [instance @typed_place_enum_data_field_uniq].
  Global Existing Instance typed_place_enum_data_field_uniq_inst.

  (** Stratification *)
  (*stratify_ltype*)
  (* we stratify recursively first.
     if we want to refold, then we show subtyping *)
  (*Search stratify_ltype.*)


  (*
  Lemma stratify_ltype_enum_shared :
    stratify_ltype π E L smu sdu sa m l
        (EnumLtype en tag lte re)
        (#r)
        (Shared κ)
        T :-
      ∀ le : loc,
      stratify_ltype π E L smu sdu sa m le lte (#re) (Shared κ) (λ L2 R rte lte re,
        match sa with
        | StratRefold
            *)


  (* TODO: what to do about this?
     - I guess I cannot really cast it anymore, because the refinement might not be in sync.
     - I could do this for a stronger version of cast_ltype that can also update the refinement, I guess.
     For now, we have to do this in stratify.
   *)

  (** cast_ltype *)
  (*
  Lemma cast_ltype_to_type_enum E L {rt} (en : enum rt) tag lte re T :
    cast_ltype_to_type E L lt (λ ty,
      mut_eqtype E L ty (enum_tag_type' en tag) (T (enum_t en)))
    ⊢ cast_ltype_to_type E L (EnumLtype en tag lte re) T.
  Proof.
  Admitted.
  Definition cast_ltype_to_type_enum_inst := [instance @cast_ltype_to_type_enum].
  Global Existing Instance cast_ltype_to_type_enum_inst.

  *)
End rules.
