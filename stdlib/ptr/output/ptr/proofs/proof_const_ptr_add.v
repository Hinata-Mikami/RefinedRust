From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_add.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_add_proof (π : thread_id) :
  const_ptr_add_lemma π.
Proof.
  const_ptr_add_prelude.

   rep <-! liRStep; liShow.
   all:
    iAssert (loc_in_bounds (l offsetst{st_of T_ty}ₗ count) 0 0) as "?";
      first (iApply (loc_in_bounds_offset l); last done; sidecond_hammer).
  all: rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* basically, the reasoning is:
      - if T is a ZST, then the wrapped offset gets annihilated everywhere, so it's fine.
      - else, we also know that it's in isize_t, so it's same as before.
    *)
  4,6: rewrite /OffsetLocSt/offset_loc; simplify_layout (use_layout_alg' (ty_syn_type T_ty)); f_equiv.
  all: destruct (decide (ly_size T_st_ly = 0%nat)); [lia | ].
  all: assert (MinInt ISize ≤ count ≤ MaxInt ISize)%Z; first by solve_goal with nia; sidecond_hammer.
  all: rewrite wrap_to_it_id; sidecond_hammer.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
