#![rr::import("refinedrust.extra_proofs.tests", "enums")]


#[rr::verify]
#[derive(Clone, Copy)]
enum Color {
    ColorA, 
    ColorB,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[rr::refined_by("sizes")]
// PEq
#[rr::derive_instantiate("PEq" := "λ a b, bool_decide (a = b)")]
// Eq
#[rr::derive_instantiate("PEq_refl" := #proof "intros ??; solve_goal")]
#[rr::derive_instantiate("PEq_sym" := #proof "intros ???; solve_goal")]
#[rr::derive_instantiate("PEq_trans" := #proof "intros ????; solve_goal")]
#[rr::derive_instantiate("PEq_leibniz" := #proof "intros ???; solve_goal")]
// POrd
#[rr::derive_instantiate("POrd" := "λ a b, Some (match a, b with | Sz1, Sz2 => Less | Sz2, Sz1 => Greater | _, _ => Equal end)")]
#[rr::derive_instantiate("POrd_eq_cons" := #proof "intros ???; solve_goal")]
// Ord
#[rr::derive_instantiate("Ord" := "λ a b, (match a, b with | Sz1, Sz2 => Less | Sz2, Sz1 => Greater | _, _ => Equal end)")]
#[rr::derive_instantiate("Ord_POrd" := #proof "intros ???; solve_goal")]
#[rr::derive_instantiate("Ord_lt_trans" := #proof "intros ????; solve_goal")]
#[rr::derive_instantiate("Ord_eq_trans" := #proof "intros ????; solve_goal")]
#[rr::derive_instantiate("Ord_gt_trans" := #proof "intros ????; solve_goal")]
#[rr::derive_instantiate("Ord_antisym" := #proof "intros ???; solve_goal")]
enum Sizes {
    #[rr::pattern("Sz1")]
    Sz1,
    #[rr::pattern("Sz2")]
    Sz2,
}
