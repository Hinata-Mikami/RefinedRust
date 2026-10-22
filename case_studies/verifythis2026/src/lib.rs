#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![rr::package("verifythis2026")]
#![rr::include("stdlib")]

#![rr::import("refinedrust.extra_proofs.verifythis2026", "challenge1")]


mod wrappers;
use wrappers::*;



/// Proofs for Challenge 1 of VerifyThis 2026

// Precondition: The citation counts are sorted in descending order.
#[rr::requires("Hsorted": "revsorted a")]
// Precondition: n is the length of the citation array.
#[rr::requires("Hlength": "length a = (Z.to_nat n)")]
// Postcondition: The return value is the h-index of the citation counts.
#[rr::ensures("hindex a ret")]
pub fn compute(a: Vec<usize>, n: usize) -> usize {
    let mut h = 0;
    while (h < n && h < *vec_index(&a, h)) {
        #[rr::inv_vars("h")]
        #[rr::inv("Hh_bounds": "0 <= h ∧ h <= n")]
        #[rr::inv("Hprefix": "∀ (i: nat), 0 ≤ i ∧ i < (Z.to_nat h) -> a !!! i >= h")]
        #[rr::ignore] || {};

        h = h + 1;
    }
    return h;
}

// Precondition: The citation counts are sorted in descending order.
#[rr::requires("Hsorted": "revsorted a")]
// Precondition: n is the length of the citation array.
#[rr::requires("Hlength": "length a = Z.to_nat n")]
// Postcondition: The return value is the h-index of the citation counts.
#[rr::ensures("hindex a ret")]
pub fn compute_opt(a: Vec<usize>, n: usize) -> usize {
    let mut lo = 0;
    let mut hi = n;
    while (lo < hi) {
        #[rr::inv_vars("lo", "hi")]
        #[rr::inv("Hbounds": "0 <= lo ∧ lo <= hi ∧ hi <= n")]
        #[rr::inv("Hbefore": "∀ i : nat, 0 <= i ∧ i < lo -> a !!! i > i")]
        #[rr::inv("Hafter": "∀ i : nat, hi <= i ∧ i < n -> a !!! i <= i")]
        #[rr::ignore] || {};

        let mid = lo + (hi - lo) / 2;
        if (*vec_index(&a, mid) <= mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    return lo;
}

// Precondition: n is the length of the citation array.
#[rr::requires("length a = Z.to_nat n")]
// Postcondition: The returned citation counts are sorted in descending order.
#[rr::ensures("revsorted ret")]
// Postcondition: The returned array is a permutation of the input array.
#[rr::ensures("Permutation a ret")]
pub fn rsorted(mut a: Vec<usize>, n: usize) -> Vec<usize> {
    let mut i = 0;
    while i < n {
        #[rr::params("original")]
        #[rr::inv_vars("a", "i")]
        #[rr::inv("length a = Z.to_nat n")]
        #[rr::inv("Permutation original a")]
        #[rr::inv("revsorted_prefix a (Z.to_nat i)")]
        #[rr::ignore] || {};

        let mut j = i + 1;
        while j < n {
            #[rr::params("outer")]
            #[rr::inv_vars("a", "i", "j")]
            #[rr::inv("length a = Z.to_nat n")]
            #[rr::inv("0 <= i ∧ i < j ∧ j <= n")]
            #[rr::inv("Permutation outer a")]
            #[rr::inv("revsorted_prefix a (Z.to_nat i)")]
            #[rr::inv("∀ k : nat, Z.to_nat i <= k ∧ k < Z.to_nat j -> a !!! k <= a !!! Z.to_nat i")]
            #[rr::ignore] || {};

            if *vec_index(&a, i) < *vec_index(&a, j) {
                vec_swap(&mut a, i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    a
}

// Precondition: n is the length of the citation array.
#[rr::requires("length a = Z.to_nat n")]
// Postcondition: The return value is the h-index of the citation counts.
#[rr::ensures("hindex a ret")]
pub fn compute_opt_rsorted(a: Vec<usize>, n: usize) -> usize {
    let sorted = rsorted(a, n);
    compute_opt(sorted, n)
}

// Precondition: The citation counts are sorted in descending order.
#[rr::requires("Hsorted": "revsorted a.cur")]
// Precondition: h is the current h-index of the citation counts.
#[rr::requires("Hhindex": "hindex a.cur h")]
// Precondition: i identifies an element of the citation array.
#[rr::requires("Hindex": "i < length a.cur")]
// Precondition: Incrementing paper i does not overflow usize.
#[rr::requires("Hincrement_bound": "a.cur !!! Z.to_nat i < MaxInt usize")]
// Postcondition: j denotes the final position of the incremented citation count.
#[rr::exists("j")]
// Postcondition: The mutable array contains the incremented citation count at j.
#[rr::observe("a.ghost": "<[Z.to_nat j := #(a.cur !!! Z.to_nat i + 1)]> (<$#> a.cur)")]
// Postcondition: The incremented citation count only moves toward the front.
#[rr::ensures("0 <= j ∧ j <= i")]
// Postcondition: The resulting citation counts remain sorted in descending order.
#[rr::ensures("revsorted (increment_at a.cur (Z.to_nat j))")]
// Postcondition: Exactly one citation is added to paper i, with reordering allowed.
#[rr::ensures("citation_update a.cur (increment_at a.cur (Z.to_nat j)) (Z.to_nat i)")]
// Postcondition: The return value is the h-index of the resulting citation counts.
#[rr::ensures("hindex (increment_at a.cur (Z.to_nat j)) ret")]
pub fn update(a: &mut Vec<usize>, h: usize, i: usize) -> usize {
    let x = *vec_index(&a, i);
    let mut lo = 0;
    let mut hi = i;

    while (lo < hi) {
        #[rr::inv_vars("lo", "hi", "x")]
        #[rr::inv("Hbounds": "0 <= lo ∧ lo <= hi ∧ hi <= i")]
        #[rr::inv("Hvalue": "x = a !!! Z.to_nat i")]
        #[rr::inv("Hbefore": "∀ j : nat, 0 <= j ∧ j < lo -> a !!! j > x")]
        #[rr::inv("Hat_or_after": "∀ j : nat, hi <= j ∧ j <= i -> a !!! j = x")]
        #[rr::ignore] || {};

        let mid = lo + (hi - lo) / 2;
        if (*vec_index(&a, mid) == x) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    *vec_index_mut(a, lo) = x + 1;
    if (lo == h && x == h) {
        return h + 1;
    }
    h
}

// Precondition: The citation counts are sorted in descending order.
#[rr::requires("Hsorted_initial": "revsorted a.cur")]
// Precondition: h is the current h-index of the citation counts.
#[rr::requires("Hhindex": "hindex a.cur h")]
// Precondition: i identifies an element of the citation array.
#[rr::requires("Hindex": "(Z.to_nat i < length a.cur)%nat")]
// Precondition: The array length is representable as a usize.
#[rr::requires("Hlength_bound": "length a.cur <= MaxInt usize")]
// Precondition: At least one citation is added.
#[rr::requires("Hk_positive": "1 <= k")]
// Precondition: Adding k citations does not overflow usize.
#[rr::requires("Hadd_bound": "a.cur !!! Z.to_nat i + k <= MaxInt usize")]
// Postcondition: final denotes the resulting citation array.
#[rr::exists("final")]
// Postcondition: The mutable array contains final when the function returns.
#[rr::observe("a.ghost": "(<#> final) : list (place_rfn Z)")]
// Postcondition: The resulting citation counts remain sorted in descending order.
#[rr::ensures("revsorted final")]
// Postcondition: final adds k citations to paper i and only reorders entries.
#[rr::ensures("citation_update_k a.cur final (Z.to_nat i) k")]
// Postcondition: The return value is the h-index of the resulting citation counts.
#[rr::ensures("hindex final ret")]
pub fn update_k(a: &mut Vec<usize>, h: usize, i: usize, k: usize) -> usize {
    let x = *vec_index(&a, i) + k;
    *vec_index_mut(a, i) = x;
    let mut j = i;

    while 0 < j && *vec_index(&a, j - 1) < x {
        #[rr::params("original", "original_ghost")]
        #[rr::inv_vars("a", "x", "j")]
        #[rr::inv("Hghost": "a.ghost = original_ghost")]
        #[rr::inv("Hlength": "length a.cur = length original")]
        #[rr::inv("Hj_bounds": "0 <= j ∧ j < length a.cur")]
        #[rr::inv("Hmoving": "a.cur !!! Z.to_nat j = x")]
        #[rr::inv("Hupdate": "citation_update_k original a.cur (Z.to_nat i) k")]
        #[rr::inv("Halmost": "revsorted_except_at a.cur (Z.to_nat j)")]
        #[rr::ignore] || {};

        vec_swap(a, j - 1, j);
        j = j - 1;
    }

    let n = vec_len(&a);
    if h < n && h < *vec_index(&a, h) {
        h + 1
    } else {
        h
    }
}
