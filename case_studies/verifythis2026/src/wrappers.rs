use std::vec::Vec;


/// These wrappers serve as a temporary workaround until RefinedRust supports unsized types and in
/// particular slices: the indexing and iteration methods on `Vec` work by dereferencing to slices,
/// which currently are not supported by RefinedRust.
/// For now, we thus create wrappers for these methods to which we can attach RefinedRust
/// specifications.
/// We have verified operationally equivalent versions of these functions against a model of Vec, justifying these specifications.

#[rr::only_spec]
#[rr::requires("index < length x.cur")]
#[rr::exists("γi")]
#[rr::returns("(x.cur !!! Z.to_nat index, γi)")]
#[rr::observe("x.ghost": "<[Z.to_nat index := PlaceGhost γi]> (<$#> x.cur)")]
pub fn vec_index_mut<T>(x: &mut Vec<T>, index: usize) -> &mut T {
    &mut x[index]
}

#[rr::only_spec]
#[rr::requires("index < length x")]
#[rr::returns("x !!! Z.to_nat index")]
pub fn vec_index<T>(x: &Vec<T>, index: usize) -> &T {
    &x[index]
}

#[rr::only_spec]
#[rr::requires("i < length x.cur")]
#[rr::requires("j < length x.cur")]
#[rr::requires("i ≠ j")]
#[rr::observe("x.ghost": "(PlaceIn <$> swap_at x.cur (Z.to_nat i) (Z.to_nat j)) : list (place_rfn Z)")]
pub fn vec_swap(x: &mut Vec<usize>, i: usize, j: usize) {
    x.swap(i, j)
}

#[rr::only_spec]
#[rr::requires("Z.of_nat (length x) ∈ USize")]
#[rr::returns("length x")]
pub fn vec_len<T>(x: &Vec<T>) -> usize {
    x.len()
}

#[rr::only_spec]
#[rr::returns("x")]
pub fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
    x.iter()
}

#[rr::only_spec]
#[rr::exists("γs")]
#[rr::ensures("length γs = length x.cur")]
#[rr::observe("x.ghost": "(PlaceGhost <$> γs) : list (place_rfn {rt_of T})")]
#[rr::returns("zip x.cur γs")]
pub fn vec_iter_mut<T>(x: &mut Vec<T>) -> core::slice::IterMut<'_, T> {
    x.iter_mut()
}
