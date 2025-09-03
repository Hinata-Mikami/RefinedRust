#![rr::import("rrstd.iterator.theories", "map")]

use crate::traits::iterator::Iterator;

#[rr::export_as(core::iter::adapters::Map)]
// TODO: problematic for this specification: The trait bounds for I, F are not in scope here.
// TODO: should we expose the closure state?
#[rr::refined_by("x" : "MapXRT {rt_of I} {rt_of F}")]
#[rr::exists("Inv" : "{xt_of I} → {xt_of F} → iProp Σ")]
/// The map invariant holds.
#[rr::invariant(#own "Inv x.(map_it) x.(map_clos)")]
/// Given the invariant, we can advance the iterator:
#[rr::invariant(#own "li_sealed (□ (∀ it_state it_state' clos_state e,
    {I::Next} it_state (Some e) it_state' -∗
    Inv it_state clos_state -∗
    {F::Pre} clos_state *[e] ∗
    (∀ e' clos_state', {F::PostMut} clos_state *[e] clos_state' e' -∗ Inv it_state' clos_state')))")]
/// If no element is emitted, the invariant is also upheld.
#[rr::invariant(#own "li_sealed (□ (∀ it_state it_state' clos_state,
    {I::Next} it_state None it_state' -∗
    Inv it_state clos_state -∗
    Inv it_state' clos_state))")]
pub struct Map<B, I, F> 
where I: Iterator, F: FnMut(I::Item) -> B
{
    #[rr::field("$# x.(map_it)")]
    pub(crate) iter: I,
    #[rr::field("$# x.(map_clos)")]
    f: F,
}

// If I make this depend on Iterator, then it will be a bit tricky to make the Rocq declaration go
// through. 

#[rr::export_as(core::iter::adapters::Map)]
impl<B, I, F> Map<B, I, F> 
where I: Iterator, F: FnMut(I::Item) -> B
{

    #[rr::params("Inv" : "{xt_of I} → {xt_of F} → iProp Σ")]
    /// Precondition: The picked invariant should hold initially.
    #[rr::requires(#iris "Inv iter f")]
    /// Precondition: persistently, each iteration preserves the invariant.
    /// If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "li_sealed (□ (∀ it_state it_state' clos_state e,
        {I::Next} it_state (Some e) it_state' -∗
        Inv it_state clos_state -∗
        {F::Pre} clos_state *[e] ∗
        (∀ e' clos_state', {F::PostMut} clos_state *[e] clos_state' e' -∗ Inv it_state' clos_state')))")]
    /// Precondition: If no element is emitted, the invariant is also upheld.
    #[rr::requires(#iris "li_sealed (□ (∀ it_state it_state' clos_state,
        {I::Next} it_state None it_state' -∗
        Inv it_state clos_state -∗
        Inv it_state' clos_state))")]
    #[rr::returns("mk_map_x iter f")]
    pub(crate) fn new(iter: I, f: F) -> Map<B, I, F> {
        Map { iter, f }
    }

    pub(crate) fn into_inner(self) -> I {
        self.iter
    }
}

/// Spec: We have the pure parts of the inner Next and the pre- and postconditions.
#[rr::instantiate("Next" := "(λ s1 e s2, 
        if_iNone e ({MI::Next} s1.(map_it) None s2.(map_it)) ∗
        if_iSome e (λ e, ∃ e_inner,
            boringly ({MI::Next} s1.(map_it) (Some e_inner) s2.(map_it)) ∗
            boringly ({MF::Pre} s1.(map_clos) *[e_inner]) ∗
            boringly ({MF::PostMut} s1.(map_clos) *[e_inner] s2.(map_clos) e)
            ))%I")]
impl<MB, MI: Iterator, MF> Iterator for Map<MB, MI, MF>
where
    MF: FnMut(MI::Item) -> MB,
{
    type Item = MB;

    #[rr::trust_me]
    #[rr::default_spec]
    fn next(&mut self) -> Option<MB> {
        self.iter
            // Calling next is possible without preconditions.
            .next()
            // Calling the closure requires us to prove its precondition.
            .map(&mut self.f)
    }
}
