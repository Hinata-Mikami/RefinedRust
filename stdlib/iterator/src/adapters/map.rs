
// TODO: problematic for this specification: The trait bounds for I, F are not in scope here.
// TODO: should we expose the closure state?
#[rr::refined_by("history" : "_", "iter" : "{rt_of I}", "clos" : "{rt_of F}")]
#[rr::exists("Inv" : "iter → clos → iProp Σ")]
/// The map invariant holds.
#[rr::invariant("Inv ({I.History} iter) clos_state")]
/// Given the invariant, we can advance the iterator:
/// TODO
pub struct Map<I, F> 
//where I: Iterator, F: FnMut(I::Item) -> B
{
    // Used for `SplitWhitespace` and `SplitAsciiWhitespace` `as_str` methods
    pub(crate) iter: I,
    f: F,
}

#[rr::export_as(core::iter::adapters)]
impl<I, F> Map<I, F> {
    pub(crate) fn new(iter: I, f: F) -> Map<I, F> {
        Map { iter, f }
    }

    pub(crate) fn into_inner(self) -> I {
        self.iter
    }
}

/// Spec: history projection
#[rr::instantiate("History" := "λ s, s.(history)")]
/// Spec: We have the pure parts of the inner Next and the pre- and postconditions.
#[rr::instantiate("Next" := "λ s1 e s2, 
        ⌜{History} s2 = e :: {History} s1⌝ ∗
        if_iNone e ({I.Next} s1.(iter) None s2.(iter)) ∗
        if_iSome e (λ e, ∃ e_inner,
            Boringly (
                {I.Next} s1.(iter) e_inner s2.(iter) ∗
                {F.Pre} s1.(f) e_inner ∗
                {F.Post} s1.(f) e_inner s2.(f) e
            ))")]
impl<B, I: Iterator, F> Iterator for Map<I, F>
where
    F: FnMut(I::Item) -> B,
{
    type Item = B;

    //#[inline]
    fn next(&mut self) -> Option<B> {
        self.iter
            // Calling next is possible without preconditions.
            .next()
            // Calling the closure requires us to prove its precondition.
            .map(&mut self.f)
    }
}
