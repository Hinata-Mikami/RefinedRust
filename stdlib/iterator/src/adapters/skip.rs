


pub struct Skip<I> {
    iter: I,
    n: usize,
}

// Issue here: we can't say when we are done!
// Solutions:
// - have a length function (as a generalization of Done)?
//   -> restrict to exact size?
// - has_more? (negation of done)
//   should be in iProp?
// - Next is a relation on options
//   + then with refinements we could get the existing spec
// - have a pure version of Next?


// this is a case for spec refinement?

// Logically, we make a two-phase transition here:
// - either we skip (in the first call to next)
// - or we just pass through

/*
#[rr::instantiate("History" := "λ s, s.(history)")]
#[rr::instantiate("Next" := "λ s1 e s2,
        ⌜s2.(n) = 0⌝ ∗
        ⌜{History} s2 = e :: {History} s1⌝ ∗
        if_iSome e (λ e,
            if bool_decide (s1.(n) = 0) then
                {I.Next} s1.(iter) (Some e) s2.(iter)
            else
                [∗ list] ...
        ) ∗
        if_iNone e (
            if bool_decide (s1.(n) = 0) then
                {I.Next} s1.(iter) None s2.(iter)
            else 
                ∃ m, 
                    m < n ∗
                    [∗ list] ...
        )")]
*/
impl<I> Iterator for Skip<I>
where
    I: Iterator,
{
    type Item = <I as Iterator>::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        if unlikely(self.n > 0) {
            self.iter.nth(crate::mem::take(&mut self.n))
        } else {
            self.iter.next()
        }
    }
}
