
pub struct Zip<A, B> {
    a: A,
    b: B,
    // index, len and a_len are only used by the specialized version of zip
    //index: usize,
    //len: usize,
    //a_len: usize,
}


/// NOTE: This impl isn't using the indirection via ZipImpl.

/*
/// Spec: history projection
#[rr::instantiate("History" := "λ s, s.(history)")]
#[rr::instantiate("Next" := "λ s1 e s2,
        ⌜{History} s2 = e :: {History} s1⌝ ∗
        ⌜if_Some e (λ _, History s2 = zip (History s2.(a)) (History s2.(b))⌝ ∗
        ∃ e1 e2, 
        {A.Next} s1.(a) e1 s2.(a) ∗
        {B.Next} s1.(b) e2 s2.(b) ∗
        ⌜if_Some e (λ e, ∃ e1' e2', e1 = Some e1' ∧ e2 = Some e2' ∧ e = (e1', e2'))⌝ ∗
        ⌜if_None e (e1 = None ∨ e2 = None)⌝")]
*/
impl<A, B> Iterator for Zip<A, B>
where
    A: Iterator,
    B: Iterator,
{
    type Item = (A::Item, B::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let x = self.a.next()?;
        let y = self.b.next()?;
        Some((x, y))
    }
}
