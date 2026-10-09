#![rr::import("rrstd.iterator.theories", "skip")]

use crate::traits::iterator::Iterator;

#[rr::export_as(core::iter::adapters::Skip)]
#[rr::refined_by("x" : "SkipXRT {rt_of I}")]
#[rr::derive_instantiate("DropGlueUnwind" := "{I::DropGlueUnwind}")]
pub struct Skip<I> {
    #[rr::field("#($# x.(skip_it))")]
    iter: I,
    #[rr::field("#(Z.of_nat x.(skip_n))")]
    n: usize,
}

#[rr::export_as(core::iter::adapters::Skip)]
impl<I> Skip<I> {
    #[rr::returns("mk_skip_x iter (Z.to_nat n)")]
    pub fn new(iter: I, n: usize) -> Skip<I> {
        Skip { iter, n }
    }
}

#[rr::instantiate("Params" := "{MI::Params}")]
#[rr::instantiate("Inv" := "(λ π p s, ⌜DropGlue_MIastraits_iterator_Iterator_Item_spec_attrs.(DropGlue_DropGlueUnwind) → False⌝ ∗ {MI::Inv} π p s.(skip_it))%I")]
#[rr::instantiate("Next" := "(λ π p_inner s1 e s2, 
        if_iNone e (
             ∃ seq s2_inner, 
                ⌜length seq ≤ s1.(skip_n)⌝ ∗ ⌜s2.(skip_n) = 0%nat⌝∗ 
                IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.(skip_it) seq s2_inner ∗
                {MI::Next} π p_inner s2_inner None s2.(skip_it)) ∗ 
        if_iSome e (λ e, 
            ∃ seq s2_inner, 
                ⌜length seq = s1.(skip_n)⌝ ∗ ⌜s2.(skip_n) = 0%nat⌝∗ 
                IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.(skip_it) seq s2_inner ∗
                {MI::Next} π p_inner s2_inner (Some e) s2.(skip_it)))%I")]
impl<MI> Iterator for Skip<MI>
where
    MI: Iterator,
{
    type Item = <MI as Iterator>::Item;

    fn next(&mut self) -> Option<MI::Item> {
        if self.n > 0 {
            let n = self.n;
            self.n = 0;
            self.iter.nth(n)
        } else {
            self.iter.next()
        }
    }
}
