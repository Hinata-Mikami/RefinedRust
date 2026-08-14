#![rr::import("rrstd.iterator.theories", "step_by")]

use crate::traits::iterator::Iterator;

#[rr::export_as(core::iter::adapters::StepBy)]
#[rr::refined_by("x" : "StepByXRT {rt_of I}")]
pub struct StepBy<I> {
    #[rr::field("$# x.(step_by_it)")]
    iter: I,
    #[rr::field("Z.of_nat x.(step_by_n)")]
    step_minus_one: usize,
    #[rr::field("x.(step_by_first)")]
    first_take: bool,
}

#[rr::export_as(core::iter::adapters::StepBy)]
impl<I> StepBy<I> {
    #[rr::requires("(0 < step)%Z")]
    #[rr::returns("mk_step_by_x iter (Z.to_nat (step - 1)) true")]
    pub(crate) fn new(iter: I, step: usize) -> StepBy<I> {
        assert!(step != 0);
        StepBy { iter, step_minus_one: step - 1, first_take: true }
    }
}

#[rr::instantiate("Params" := "{MI::Params}")]
#[rr::instantiate("Inv" := "λ π p s, {MI::Inv} π p s.(step_by_it)")]
#[rr::instantiate("Next" := "(λ π p_inner s1 e s2,
        ⌜s2.(step_by_n) = s1.(step_by_n)⌝ ∗
        ⌜s2.(step_by_first) = false⌝ ∗
        if s1.(step_by_first) then
          {MI::Next} π p_inner s1.(step_by_it) e s2.(step_by_it)
        else
          if_iNone e (
            ∃ seq s2_inner,
              ⌜length seq ≤ s1.(step_by_n)⌝ ∗
              IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.(step_by_it) seq s2_inner ∗
              {MI::Next} π p_inner s2_inner None s2.(step_by_it)) ∗
          if_iSome e (λ e,
            ∃ seq s2_inner,
              ⌜length seq = s1.(step_by_n)⌝ ∗
              IteratorNextFusedTrans traits_iterator_Iterator_MI_spec_attrs π p_inner s1.(step_by_it) seq s2_inner ∗
              {MI::Next} π p_inner s2_inner (Some e) s2.(step_by_it)))%I")]
impl<MI> Iterator for StepBy<MI>
where
    MI: Iterator,
{
    type Item = <MI as Iterator>::Item;

    fn next(&mut self) -> Option<MI::Item> {
        if self.first_take {
            self.first_take = false;
            self.iter.next()
        } else {
            self.iter.nth(self.step_minus_one)
        }
    }
}
