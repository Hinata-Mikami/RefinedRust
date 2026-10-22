#![rr::import("rrstd.iterator.theories", "take")]

use crate::traits::iterator::Iterator;

#[rr::export_as(core::iter::adapters::Take)]
#[rr::refined_by("x" : "TakeXRT {rt_of I}")]
#[rr::derive_instantiate("DropGlueUnwind" := "{I::DropGlueUnwind}")]
pub struct Take<I> {
    #[rr::field("#($# x.(take_it))")]
    iter: I,
    #[rr::field("#(Z.of_nat x.(take_n))")]
    n: usize,
}

#[rr::export_as(core::iter::adapters::Take)]
impl<I> Take<I> {
    #[rr::returns("mk_take_x iter (Z.to_nat n)")]
    pub fn new(iter: I, n: usize) -> Take<I> {
        Take { iter, n }
    }
}


#[rr::instantiate("Params" := "{MI::Params}")]
#[rr::instantiate("Inv" := "λ π p s, {MI::Inv} π p s.(take_it)")]
// TODO: could also unify the decide branches, but that depends a bit on how easily we can simplify seq to [] in that case
#[rr::instantiate("Next" := "(λ π p_inner s1 e s2, 
        if_iNone e (
            (⌜s1.(take_n) = 0%nat⌝ ∗ True) ∨ (⌜s1.(take_n) ≠ 0%nat⌝ ∗ ⌜s2.(take_n) = (s1.(take_n) - 1)%nat⌝ ∗ {MI::Next} π p_inner s1.(take_it) None s2.(take_it))) ∗ 
        if_iSome e (λ e, ⌜s1.(take_n) > 0%nat⌝ ∗ ⌜s2.(take_n) = (s1.(take_n) - 1)%nat⌝ ∗ {MI::Next} π p_inner s1.(take_it) (Some e) s2.(take_it)))%I")]
impl<MI> Iterator for Take<MI>
where
    MI: Iterator,
{
    type Item = <MI as Iterator>::Item;

    fn next(&mut self) -> Option<<MI as Iterator>::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }
}
