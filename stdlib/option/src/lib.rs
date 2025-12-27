#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.option")]

#![rr::include("closures")]
#![rr::include("ptr")]
#![rr::include("clone")]
#![rr::include("result")]

use core::mem;

#[rr::refined_by("option (place_rfn {rt_of T})")]
#[rr::export_as(core::option::Option)]
#[derive(Copy, Clone, Debug)]
pub enum Option<T> {
    #[rr::pattern("None")]
    #[rr::export_as(core::option::Option::None)]
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("*[x]")]
    #[rr::export_as(core::option::Option::Some)]
    Some(T)
}
use crate::Option::*;

#[rr::export_as(core::option::Option)]
#[rr::only_spec]
impl<T> Option<T> {

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("bool_decide (is_Some x)")]
    pub fn is_some(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("bool_decide (¬ is_Some x)")]
    pub fn is_none(&self) -> bool {
        unimplemented!()
    }

    #[rr::params("x")]
    #[rr::args("Some x")]
    #[rr::returns("x")]
    pub fn unwrap(self) -> T {
        unimplemented!();
    }

    #[rr::returns("default def self")]
    pub fn unwrap_or(self, def: T) -> T {
        match self {
            Some(x) => x,
            None => def,
        }
    }

}

#[rr::export_as(core::option::Option)]
impl<T> Option<T> {
    #[rr::params("Hx" : "TyGhostDrop {F}")]
    #[rr::ensures(#iris "if_iNone self (⌜ret = None⌝ ∗ ty_ghost_drop_for {F} Hx π ($# f))")]
    #[rr::requires(#iris "if_iSome self (λ self, {F::Pre} π f *[self])")]
    #[rr::ensures(#iris "if_iSome self (λ self, ∃ x, ⌜ret = Some x⌝ ∗ {F::Post} π f *[self] x)")]
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Some(x) => Some(f(x)),
            None => None,
        }
    }

    #[rr::only_spec]
    #[rr::returns("self.cur")]
    #[rr::observe("self.ghost": "(None : option (place_rfn {rt_of T}))")]
    pub fn take(&mut self) -> Option<T> {
        // FIXME(const-hack) replace `mem::replace` by `mem::take` when the latter is const ready
        mem::replace(self, None)
    }

    // TODO: maybe ghost drop Self, too, in case pred returns false.
    #[rr::params("Hx" : "TyGhostDrop {P}")]
    #[rr::requires(#iris "if_iSome self (λ self, {P::Pre} π predicate *[self])")]
    #[rr::ensures(#iris "if_iSome ret (λ ret, ⌜self = Some ret⌝ ∗ {P::Post} π predicate *[ret] true)")]
    #[rr::ensures(#iris "if_iNone ret (if_iNone self (ty_ghost_drop_for {P} Hx π ($# predicate)) ∗ 
                            if_iSome self (λ x, {P::Post} π predicate *[x] false))")]
    pub fn filter<P>(self, predicate: P) -> Self
    where
        P: FnOnce(&T) -> bool,
    {
        if let Some(x) = self {
            if predicate(&x) {
                return Some(x);
            }
        }
        None
    }
}

#[rr::export_as(core::option::Option)]
impl<T> Option<Option<T>> {
    #[rr::returns("self ≫= id")]
    pub fn flatten(self) -> Option<T> {
        match self {
            Some(inner) => inner,
            None => None,
        }
    }
}
