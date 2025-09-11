#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.option")]

#![rr::include("closures")]
#![allow(unused)]

#[rr::refined_by("option (place_rfn {rt_of T})")]
#[rr::export_as(core::option::Option)]
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
}
