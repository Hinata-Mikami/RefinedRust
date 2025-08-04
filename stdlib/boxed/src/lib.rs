#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.boxed")]
#![rr::import("rrstd.boxed.theories", "shims")]
#![rr::include("option")]
#![rr::include("alloc")]
#![rr::include("rr_internal")]
#![allow(unused)]

use std::alloc::{Allocator, Global};
use std::marker::PhantomData;


// TODO: maybe we should seal this definition at the module boundary so that there's no chance of
// the definition details leaking?
#[rr::export_as(alloc::boxed::Box)]
#[rr::refined_by("x" : "{rt_of T}")]
#[rr::exists("a", "b")]
pub struct Box<T: ?Sized, A: Allocator = Global>{
    #[rr::field("a")]
    _x: PhantomData<T>,
    #[rr::field("b")]
    _y: A,
}

#[rr::export_as(alloc::boxed::Box)]
impl<T> Box<T> {
    // TODO: put shim here
    #[rr::trust_me]
    #[rr::returns("x")]
    pub fn new(x: T) -> Self {
        unimplemented!();
    }
}
