#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![feature(allocator_api)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.boxed")]
#![rr::import("rrstd.boxed.theories", "shims")]
#![rr::include("alloc")]
#![rr::include("option")]
#![rr::include("rr_internal")]
#![rr::include("mem")]
#![rr::include("ptr")]

use std::alloc::{Allocator, Global};
use std::marker::PhantomData;
use std::ptr::dangling;


// TODO: maybe we should seal this definition at the module boundary so that there's no chance of
// the definition details leaking?

/*
#[rr::export_as(alloc::boxed::Box)]
#[rr::refined_by("x" : "{rt_of T}")]
#[rr::exists("a", "b")]
pub struct Box<T: ?Sized, A: Allocator = Global>{
    #[rr::field("a")]
    _x: PhantomData<T>,
    #[rr::field("b")]
    _y: A,
}
*/

#[rr::export_as(#method alloc::boxed::Box::new)]
#[rr::trust_me]
#[rr::code_shim("box_new")]
#[rr::returns("x")]
pub fn box_new<T>(x: T) -> Box<T> {
    core::mem::size_of::<T>();
    std::ptr::dangling::<T>();
    unimplemented!();
}
