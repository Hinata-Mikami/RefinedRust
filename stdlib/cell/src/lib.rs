#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.cell")]
#![rr::include("sized")]

#[repr(transparent)]
#[rr::export_as(core::cell::UnsafeCell)]
#[rr::refined_by("x" : "{rt_of T}")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
pub struct UnsafeCell<T: ?Sized> {
    #[rr::field("#x")]
    value: T,
}
