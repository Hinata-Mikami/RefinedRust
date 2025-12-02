#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.sized")]
#![allow(unused)]

#[rr::export_as(core::marker::Sized)]
#[rr::semantic("TySized {Self}")]
pub trait Sized {

}
