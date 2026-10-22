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


#[rr::export_as(core::ops::Drop)]
pub trait Drop {
    // The base spec doesn't really matter that much.
    // We cannot call an arbitrary implementor `T : Drop` anyways.
    // We only ever call concrete impls of `Drop` from the corresponding drop glue,
    // where a more specific spec for a particular impl can be concretely resolved.
    //
    // Morally, this function should be marked as `unsafe` in Rust, but for some reason it isn't.
    // Most impls will break the safety contract of mutable references as the safety invariant will
    // be invalidated afterwards.
    #[rr::requires("False")]
    fn drop(&mut self);
}
