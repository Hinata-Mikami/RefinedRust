#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![feature(allocator_api)]
#![feature(pointer_is_aligned_to)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.ptr_advanced")]

#![rr::include("mem")]
#![rr::include("ptr")]
#![rr::include("option")]
#![rr::include("clone")]

//! Advanced pointer functionality so that we can depend on `option`.

mod nonnull;
mod unique;
