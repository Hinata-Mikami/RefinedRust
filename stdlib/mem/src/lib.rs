#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.mem")]
#![rr::import("rrstd.mem.theories", "shims")]
#![allow(unused)]

#[rr::export_as(core::mem::size_of)]
#[rr::code_shim("mem_size_of")]
#[rr::returns("ly_size {ly_of T}")]
pub const fn mem_size_of<T>() -> usize {
    unimplemented!();
}

#[rr::export_as(core::mem::align_of)]
#[rr::code_shim("mem_align_of")]
#[rr::returns("ly_align {ly_of T}")]
pub const fn mem_align_of<T>() -> usize {
    unimplemented!();
}

#[rr::code_shim("mem_align_log_of")]
#[rr::returns("ly_align_log {ly_of T}")]
pub const fn mem_align_log_of<T>() -> usize {
    unimplemented!();
}
