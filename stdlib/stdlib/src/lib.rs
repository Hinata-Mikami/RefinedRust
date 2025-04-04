//! Dummy crate that re-exports all other stdlib modules so we just have to import one module

#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.stdlib")]
#![allow(unused)]

#![rr::export_include("alloc")]
#![rr::export_include("boxed")]
#![rr::export_include("clone")]
#![rr::export_include("closures")]
#![rr::export_include("controlflow")]
#![rr::export_include("iterator")]
#![rr::export_include("option")]
#![rr::export_include("ptr")]
#![rr::export_include("result")]
#![rr::export_include("rr_internal")]
#![rr::export_include("vec")]

