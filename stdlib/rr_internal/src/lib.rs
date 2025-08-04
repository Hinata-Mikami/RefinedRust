#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.rr_internal")]
#![rr::import("rrstd.rr_internal.theories", "shims")]

#![rr::include("ptr")]
#![rr::include("alloc")]
#![allow(unused)]

use std::alloc;
