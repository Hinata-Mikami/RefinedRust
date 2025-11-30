#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![feature(allocator_api)]

#![rr::package("stdlib-rr_internal")]
#![rr::coq_prefix("rrstd.rr_internal")]
#![rr::include("alloc")]
#![rr::include("ptr")]
#![rr::import("rrstd.rr_internal.theories", "shims")]

use std::alloc;
