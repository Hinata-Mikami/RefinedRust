#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.spin")]

#![rr::include("closures")]
#![rr::include("option")]

mod relax;
mod once;
mod rwlock;
