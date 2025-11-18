#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("stdlib-spin")]
#![rr::coq_prefix("rrstd.spin")]

mod relax;
mod once;
mod rwlock;
