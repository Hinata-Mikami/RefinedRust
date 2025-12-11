#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]

#![feature(try_trait_v2)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.iterator")]
#![rr::include("closures")]
#![rr::include("option")]

mod step;
pub mod adapters;
pub mod traits;

