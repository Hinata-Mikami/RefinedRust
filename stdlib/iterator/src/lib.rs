#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]

#![feature(try_trait_v2)]

#![rr::coq_prefix("rrstd.iterator")]
#![rr::package("refinedrust-stdlib")]
#![rr::include("closures")]
#![rr::include("option")]

mod step;
pub mod adapters;
pub mod traits;

